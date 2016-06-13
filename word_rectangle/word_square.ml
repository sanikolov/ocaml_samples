module Wset = Set.Make(struct type t = string let compare = Pervasives.compare end)
module IntSet = Set.Make(struct type t = int let compare = Pervasives.compare end)

type solution = (int * string) list

exception Found_one of (solution * solution) list
exception Nothing
exception Done

let print = Printf.printf

(* reads words from file and returns them in a sorted list *)
and read_words file sort_fn =
  let ch = open_in file in
  let rec loop acc =
    let eof, word =
    try
      false, input_line ch
    with End_of_file -> close_in ch; true, "" in
      if eof then List.sort sort_fn acc else loop (word :: acc)
  in
    loop []

(* returns a set of word sizes, e.g. {2,3,4,5....28} *)
let rec count_wordlens iset = function
  | [] -> iset
  | hd :: tl -> count_wordlens (IntSet.add (String.length hd) iset) tl

(* create and populate map N -> {set of words of sizes N} for each N 
 * in the set of word lengths
 *)
and create_mapping wsizes_set wlist =
  let populate_map map =
    List.iter (fun w -> let len = String.length w in
	       let value = Hashtbl.find map len in
	       let newval = Wset.add w value in
		 Hashtbl.replace map len newval) in
  let map = Hashtbl.create (IntSet.cardinal wsizes_set) in
    IntSet.iter (fun word_len -> Hashtbl.add map word_len Wset.empty) wsizes_set;
    populate_map map wlist;
    map

(* sort words first by length, then lexicographically *)
and wsort w1 w2 =
  let len = String.length w1 - String.length w2 in
    if len < 0 || len > 0 then len
    else
      if w1 < w2 then -1 else if w1 > w2 then 1 else 0

and gen_indexes n len =
  let rec init_set n acc =
    if n = 0 then acc else init_set (pred n) (IntSet.add (pred n) acc)
  and contained set_el lst = (* structured equality doesn't work for sets *)
    let rec loop = function
      | [] -> false
      | hd :: tl -> if IntSet.equal set_el hd then true else loop tl
    in
      loop lst
  and dec_one lst_sets =
    let lst = ref [] in
      List.iter (fun aset ->
		   IntSet.iter (fun el ->
				  let subset = IntSet.remove el aset in 
				    if not (contained subset !lst) then lst := subset :: !lst
			       ) aset
		) lst_sets;
      !lst in
  let rec repeat l n =
    if n = 0 then l else repeat (dec_one l) (pred n)
  in
    if n > len then (
      let nset, less = init_set n IntSet.empty, n - len < len in
      let func, arg = if less then (fun x -> x), n - len else List.map (IntSet.diff nset), len in
	func (repeat [nset] arg)
    ) else []

(* return 2 lists, one of size num, the other one is the remainder, caller does range checks *)
let rec split_list num lst =
  let rec loop n p1 p2 =
    if n = 0 then p1, p2 else loop (pred n) ((List.hd p2) :: p1) (List.tl p2)
  in
    loop num [] lst

and create_key prev pos ch = prev ^ "p" ^ (string_of_int pos) ^ "c" ^ (String.make 1 ch)

and hkey_list len index clist =
  let sorted = List.sort (fun (pos1,_) (pos2,_) -> pos1 - pos2) clist
  and key = ref (string_of_int len) in
    List.iter (fun (pos, word) -> key := create_key !key pos word.[index]) sorted;
    !key

and hkey_set word iset =
  let len = String.length word in
  let key = ref (string_of_int len) in
    IntSet.iter (fun index -> key := create_key !key index word.[index]) iset;
    !key

and lookup (pmap1, pmap2) key =
  try Hashtbl.find pmap1 key
  with Not_found -> if pmap1 == pmap2 then raise Not_found else
    Hashtbl.find pmap2 key

(* maps [wordlen, (position * letter) list ] to a set of wordlen long 
 * words that contain that letter in that position
 *)
let compute_posmap depth_map map dim =
  let filename = "hashtbl_" ^ (Printf.sprintf "%.3d" dim) ^ ".xdr" in
    try
      let ch =
	open_in_bin filename in
      let pos_map : (string,Wset.t) Hashtbl.t = Marshal.from_channel ch in
	close_in ch;
	print "pos_map: loaded %d bindings for size %d\n%!" (Hashtbl.length pos_map) dim;
	pos_map
    with Sys_error _ ->
      let pos_map, mdepth = Hashtbl.create 500000, Hashtbl.find depth_map dim in
      let subscript_arr =
	Array.init dim (fun i -> if i < mdepth then gen_indexes dim (succ i) else []) in
      let iter_fun w =
	Array.iter (List.iter (fun set -> let key = hkey_set w set in
			       let value = try
				 Hashtbl.find pos_map key
			       with Not_found -> Wset.empty in
				 Hashtbl.replace pos_map key (Wset.add w value)
			      )
		   ) subscript_arr
      in
	Wset.iter iter_fun (Hashtbl.find map dim);
	let ch = open_out_bin filename in
	  Marshal.to_channel ch pos_map [];
	  close_out ch;
	  print "pos_map: computed %d bindings for size %d\n%!" (Hashtbl.length pos_map) dim;
	  pos_map

type cache_res = C_hit | C_miss

let cache_create size init_key init_val =
  Array.make size (init_key, init_val)

let cache_lookup cache_id el =
  let size = Array.length cache_id in
  let hash = abs(Hashtbl.hash el) in
  let index = hash mod size in
  let k, v = cache_id.(index) in
    (if k = el then C_hit else C_miss), v

let cache_replace cache_id k v =
  let size = Array.length cache_id in
  let hash = abs(Hashtbl.hash k) in
  let index = hash mod size in
    cache_id.(index) <- (k, v)

let cardinal map dim = Wset.cardinal (Hashtbl.find map dim)
(*  wiszes_set is something like {2,3,4,5,6...,28}
 *  map has wsizes_set (e.g. N) as keys and the values hold all N-letter words as a set
 *  pos_map has (word_len, position, letter) as keys and all word_len letter words as values as a set
 *  tuple_set is the set of all possible (word_len, position, letter) tuples in the input file
 *)
let solve_rectangle wsizes_set map depth_map =
  let module Cset = Set.Make(struct type t = char let compare = Pervasives.compare end) in
  let memo_rep = Hashtbl.create 100 in
  let char_sets wset =
    let wlen = String.length (Wset.choose wset) in
      try Hashtbl.find memo_rep wlen
      with Not_found ->
	let carr = Array.make wlen Cset.empty in
	  Wset.iter (fun w -> 
		       for i = 0 to (pred wlen) do
			 carr.(i) <- Cset.add w.[i] carr.(i)
		       done
		    ) wset;
	  let sizes_arr, min_index, mn = Array.map Cset.cardinal carr, ref 0, ref max_int in
	    Array.iteri (fun i el -> if el < !mn then ( min_index := i; mn := el)) sizes_arr;
	    Hashtbl.replace memo_rep wlen !min_index;
	    !min_index
  in
  let solve_fixed dim1 dim2 pos_map = (* solve rectangle of size dim1 x dim2 *)
    let other dim = if dim = dim1 then dim2 else dim1
    and mdepth1, mdepth2 = Hashtbl.find depth_map dim1, Hashtbl.find depth_map dim2 in
    let rec compute_initial_indexes dim iset =
      if dim = 0 then iset else compute_initial_indexes (pred dim) (IntSet.add (pred dim) iset) in

    (* fill rectangle along dimension 'len' with a word subject to the constraints
     * in the constraint list, i.e. list of cross words and their indexes
     *)
    let s1, s2 = Hashtbl.find map dim1, Hashtbl.find map dim2 in
    let sz1, sz2 = Wset.cardinal s1, Wset.cardinal s2 in
    let smaller_set, larger_set = if sz1 < sz2 then s1, s2 else s2, s1 in
    let sized_set dim = if dim = dim1 then s1 else s2 in
    let mdepth dim = if dim = dim1 then mdepth1 else mdepth2 in
    let smaller_dim = if sz1 < sz2 then dim1 else dim2
    and compute_min_index pos_set clist =
      let clen = List.length clist in
	if clen = 0 then
	  let least = char_sets larger_set in least, smaller_set, IntSet.remove least pos_set
	else (
	  let _, aword = List.hd clist in
	  let wlen = String.length aword in 
	  let cross_len = other wlen in
	  let depth = mdepth cross_len in
	  let min_ind, min_set = ref max_int, ref (sized_set cross_len) in
	    try
	      IntSet.iter (fun index ->
			     let l1, l2 =
			       if List.length clist <= depth
			       then clist, [] else split_list depth clist in
			     let aset = ref (
			       let key1 = hkey_list cross_len index l1 in
				 try
				   lookup pos_map key1
				 with Not_found -> raise Nothing
			     ) in
			       List.iter (fun el -> aset := Wset.inter !aset (
					    try
					      lookup pos_map (hkey_list cross_len index [el])
					    with Not_found -> raise Nothing
					  )
					 ) l2;

			       if Wset.cardinal !aset < Wset.cardinal !min_set then (
				 min_ind := index;
				 min_set := !aset
			       )
			  ) pos_set;
	      !min_ind, !min_set, IntSet.remove !min_ind pos_set
	    with Nothing -> 0, Wset.empty, IntSet.empty
	)
    in
      (* pos_set holds available indexes for current direction
       * clist holds constraint list for current direction
       * other_set holds available indexes for next descent
       * other_clist holds constraint list for next descent
       *)
    let solve_all pos_set clist other_set other_clist just_one depth_limit =
      let all = ref [] in
      let cache = cache_create 8192 [|0,"",""|] false in
      let dep_array = Array.make ((IntSet.cardinal pos_set) + (IntSet.cardinal other_set)) (0, "", "") in
      let depth, idx = ref 0, ref 0 in
      let rec solve pos_set clist other_set other_clist =
	let solvable = ref false in
	let solved = IntSet.is_empty other_set && IntSet.is_empty pos_set in
	  if solved then (
	    if just_one then raise (Found_one [(clist, other_clist)]) else
	      all := (clist, other_clist) :: !all;

	    solvable := true
	  ) else (
	      let min_index, min_wset, new_pos_set = compute_min_index other_set clist in
		if Wset.cardinal min_wset > 0 then (
		  let sz, min_el, max_el = Wset.cardinal min_wset, Wset.min_elt min_wset, Wset.max_elt min_wset in
		    dep_array.(!depth) <- (sz, min_el, max_el);
		    let sub_arr = (Array.sub dep_array 0 !depth) in
		    let product = if depth_limit > 0 then Array.fold_left (fun sz1 (sz2,_,_) -> Int64.mul sz1 (Int64.of_int sz2)
						  ) Int64.one sub_arr else Int64.minus_one in
		    let unreachable =
		      if product < (Int64.of_int depth_limit) then false else
			let c_val, _ = cache_lookup cache dep_array in c_val = C_hit
		    in
		      if not unreachable then (
			Wset.iter (fun word ->
				     depth := succ !depth;
				     solvable := (solve new_pos_set ((min_index, word) :: other_clist) pos_set clist) || !solvable;
				     depth := pred !depth
				  ) min_wset;
			
			if depth_limit > 0 && product >= Int64.of_int depth_limit && not !solvable then
			  cache_replace cache dep_array true
		      )
		)
	  );
	  
	  !solvable
      in
	print "solve_all: max_depth %d%!\n" depth_limit;
	ignore (solve pos_set clist other_set other_clist);
	!all
    in
    let pos_set_min = compute_initial_indexes smaller_dim IntSet.empty
    and pos_set_max = compute_initial_indexes (other smaller_dim) IntSet.empty in
    let all_solutions =
	try
	  solve_all pos_set_min [] pos_set_max [] (Sys.argv.(2) <> "all") 
	    (if Sys.argv.(4) = "heuristic" then 80000 else 0)
	with Found_one(sol) -> sol in
	if List.length all_solutions > 0 then print "solution are:\n%!";
	let sort_fn (pos1, _) (pos2, _) = pos1 - pos2 in
	  List.iter (fun (sol_a, sol_b) ->
	    let lst_a, lst_b = List.sort sort_fn sol_a, List.sort sort_fn sol_b in
	      print_endline("***********");
	      List.iter (fun (pos, w) -> print "%d -> %s\n" pos w) lst_a;
	      print_newline ();
	      List.iter (fun (pos, w) -> print "%d -> %s\n" pos w) lst_b
	  ) all_solutions;
	  if List.length all_solutions > 0 then raise Done
  and generate_dims dim =
    let pairs = ref [] in
      for d = dim downto 1 do
	if IntSet.mem d wsizes_set then (
	  for k = d downto 1 do
	    if IntSet.mem k wsizes_set then
	      pairs := (d, k) :: !pairs
	  done
	)
      done;
      List.sort (fun (d1, d2) (dim1, dim2) ->
		   let delta = dim1 * dim2 - d1 * d2 
		   and sz1, sz2 = cardinal map dim1, cardinal map dim2 in
		     if delta = 0 then sz2 - sz1 else delta
		) !pairs
  and bound = abs(try int_of_string Sys.argv.(3) with Failure _ -> 0)
  and set_size = IntSet.max_elt wsizes_set in
  let upper_bound = if bound = 0 then set_size else min bound set_size in
    List.iter (fun (dim1, dim2) ->
		 let start = Unix.gettimeofday () in
		   print "trying to solve for rectangle %d x %d\n" dim1 dim2;
		   let sz1, sz2 = cardinal map dim1, cardinal map dim2 in
		     print "which contains %d x %d = %d elements ->\n%!" sz1 sz2 (sz1*sz2);
		     let pmap1 = compute_posmap depth_map map dim1 in
		     let pmap2 = if dim1 = dim2 then pmap1 else compute_posmap depth_map map dim2 in
		       Gc.full_major ();
		       solve_fixed dim1 dim2 (pmap1, pmap2);
		       print "%.1f seconds elapsed, no solution found\n\n%!" (Unix.gettimeofday () -. start)
	      ) (generate_dims upper_bound)

let compute_partitions n len =
  let rec loop n len acc_up acc_down =
    if len = 0 then acc_up / acc_down else
      loop (pred n) (pred len) (acc_up * n) (acc_down * len)
  in
    loop n (min len (n-len)) 1 1

let compute_max_depth map wsizes_set max_keys_set_size =
  let max_depth n =
    let rec loop k =
      if (compute_partitions n k) > max_keys_set_size then pred k
      else if k >= n/2 then k
      else loop (succ k)
    in
      loop 1 in
  let depth_map = Hashtbl.create (IntSet.cardinal wsizes_set) in
    IntSet.iter (fun n -> Hashtbl.replace depth_map n (max_depth n)) wsizes_set;
    depth_map

let _ =
  (
    match Sys.argv with
      | [|_;_;_;_;_|] -> ()
      | _ -> print_endline ("Usage: " ^ Sys.argv.(0) ^ " wordfile <all|one> max_num heuristic\n");  (* one is recommended for speed *)
	  print_endline "where wordfile holds all words, all or one solutions are printed\nand max_num may be 0 if no upper bound on word length desired\nif heuristic given then solutions are found quicker"; 
	  exit 1
  );
  let wlist = read_words Sys.argv.(1) wsort in
  let wsizes_set = count_wordlens IntSet.empty wlist in
  let map = create_mapping wsizes_set wlist in
  let depth_map = compute_max_depth map wsizes_set 125 in
    try
      solve_rectangle wsizes_set map depth_map
    with Done -> exit 0
