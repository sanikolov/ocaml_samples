This is an implementation of a great ITA puzzle which was popular some time before
they got acquired by Google.

Word Rectangle:
Write a program to find the largest possible rectangle of letters such that 
every row forms a word (reading left to right) and every column forms a word 
(reading top to bottom). Words should appear in this dictionary: WORD.LST (1.66MB).
Heuristic solutions that may not always produce a provably optimal rectangle
will be accepted: seek a reasonable tradeoff of efficiency and optimality. 


Compile code with:

$ ocamlopt word_square.ml

To find a heuristic solution run it thus

$ ./a.out WORD.LST one 0 heuristic

or to find all optimal (non heuristic) solutions

$ ./a.out WORD.LST all 0 0
