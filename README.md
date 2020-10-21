# UniAna
This is the Coq formalization of the divergence analysis of the paper "An Abstract Interpretation for SIMD Divergence on
Reducible Control Flow Graphs"

The documentation of the Coq code is available [here](http://compilers.cs.uni-saarland.de/projects/uniana/toc.html).

To compile the Coq proofs you need [Coq 8.12.0](https://github.com/coq/coq/releases/tag/V8.12.0).
There are no further dependencies.

Executing
```
$ make
```
compiles the whole development.

The directory ```uniana``` contains the Coq formalization.

DISCLAIMER:

The content of the directory ```uniana/external/lvc``` is taken from Sigurd Schneider's [Phd thesis](https://github.com/sigurdschneider/lvc).

The content of the folder ```uniana/external/finiteTypes``` is taken from Jan Menz' [bachelor's thesis](https://www.ps.uni-saarland.de/~menz/bachelor.php).



