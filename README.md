# Supplementary Material to the paper "An Abstract Interpretation for Divergence Analysis on Control Flow Graphs"

To make use of the links in the submitted PDF, move it to this paper submission into the root directory of the unpacked supplementary material.
The directory ```html``` contains the compiled Coqdoc, all links from the paper target this directory.
You can also navigate through the Coqdoc manually by opening the file ```html/toc.html``.

Relational links in PDFs are not implemented consistently among different operating systems.
On Mac, you need to use Skim for the relational links to work at all, and it is simply not possible to jump to the right position of the HTML-file.
On Linux, please use the file ```uniana-linux.pdf```. It is identical to the official submission except for the fact that the relational links also point to the correct location.
Unfortunately, the way the links are stated there is not interpretable on Mac.

The directory ```theories``` contains the Coq formalization.
To compile the Coq proofs you need [Coq 8.10.1](https://github.com/coq/coq/releases/tag/V8.10.1).
There are no further dependencies.

Executing
```
$ make
```
compiles the whole development.

(The directory ```coqdocjs`` is a library used to display the Coqdoc, it is not part of the submission.)
