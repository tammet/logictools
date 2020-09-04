# logictools

The goal is to help studying logic and solvers by providing 
easy-to-use, pure browser-based javascript tools for both full classical predicate logic and propositional formulas at the [logictools.org](http://logictools.org) site.

The high-performance predicate logic prover [gkc](https://github.com/tammet/gkc) is written in 
C and available available under the
[AGPL v3](https://www.gnu.org/licenses/agpl-3.0.en.html) licence
as a command line tool on Linux, Windows and macOS and Wasm for running in the
browser. The browser version on this site is inevitably crippled when compared to the 
command-line version: the latter can utilize multiple cores, all the available memory, shared
memory databases and has several additional options not available in the browser. 
The browser version runs on a single core and has severe memory restrictions.

The educational propositional provers are self-contained, no-dependencies, easy-to-hack 
javascript code under the
[MIT licence](https://en.wikipedia.org/wiki/MIT_License).
The focus is on simplicity, ease of use, hacking and experimenting, 
not state of the art efficiency-wise.

Contact the author Tanel Tammet as (tanel.tammet at gmail.com). 

