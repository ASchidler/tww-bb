This is the code for the twin-width Branch & Bound solver.
Details can be found in our paper "Computing Twin-width with SAT and Branch & Bound", IJCAI 2023 (https://www.ijcai.org/proceedings/2023/224).
The SAT encodings can be found at https://github.com/ASchidler/twin_width

The code uses CMake and can be compiled using "cmake ." and then "make". This creates the binary "tww-bb"
Boost is required for this solver. The code has been tested on Ubuntu and MacOS.
The source code contains nauty 2.8.6 (https://pallini.di.uniroma1.it/)

The solver is used by calling
./tww-bb <instance>
The instance has to be in DIMACS format and bz2 compressed.

The following options are supported:
-v verbose mode

-w print the twin-width.

-g whenever a branch is closed, create a witness trigraph that is used as a subgraph lower bound.

-c use caching to speed up search.

-e <int> approximate size for cache in GB.

-o detect isomorphic orderings to speed up search (requires -c).

-f do full instead of fast isomorphic order check (requires -c and -o). This is slower than the fast check but can detect more isomorphisms.

-d compute lower bounds.

-t <int> timeout for lower bound computation in seconds.

-u <int> upper bound used for computation.

-b uses the two neighborhood for contractions. Speeds up search, but can lead to non-optimal results.

-r <file path> logs a proof that can be verified with the SAT encodings, see reference above.


