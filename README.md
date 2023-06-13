This twin-width solver can be compiled using CMake and uses Boost.
It has been tested on Linux/Ubuntu 18.04 and 20.04.

To run the branch & bound part use:
./tww-bb <instance>

For the new SAT encoding use:
./tww-bb -s <instance>

For the new SAT encoding with symmetry breaking (used for the experiments) use:
./tww-bb -s -d <instance>

The instance has to be in DIMACS format and bz2 compressed.

The source code contains nauty 2.8.6 (https://pallini.di.uniroma1.it/) and Cadical (https://github.com/arminbiere/cadical)
