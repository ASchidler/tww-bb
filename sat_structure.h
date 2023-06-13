//
// Created by asc on 18.12.22.
//

#ifndef TWW_BB_SAT_STRUCTURE_H
#define TWW_BB_SAT_STRUCTURE_H

#include "cadical/cadical.hpp"
#include "cadical/signal.hpp"
#include "graph.h"
#include "tww.h"

using namespace std;

namespace tww {
    class SatStructure {
    private:
        CaDiCaL::Solver solver;
        int cvar = 0;
        vector<vector<int>> red;
        vector<vector<int>> black;
        vector<vector<vector<int>>> c1;
        vector<vector<vector<int>>> c2;
        vector<vector<vector<vector<int>>>> nred;
        vector<node_t> mapping;

        int atmost(vector<int> &literals, node_t bound) {
            int exceeded = ++cvar;
            if (bound == 0) {
                for(auto& cv : literals) {
                    solver.add(-cv);
                    solver.add(0);
                }
                solver.reserve(cvar);
                return exceeded;
            }

            vector<vector<int>> aux(literals.size(), vector<int>(bound + 1));

            for (auto n = 0; n < aux.size(); n++) {
                for (auto d = 1; d <= bound; d++) {
                    aux[n][d] = ++cvar;
                }
            }
            solver.reserve(cvar);

            for (auto n = 0; n < aux.size(); n++) {
                solver.add(-literals[n]);
                solver.add(aux[n][1]);
                solver.add(0);

                if (n > 0) {
                    solver.add(-aux[n - 1][bound]);
                    solver.add(-literals[n]);
                    solver.add(exceeded);
                    solver.add(0);

                    for (auto d = 1; d <= bound; d++) {
                        solver.add(-aux[n - 1][d]);
                        solver.add(aux[n][d]);
                        solver.add(0);

                        if (d > 1) {
                            solver.add(-aux[n - 1][d - 1]);
                            solver.add(-literals[n]);
                            solver.add(aux[n][d]);
                            solver.add(0);
                        }
                    }
                }
            }

            return exceeded;
        }

    public:
        SatStructure(node_t size, node_t bound) : red(size, vector<int>(size)), black(size, vector<int>(size)),
                                                  c1(size, vector<vector<int>>(size, vector<int>(size))),
                                                  c2(size, vector<vector<int>>(size, vector<int>(size))),
                                                  nred(size, vector<vector<vector<int>>>(size, vector<vector<int>>(size, vector<int>(size)))),
                                                  mapping(size){
            for (node_t n = 0; n < size; n++) {
                for (node_t n2 = n+1; n2 < size; n2++) {
                    red[n][n2] = ++cvar;
                    black[n][n2] = ++cvar;
                    black[n2][n] = black[n][n2];
                    red[n2][n] = red[n][n2];

                    for (node_t n3 = 0; n3 < size; n3++) {
                        if (n != n3) {
                            c1[n][n2][n3] = ++cvar;
                            c2[n][n2][n3] = ++cvar;

                            c1[n2][n][n3] = c1[n][n2][n3];
                            c2[n2][n][n3] = c2[n][n2][n3];

                            for (node_t n4 = n3+1; n4 < size; n4++) {
                                nred[n][n2][n3][n4] = ++cvar;
                                nred[n][n2][n4][n3] = nred[n][n2][n3][n4];
                                nred[n2][n][n3][n4] = nred[n][n2][n3][n4];
                                nred[n2][n][n4][n3] = nred[n][n2][n3][n4];
                            }
                        }
                    }
                }
            }
            solver.reserve(cvar);

            vector<int> tmp(size-2);
            vector<int> tmp2(size-2);
            vector<int> exceeded(size-1);

            for (node_t n = 0; n < size; n++) {
                for (node_t n2 = n+1; n2 < size; n2++) {
                    size_t cnt = 0;
                    size_t exceeded_cnt = 0;
                    for (node_t n3 = 0; n3 < size; n3++) {
                        if (n != n3 && n2 != n3) {
                            tmp[cnt] = -nred[n][n2][n2][n3];
                            ++cnt;

                            solver.add(-black[n][n3]);
                            solver.add(black[n2][n3]);
                            solver.add(c1[n][n2][n3]);
                            solver.add(0);

                            solver.add(black[n][n3]);
                            solver.add(-c1[n][n2][n3]);
                            solver.add(0);

                            solver.add(-black[n2][n3]);
                            solver.add(-c1[n][n2][n3]);
                            solver.add(0);

                            solver.add(black[n][n3]);
                            solver.add(-black[n2][n3]);
                            solver.add(c2[n][n2][n3]);
                            solver.add(0);

                            solver.add(-black[n][n3]);
                            solver.add(-c2[n][n2][n3]);
                            solver.add(0);

                            solver.add(black[n2][n3]);
                            solver.add(-c2[n][n2][n3]);
                            solver.add(0);

                            solver.add(-nred[n][n2][n2][n3]);
                            solver.add(red[n][n3]);
                            solver.add(red[n2][n3]);
                            solver.add(c1[n][n2][n3]);
                            solver.add(c2[n][n2][n3]);
                            solver.add(0);

                            solver.add(-red[n][n3]);
                            solver.add(nred[n][n2][n2][n3]);
                            solver.add(0);

                            solver.add(-red[n2][n3]);
                            solver.add(nred[n][n2][n2][n3]);
                            solver.add(0);

                            solver.add(-c1[n][n2][n3]);
                            solver.add(nred[n][n2][n2][n3]);
                            solver.add(0);

                            solver.add(-c2[n][n2][n3]);
                            solver.add(nred[n][n2][n2][n3]);
                            solver.add(0);

                            node_t tmp2_cnt = 0;
                            for(node_t n4=0; n4 < size; n4++) {
                                if (n4 > n3 && n4 !=n && n4 != n2) {
                                    solver.add(-nred[n][n2][n3][n4]);
                                    solver.add(red[n3][n4]);
                                    solver.add(0);

                                    solver.add(nred[n][n2][n3][n4]);
                                    solver.add(-red[n3][n4]);
                                    solver.add(0);
                                }
                                if (n4 != n3 && n4 != n) {
                                    tmp2[tmp2_cnt] = -nred[n][n2][n3][n4];
                                    ++tmp2_cnt;
                                }
                            }
                            assert(tmp2_cnt == tmp2.size());
                            exceeded[exceeded_cnt] = atmost(tmp2, size - bound - 3);
                            ++exceeded_cnt;
                        }
                    }
                    assert(cnt == tmp.size());
                    exceeded[exceeded_cnt] = atmost(tmp, size - bound - 3);
                    ++exceeded_cnt;
                    assert(exceeded_cnt == exceeded.size());
                    for(auto cv : exceeded) {
                        //solver.add(-cv);
                        solver.add(-exceeded[exceeded.size()-1]);
                    }
                    solver.add(0);
                }
            }
        }

        bool check(Graph &g, dynamic_bitset<>& component) {
            assert(component.count() == red.size());
            node_t cnode = 0;
            solver.reset_assumptions();

            for(auto n=component.find_first(); n != component.npos; n = component.find_next(n)) {
                mapping[cnode] = n;

                for(auto n2m=0; n2m < cnode; ++n2m) {
                    auto n2 = mapping[n2m];
                    if (g.adjacency[n].test(n2))
                        solver.assume(black[n2m][cnode]);
                    else
                        solver.assume(-black[n2m][cnode]);

                    if (g.red_adjacency[n].test(n2))
                        solver.assume(red[n2m][cnode]);
                    else
                        solver.assume(-red[n2m][cnode]);
                }

                cnode++;
            }

            return solver.solve() == 10;
        }
    };
}
#endif //TWW_BB_SAT_STRUCTURE_H
