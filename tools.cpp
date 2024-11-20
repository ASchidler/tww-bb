#include "tools.h"

namespace tww {
    Graph create_grid(node_t x, node_t y) {
        Graph g(x * y);

        for(node_t n1=0; n1 < x; ++n1) {
            for (node_t n2=0; n2 < y; ++n2) {
                auto cn = n2 * x + n1;

                if (n1 > 0)
                    g.add_edge(cn, n2 * x + n1 - 1);

                if (n1 < x - 1)
                    g.add_edge(cn, n2 * x + n1 + 1);

                if (n2 > 0)
                    g.add_edge(cn, (n2 - 1) * x + n1);

                if (n2 < y - 1)
                    g.add_edge(cn, (n2 + 1) * x + n1);
            }
        }

        return g;
    }

    Graph create_reduced_grid(node_t extra) {
        node_t x = 6;
        node_t y = 8;
        Graph g((9*6));

        for(node_t n1=0; n1 < x; ++n1) {
            for (node_t n2=0; n2 < y; ++n2) {
                auto cn = n2 * x + n1;

                if (n1 > 0)
                    g.add_edge(cn, n2 * x + n1 - 1);

                if (n1 < x - 1)
                    g.add_edge(cn, n2 * x + n1 + 1);

                if (n2 > 0)
                    g.add_edge(cn, (n2 - 1) * x + n1);

                if (n2 < y - 1)
                    g.add_edge(cn, (n2 + 1) * x + n1);
            }
        }

        for (node_t ex=0; ex < extra; ++ex) {
            auto cn = (x*y) + ex;

            if (ex > 0)
                g.add_edge(cn, (y-1) * x + ex - 1);

            if (ex < x - 1)
                g.add_edge(cn, (y-1) * x + ex + 1);

            g.add_edge(cn, (y-2) * x + ex);
        }

        return g;
    }

    Graph create_rook(node_t n) {
        Graph g(n * n);

        for(node_t x1=0; x1 < n; ++x1) {
            for (node_t y1 = 0; y1 < n; ++y1) {
                auto cn = y1 * n + x1;
                for (node_t x2 = x1 + 1; x2 < n; ++x2) {
                    g.add_edge(cn, y1 * n + x2);
                }
                for(node_t y2 = y1+1; y2 < n; ++ y2) {
                    g.add_edge(cn, y2 * n + x1);
                }
            }
        }

        return g;
    }

    Graph create_knight(node_t n) {
        Graph g(n * n);

        for(int x1=0; x1 < n; ++x1) {
            for (int y1 = 0; y1 < n; ++y1) {
                for(int mod1=-2; mod1 < 3; mod1 += 4) {
                    for (int mod2=-1; mod2 < 2; mod2 += 2) {
                        int u1 = x1 + mod1;
                        int v1 = y1 + mod2;
                        if (u1 > 0 && u1 < n && v1 > 0 && v1 < n)
                            g.add_edge(u1 * n + v1, x1 * n + y1);
                        int u2 = x1 + mod2;
                        int v2 = y1 + mod1;
                        if (u2 > 0 && u2 < n && v2 >0 && v2 < n) {
                            g.add_edge(u2 * n + v2, x1 * n + y1);
                        }
                    }
                }
            }
        }

        return g;
    }

    Graph create_line(node_t n) {
        Graph g(n * (n-1) / 2);
        vector<vector<node_t>> vertices(n, vector<node_t>(n));

        node_t cvertex = 0;
        for(node_t x=0; x < n; ++x) {
            for (node_t y = x+1; y < n; ++y) {
                vertices[x][y] = cvertex;
                vertices[y][x] = cvertex;
                cvertex++;
            }
        }

        for(node_t x=0; x < n; ++x) {
            for (node_t y = x+1; y < n; ++y) {
                for (node_t z = 0; z < n; ++z) {
                    if (y != z) {
                        g.add_edge(vertices[x][y], vertices[x][z]);
                    }

                    if (x != z) {
                        g.add_edge(vertices[x][y], vertices[y][z]);
                    }
                }
            }
        }

        return g;
    }

    Graph prime_paley(node_t p) {
        Graph g(p);
        dynamic_bitset<> square_set(p);
        for (node_t i=1; i < p; i++) {
            square_set.set(i * i % p);
        }

        for (node_t x=0; x < p; x++) {
            for(node_t y=x+1; y < p; y++) {
                if (square_set.test(y - x))
                    g.add_edge(x, y);
            }
        }

        return g;
    }

    /** Generates the paley graph for p^2 */
    Graph prime_square_paley(node_t p) {
        auto ps = p * p;
        // See: https://en.wikipedia.org/wiki/Finite_field
        auto g = Graph(ps);

        // Find non-square, i.e. quadratic non-residue
        dynamic_bitset<> p_squares(p);
        dynamic_bitset<> n_squares(p);

        for (node_t i=1; i < p; i++) {
            p_squares.set(i * i % p);
        }

        for(node_t i=1; i < p; i++) {
            if(! p_squares.test(i))
                n_squares.set(i);
        }
        auto m = n_squares.find_first();
        vector<dynamic_bitset<>> squares(p, dynamic_bitset<>(p));
        for (node_t x=0; x < p; x++) {
            for (node_t y=0; y < p; y++) {
                squares[(x * x + m * y * y) % p].set((2 * x * y) % p);
            }
        }

        for(int x1=0; x1 < p; x1++) {
            for(int y1=0; y1 < p; y1++) {
                for(int x2=0; x2 < p; x2++) {
                    for(int y2=0; y2 < p; y2++) {
                        if (x1 != x2 || y1 != y2) {
                            auto result = (x2 - x1) % p;
                            if (result < 0)
                                result += p;
                            auto result2 = (y2 - y1) % p;
                            if (result2 < 0)
                                result2 += p;

                            if (squares[result].test(result2))
                                g.add_edge(x1 * p + y1, x2 * p + y2);
                        }
                    }
                }
            }
        }

        return g;
    }

    node_t test_sequence(Graph& og, vector<pair<node_t, node_t>>& contr) {
        Graph g = og.copy(true);
        size_t result = 0;

        dynamic_bitset<> done(g.num_nodes());

        for(node_t cn=0; cn < g.num_nodes(); ++cn)
            result = max(result, g.red_adjacency[cn].count());

        for(auto& cc: contr) {
            assert(! done.test(cc.first));
            if (done.test(cc.first)) {
                cerr << "ERROR: Double Merge " << cc.first << endl;
            }
            done.set(cc.first);

            auto reds = ((g.adjacency[cc.first] ^ g.adjacency[cc.second]) | g.red_adjacency[cc.first]) - done;
            reds.reset(cc.second);
            assert(! reds.test(cc.first));
            assert(! reds.test(cc.second));

            g.remove(cc.first);

            g.red_adjacency[cc.second] |= reds;

//            if (VALIDATION_MODE) {
//                if (g.red_adjacency[cc.second].count() > result) {
//                    cout << cc.second << " (" << cc.first << "/" << cc.second << ") " << g.red_adjacency[cc.second].count() << ":";
//                    for(auto cx=new_reds.find_first(); cx != new_reds.npos; cx = new_reds.find_next(cx)) {
//                        cout << " " << cx;
//                    }
//                    cout << endl;
//                }
//            }
            result = max(result, g.red_adjacency[cc.second].count());

            for(auto cn=reds.find_first(); cn != reds.npos; cn = reds.find_next(cn)) {
                if (! g.red_adjacency[cn].test(cc.second)) {
                    g.red_adjacency[cn].set(cc.second);
//                    if (VALIDATION_MODE) {
//                        if (g.red_adjacency[cn].count() > result)
//                            cout << cn << " (" << cc.first <<"/" << cc.second << ") " << g.red_adjacency[cn].count() << endl;
//                    }
                    result = max(result, g.red_adjacency[cn].count());
                }
            }
        }

        return static_cast<node_t>(result);
    }
}