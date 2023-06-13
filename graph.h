//
// Created by asc on 09.11.22.
//

#ifndef TWW_BB_GRAPH_H
#define TWW_BB_GRAPH_H
#include <boost/dynamic_bitset.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include "tww.h"
#include <fstream>
#include <cstring>
#include <sstream>
#include <iostream>
#include <utility>
#include <vector>
#include <bzlib.h>
#include <unordered_map>

extern "C" {
#include "nauty2_8_6/nauty.h"
#include "nauty2_8_6/gtools.h"
};

using namespace boost;

namespace tww {
    class Graph {
    public:
        std::vector<dynamic_bitset<>> adjacency;
        std::vector<dynamic_bitset<>> red_adjacency;

        explicit Graph(node_t nodes) : _deleted(nodes) {
            adjacency = std::vector<dynamic_bitset<>>(nodes, dynamic_bitset<>(nodes));
            red_adjacency = std::vector<dynamic_bitset<>>(nodes, dynamic_bitset<>(nodes));
        }
        bool is_deleted(node_t n) const {
            return _deleted[n];
        }

        node_t num_nodes() const {
            return adjacency.size();
        }

        size_t num_edges() const {
            size_t cnum = 0;
            for(auto& cn: adjacency) {
                cnum += cn.count();
            }
            cnum /= 2;
            return cnum;
        }

        void remove(node_t n) {
            _deleted[n] = true;
            for (auto cn=adjacency[n].find_first(); cn != adjacency[n].npos; cn = adjacency[n].find_next(cn)) {
                adjacency[cn].reset(n);
            }
            for (auto cn=red_adjacency[n].find_first(); cn != red_adjacency[n].npos; cn = red_adjacency[n].find_next(cn)) {
                red_adjacency[cn].reset(n);
            }
        }

        void restore(node_t n) {
            _deleted[n] = false;
            for (auto cn=adjacency[n].find_first(); cn != adjacency[n].npos; cn = adjacency[n].find_next(cn)) {
                adjacency[cn].set(n);
            }
            for (auto cn=red_adjacency[n].find_first(); cn != red_adjacency[n].npos; cn = red_adjacency[n].find_next(cn)) {
                red_adjacency[cn].set(n);
            }
        }

        void add_edge(node_t n1, node_t n2) {
            adjacency[n1].set(n2);
            adjacency[n2].set(n1);
        }

        Graph copy(bool copy_red) const {
            Graph newG = Graph(adjacency.size());
            for(auto n=0; n < adjacency.size(); n++) {
                newG.adjacency[n] |= adjacency[n];
                if (copy_red)
                    newG.red_adjacency[n] |= red_adjacency[n];
            }

            return newG;
        }

        static inline std::string &ltrim(std::string &s) {
           s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](int c) {return std::isprint(c);}));
           return s;
        }

        static Graph parse(const std::string& filename) {
            std::fstream fl;
            std::unique_ptr<Graph> g = nullptr;

            if (algorithm::ends_with(filename, ".bz2")) {
                FILE *bz2File = fopen(filename.c_str(), "rb");
                int bzError;
                BZFILE *myBZ = BZ2_bzReadOpen(&bzError, bz2File, 0, 0, NULL, 0);
                char buffer[4096];

                std::string tok = "";
                node_t nodes[2];
                bool header_read = false;
                bool is_header = false;
                bool is_edge = false;
                bool is_empty = false;

                while (bzError == BZ_OK) {
                    memset(buffer, '\0', strlen(buffer));
                    if (!tok.empty())
                        strcpy(buffer, tok.c_str());
                    int charsRead = BZ2_bzRead(&bzError, myBZ, buffer + tok.size(), sizeof(buffer) - tok.size() - 1);

                    if (charsRead > 0) {
                        std::istringstream iss(buffer);
                        for (long i = 0; getline(iss, tok); i++) {
                            if (!iss.eof() || bzError == BZ_STREAM_END) {
                                is_edge = false;
                                is_header = false;
                                is_empty = false;
                                tok = ltrim(tok);
                                std::istringstream iss2(tok);
                                std::string tok2;
                                long j = 0;

                                for (; getline(iss2, tok2, ' '); j++) {
                                    if (j==0 && tok2.empty()) {
                                        is_empty = true;
                                        break;
                                    }
                                    if (j == 0 && tok2 == "p") {
                                        if (header_read) {
                                            std::cout << "Double header" << std::endl;
                                            exit(1);
                                        }
                                        is_header = true;
                                        header_read = true;
                                        is_edge = false;
                                    }
                                    if (j == 0 && tok2 == "c") {
                                        break;
                                    }

                                    if (j == 0 && tok2 == "e") {
                                        is_edge = true;
                                    }

                                    if (is_edge && j > 2) {
                                        std::cout << "ERROR: encountered an edge with more than 2 edges" << std::endl;
                                        exit(1);
                                    }

                                    if ((is_edge && j > 0) || (is_header && j > 1) || (! is_edge && ! is_header)) {
                                        nodes[j - (is_header ? 2 : (is_edge ? 1 : 0))] = stoull(tok2);
                                    }
                                }
                                if (is_empty || tok.empty())
                                    continue;

                                if (is_edge && j != 3) {
                                    std::cout << "ERROR: found incomplete edge" << std::endl;
                                    exit(1);
                                }
                                if (is_header && j != 4) {
                                    std::cout << "ERROR: invalid header" << std::endl;
                                    exit(1);
                                }
                                if (!(is_header || is_edge) && j != 2) {
                                    std::cout << "ERROR: found invalid edge" << std::endl;
                                    exit(1);
                                }
                                if (g == nullptr && is_header) {
                                    g = std::make_unique<Graph>(nodes[0]);
                                }
                                if (!is_header) {
                                    auto n1 = nodes[0] - 1;
                                    auto n2 = nodes[1] - 1;
                                    g->add_edge(n1, n2);
                                }
                            } else {
                                ltrim(tok);
                            }
                        }
                    }
                }


                // Close the file
                BZ2_bzReadClose(&bzError, myBZ);
                fclose(bz2File);
            } else { // Assume textfile
                std::unique_ptr<std::ifstream> infile = nullptr;
                if (! filename.empty())
                    infile = std::make_unique<std::ifstream>(filename);

                std::string line;
                node_t nodes[2];
                bool header_read = false;
                bool is_header = false;

                while (std::getline(infile == nullptr ? std::cin : *infile, line))
                {
                    std::istringstream iss(line);
                    std::string tok2;
                    long j = 0;

                    for (; getline(iss, tok2, ' '); j++) {
                        if (j == 0 && tok2 == "p") {
                            if (header_read) {
                                std::cout << "Double header" << std::endl;
                                exit(1);
                            }
                            is_header = true;
                            header_read = true;
                        }
                        if (j == 0 && tok2 == "c") {
                            break;
                        }

                        if (!is_header && j > 2) {
                            std::cout << "ERROR: encountered an edge with more than 2 nodes" << std::endl;
                            exit(1);
                        }

                        if (!is_header|| j > 1)
                            nodes[j - (is_header ? 2 : 0)] = stoull(tok2);
                    }
                    if (!is_header && j != 2 && j > 0) {
                        std::cout << "ERROR: found incomplete edge " << j << std::endl;
                        exit(1);
                    }
                    if (is_header && j != 4) {
                        std::cout << "ERROR: invalid header" << std::endl;
                        exit(1);
                    }
                    if (g == nullptr && is_header) {
                        g = std::make_unique<Graph>(nodes[0]);
                        is_header = false;
                    }
                    else if (!is_header && j > 0) {
                        auto n1 = nodes[0] - 1;
                        auto n2 = nodes[1] - 1;

                        g->adjacency[n1].set(n2);
                        g->adjacency[n2].set(n1);
                    }

                    // process pair (a,b)
                }
            }

            return *g;
        }

        std::string get_canonical(std::vector<node_t>& mapping, std::vector<node_t>& orbitso) {
            int n = adjacency.size();
            int m = SETWORDSNEEDED(2*n);

            DYNALLSTAT(graph, g, g_sz);
            DYNALLSTAT(graph, g2, g2_sz);
            DYNALLSTAT(int, lab, lab_sz);
            DYNALLSTAT(int, ptn, ptn_sz);
            DYNALLSTAT(int, orbits, orbits_sz);

            statsblk stats;

            static DEFAULTOPTIONS_DENSEGRAPH(options);

            DYNALLOC2(graph, g, g_sz, m, 2*n, "malloc");
            DYNALLOC1(int, lab, lab_sz, 2*n, "malloc");
            DYNALLOC1(int, ptn, ptn_sz, 2*n, "malloc");
            DYNALLOC1(int, orbits, orbits_sz, 2*n, "malloc");
            DYNALLOC2(graph, g2, g2_sz, m, 2*n, "malloc");

            EMPTYGRAPH(g, m, 2*n);


            for(auto cn=0; cn < adjacency.size(); cn++) {
                ADDONEEDGE(g, cn, n + cn, m);
                if (! is_deleted(cn)) {
                    for (auto n2=adjacency[cn].find_first(); n2 != adjacency[cn].npos; n2 = adjacency[cn].find_next(n2)) {
                        ADDONEEDGE(g, cn, (int) n2, m);
                    }

                    for (auto n2=red_adjacency[cn].find_first(); n2 != red_adjacency[cn].npos; n2 = red_adjacency[cn].find_next(n2)) {
                        ADDONEEDGE(g, n + cn, n + (int) n2, m);
                    }
                }
            }

            options.getcanon = true;
            options.defaultptn = true;

            densenauty(g, lab, ptn, orbits, &options, &stats, m, 2*n, g2);

            std::string s = ntog6(g2, m, 2*n);

            node_t cidx=0;
            for (auto i = 0; i < 2 * adjacency.size(); ++i) {
                if (lab[i] < adjacency.size())
                    mapping[lab[i]] = cidx++;

                if (i < adjacency.size())
                    orbitso[i] = orbits[i];
            }
//
//            for(int i=0; i < orbits_sz; i++) {
//                std::cout << i << ":" << orbits[i] << std::endl;
//            }

            DYNFREE(lab, lab_sz);
            DYNFREE(orbits, orbits_sz);
            DYNFREE(ptn, ptn_sz);
            DYNFREE(g, g_sz);
            DYNFREE(g2, g2_sz);

            return s;
        }

        void get_orbits(std::vector<node_t>& orbitso) {
            int n = adjacency.size();
            int m = SETWORDSNEEDED(2*n);

            DYNALLSTAT(graph, g, g_sz);
            DYNALLSTAT(int, lab, lab_sz);
            DYNALLSTAT(int, ptn, ptn_sz);
            DYNALLSTAT(int, orbits, orbits_sz);

            statsblk stats;

            static DEFAULTOPTIONS_DENSEGRAPH(options);

            DYNALLOC2(graph, g, g_sz, m, 2*n, "malloc");
            DYNALLOC1(int, lab, lab_sz, 2*n, "malloc");
            DYNALLOC1(int, ptn, ptn_sz, 2*n, "malloc");
            DYNALLOC1(int, orbits, orbits_sz, 2*n, "malloc");

            EMPTYGRAPH(g, m, 2*n);


            for(auto cn=0; cn < adjacency.size(); cn++) {
                if (! is_deleted(cn)) {
                    ADDONEEDGE(g, cn, n + cn, m);
                    for (auto n2=adjacency[cn].find_first(); n2 != adjacency[cn].npos; n2 = adjacency[cn].find_next(n2)) {
                        ADDONEEDGE(g, cn, (int) n2, m);
                    }

                    for (auto n2=red_adjacency[cn].find_first(); n2 != red_adjacency[cn].npos; n2 = red_adjacency[cn].find_next(n2)) {
                        ADDONEEDGE(g, n + cn, n + (int) n2, m);
                    }
                }
            }

            densenauty(g, lab, ptn, orbits, &options, &stats, m, 2*n, NULL);

            for (auto i = 0; i < adjacency.size(); ++i) {
                orbitso[i] = orbits[i];
            }
        }

    private:
        std::vector<char> _deleted;
    };
}
#endif //TWW_BB_GRAPH_H
