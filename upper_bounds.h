#ifndef TWW_BB_UPPER_BOUNDS_H
#define TWW_BB_UPPER_BOUNDS_H
#include "tww.h"
#include "graph.h"

using namespace std;
namespace tww {
    std::mt19937 device;
    std::uniform_real_distribution<double> real_device(0,1);
    vector<double> sampled_values;

    static pair<node_t, vector<pair<node_t, node_t>>> greedy(Graph &og) {
        auto g = og.copy(false);
        vector<pair<node_t, node_t>> degrees;
        vector<pair<node_t, node_t>> contractions;
        degrees.reserve(g.num_nodes());
        contractions.reserve(g.num_nodes());
        node_t c_min_degree = 0;
        vector<dynamic_bitset<>> tnb;
        tnb.reserve(g.num_nodes());

        for (node_t n = 0; n < g.num_nodes(); ++n) {
            node_t node_min = INVALID_NODE;

            auto cnb = dynamic_bitset<>(g.num_nodes());
            for (auto x = g.adjacency[n].find_first();
                 x != g.adjacency[n].npos; x = g.adjacency[n].find_next(x)) {
                cnb |= g.adjacency[x];
            }
            cnb.reset(n);
            tnb.push_back(cnb);
            for (auto x = cnb.find_first();
                 x != cnb.npos; x = cnb.find_next(x)) {
                auto diff = g.adjacency[n] ^ g.adjacency[x];
                diff.reset(n);
                diff.reset(x);
                node_min = min(node_min, static_cast<node_t>(diff.count()));
            }
            degrees.emplace_back(node_min, n);
            c_min_degree = max(node_min, c_min_degree);
        }

        std::sort(degrees.begin(), degrees.end(), greater<>());

        vector<pair<node_t, node_t>> new_degrees;
        new_degrees.reserve(g.num_nodes());

        while(g.available_num > 1) {
            new_degrees.clear();
            bool contracted = false;
            for(auto& cd : degrees) {
                if (! g.is_deleted(cd.second)) {
                    auto cnb = (tnb[cd.second] | g.red_adjacency[cd.second]) & g.available;
                    for(auto x=cnb.find_first(); x != cnb.npos; x=cnb.find_next(x)) {
                        auto red = (g.adjacency[cd.second] ^ g.adjacency[x]) | g.red_adjacency[cd.second] | g.red_adjacency[x];
                        red.reset(x);
                        red.reset(cd.second);

                        if (red.count() <= c_min_degree) {
                            bool is_valid = true;
                            auto new_red = red - g.red_adjacency[cd.second];
                            auto created = new_red - g.red_adjacency[x];

                            for(auto z=created.find_first(); z != created.npos; z = created.find_next(z)) {
                                if (g.red_adjacency[z].count() + 1 > c_min_degree) {
                                    is_valid = false;
                                    break;
                                }
                            }

                            if (is_valid) {
                                assert(! g.is_deleted(x));
                                g.remove(x);
                                for(auto z=new_red.find_first(); z != new_red.npos; z = new_red.find_next(z)) {
                                    g.add_red_edge(cd.second, z);
                                }
                                contracted = true;
                                contractions.emplace_back(x, cd.second);
                                break;
                            }
                        }
                    }

                    if (contracted)
                        continue;
                }
            }

            if (! contracted)
                ++c_min_degree;
        }

        return {c_min_degree, contractions};
    }

    static pair<node_t, vector<pair<node_t, node_t>>> greedy2(Graph &og, node_t ub) {
        auto g = og.copy(false);
        node_t min_degree = 0;
        vector<dynamic_bitset<>> tnb;
        vector<pair<node_t, node_t>> contractions;
        contractions.reserve(g.num_nodes());
        tnb.reserve(g.num_nodes());

        vector<pair<node_t, node_t>> all_degrees;

        for (node_t n = 0; n < g.num_nodes(); ++n) {
            auto cnb = dynamic_bitset<>(g.num_nodes());
            for (auto x = g.adjacency[n].find_first();
                 x != g.adjacency[n].npos; x = g.adjacency[n].find_next(x)) {
                cnb |= g.adjacency[x];
            }
            cnb.reset(n);
            tnb.push_back(cnb);
        }

        vector<pair<node_t, dynamic_bitset<>>> new_degrees;
        new_degrees.reserve(g.num_nodes());


        while(g.available_num > 1) {
            new_degrees.clear();
            dynamic_bitset<> c_min_red;
            node_t c_min_degree = INVALID_NODE;
            pair<node_t, node_t> c_min_contraction = {INVALID_NODE, INVALID_NODE};
            node_t decrease_size = 0;


            for(node_t n=0; n < g.num_nodes(); ++n) {
                if (! g.is_deleted(n)) {
                    auto cnb = (tnb[n] | g.red_adjacency[n]) & g.available;

                    for(auto x=cnb.find_first(); x != cnb.npos; x=cnb.find_next(x)) {
                        auto red = (g.adjacency[n] ^ g.adjacency[x]) | g.red_adjacency[n] | g.red_adjacency[x];
                        red.reset(x);
                        red.reset(n);

                        auto new_degree = static_cast<node_t>(red.count());

                        if (new_degree <= c_min_degree) {
                            auto new_red = red - g.red_adjacency[n];
                            auto created = new_red - g.red_adjacency[x];

                            for (auto z = created.find_first(); new_degree <= c_min_degree && z != created.npos; z = created.find_next(z)) {
                                new_degree = max(new_degree, static_cast<node_t>(g.red_adjacency[z].count() + 1));
                            }

                            if (new_degree < c_min_degree) {
                                c_min_degree = new_degree;
                                c_min_contraction.first = n;
                                c_min_contraction.second = x;
                                c_min_red = new_red;
                                decrease_size = (g.red_adjacency[n] & g.red_adjacency[x]).count();
                            } else if (new_degree == c_min_degree) {
                                node_t new_decrease_size = (g.red_adjacency[n] & g.red_adjacency[x]).count();
                                if (new_decrease_size < decrease_size) {
                                    c_min_red = new_red;
                                    decrease_size = new_decrease_size;
                                    c_min_contraction.first = n;
                                    c_min_contraction.second = x;
                                }
                            }
                        }
                    }
                }
            }

            if (c_min_contraction.first == INVALID_NODE) {
                for(node_t n=0; n < g.num_nodes(); ++n) {
                    if (! g.is_deleted(n)) {
                        if (c_min_contraction.first == INVALID_NODE)
                            c_min_contraction.first = n;
                        else {
                            c_min_contraction.second = n;

                            auto red = (g.adjacency[c_min_contraction.first] ^ g.adjacency[c_min_contraction.second])
                                    | g.red_adjacency[c_min_contraction.first] | g.red_adjacency[c_min_contraction.second];
                            red.reset(c_min_contraction.first);
                            red.reset(c_min_contraction.second);

                            auto new_degree = static_cast<node_t>(red.count());

                            auto new_red = red - g.red_adjacency[c_min_contraction.first];
                            auto created = new_red - g.red_adjacency[c_min_contraction.second];

                            for (auto z = created.find_first(); new_degree < c_min_degree && z != created.npos; z = created.find_next(z)) {
                                new_degree = max(new_degree, static_cast<node_t>(g.red_adjacency[z].count() + 1));
                            }

                            c_min_degree = new_degree;
                            c_min_red = new_red;
                        }
                    }
                }
            }

            if (c_min_degree >= ub)
                return {INVALID_NODE, vector<pair<node_t, node_t>>()};

            g.remove(c_min_contraction.second);
            for (auto z = c_min_red.find_first(); z != c_min_red.npos; z = c_min_red.find_next(z)) {
                g.add_red_edge(z, c_min_contraction.first);
            }
            contractions.emplace_back(c_min_contraction.second, c_min_contraction.first);

            min_degree = max(min_degree, c_min_degree);
        }

        return {min_degree, contractions};
    }

    static pair<node_t, vector<pair<node_t, node_t>>> greedy3(Graph &og, node_t ub) {
        auto g = og.copy(false);
        node_t min_degree = 0;
        vector<dynamic_bitset<>> tnb;
        vector<pair<node_t, node_t>> contractions;
        contractions.reserve(g.num_nodes());
        tnb.reserve(g.num_nodes());

        vector<pair<node_t, node_t>> all_degrees;

        for (node_t n = 0; n < g.num_nodes(); ++n) {
            auto cnb = dynamic_bitset<>(g.num_nodes());
            for (auto x = g.adjacency[n].find_first();
                 x != g.adjacency[n].npos; x = g.adjacency[n].find_next(x)) {
                cnb |= g.adjacency[x];
            }
            cnb.reset(n);
            tnb.push_back(cnb);
        }

        vector<pair<node_t, dynamic_bitset<>>> new_degrees;
        new_degrees.reserve(g.num_nodes());

        while(g.available_num > 1) {
            new_degrees.clear();
            dynamic_bitset<> c_min_red;

            node_t c_min_degree = INVALID_NODE;
            pair<node_t, node_t> c_min_contraction = {INVALID_NODE, INVALID_NODE};
            dynamic_bitset<> c_max_red;
            node_t c_max_degree = INVALID_NODE;
            pair<node_t, node_t> c_max_contraction = {INVALID_NODE, INVALID_NODE};

            for(node_t n=0; n < g.num_nodes(); ++n) {
                if (! g.is_deleted(n)) {
                    auto cnb = (tnb[n] | g.red_adjacency[n]) & g.available;

                    for(auto x=cnb.find_first(); x != cnb.npos; x=cnb.find_next(x)) {
                        auto red = (g.adjacency[n] ^ g.adjacency[x]) | g.red_adjacency[n] | g.red_adjacency[x];
                        red.reset(x);
                        red.reset(n);

                        auto new_degree = static_cast<node_t>(red.count());

                        if (new_degree <= min_degree || new_degree < c_min_degree) {
                            auto new_red = red - g.red_adjacency[n];
                            auto created = new_red - g.red_adjacency[x];

                            for (auto z = created.find_first(); new_degree <= c_min_degree && z != created.npos; z = created.find_next(z)) {
                                new_degree = max(new_degree, static_cast<node_t>(g.red_adjacency[z].count() + 1));
                            }

                            if (new_degree < c_min_degree) {
                                c_min_degree = new_degree;
                                c_min_contraction.first = n;
                                c_min_contraction.second = x;
                                c_min_red = new_red;
                            }
                            if (new_degree <= min_degree && created.count() < c_max_degree) {
                                c_max_degree = created.count();
//                            if (new_degree <= min_degree && (c_max_degree == INVALID_NODE || new_red.count() < c_max_degree)) {
//                                c_max_degree = new_red.count();
                                c_max_contraction.first = n;
                                c_max_contraction.second = x;
                                c_max_red = new_red;
                            }
                        }
                    }
                }
            }

            if (c_min_degree >= ub)
                return {INVALID_NODE, vector<pair<node_t, node_t>>()};

            if (c_min_contraction.first == INVALID_NODE && c_max_contraction.first == INVALID_NODE) {
                for(node_t n=0; n < g.num_nodes(); ++n) {
                    if (! g.is_deleted(n)) {
                        if (c_min_contraction.first == INVALID_NODE)
                            c_min_contraction.first = n;
                        else {
                            c_min_contraction.second = n;

                            auto red = (g.adjacency[c_min_contraction.first] ^ g.adjacency[c_min_contraction.second])
                                       | g.red_adjacency[c_min_contraction.first] | g.red_adjacency[c_min_contraction.second];
                            red.reset(c_min_contraction.first);
                            red.reset(c_min_contraction.second);

                            auto new_degree = static_cast<node_t>(red.count());

                            auto new_red = red - g.red_adjacency[c_min_contraction.first];
                            auto created = new_red - g.red_adjacency[c_min_contraction.second];

                            for (auto z = created.find_first(); new_degree < c_min_degree && z != created.npos; z = created.find_next(z)) {
                                new_degree = max(new_degree, static_cast<node_t>(g.red_adjacency[z].count() + 1));
                            }

                            c_min_degree = new_degree;
                            c_min_red = new_red;
                        }
                    }
                }
            }

            auto x1 = (c_max_contraction.first != INVALID_NODE && c_min_degree > 0) ? c_max_contraction.first : c_min_contraction.first;
            auto x2 = (c_max_contraction.first != INVALID_NODE && c_min_degree > 0) ? c_max_contraction.second : c_min_contraction.second;
            auto& nb = (c_max_contraction.first != INVALID_NODE && c_min_degree > 0) ? c_max_red : c_min_red;

            g.remove(x2);
            for (auto z = nb.find_first(); z != nb.npos; z = nb.find_next(z)) {
                g.add_red_edge(x1, z);
            }
            contractions.emplace_back(x2, x1);

            if (c_max_contraction.first == INVALID_NODE)
                min_degree = max(min_degree, c_min_degree);
        }

        return {min_degree, contractions};
    }

    static pair<node_t, vector<pair<node_t, node_t>>> greedy4(Graph &og, node_t ub, int num_iterations=10000, int rounds=1) {
        vector<vector<pair<double, pair<node_t, node_t>>>> contraction_list(og.num_nodes());

        auto g = og.copy(false);
        node_t min_degree = ub-1;
        vector<dynamic_bitset<>> tnb;
        vector<pair<node_t, node_t>> contractions;
        vector<dynamic_bitset<>> backtrack_reds;
        contractions.reserve(g.num_nodes());
        tnb.reserve(g.num_nodes());
        int c_iteration = 0;
        int c_round = 0;

        vector<pair<node_t, node_t>> all_degrees;

        for (node_t n = 0; n < g.num_nodes(); ++n) {
            auto cnb = dynamic_bitset<>(g.num_nodes());
            for (auto x = g.adjacency[n].find_first();
                 x != g.adjacency[n].npos; x = g.adjacency[n].find_next(x)) {
                cnb |= g.adjacency[x];
            }
            cnb.reset(n);
            tnb.push_back(cnb);
        }

        while(g.available_num > 1) {
            for (node_t n = 0; n < g.num_nodes(); ++n) {
                if (!g.is_deleted(n)) {
                    auto cnb = (tnb[n] | g.red_adjacency[n]) & g.available;
                    cnb = g.available;

                    for (auto x = cnb.find_next(n); x != cnb.npos; x = cnb.find_next(x)) {
                        auto red = (g.adjacency[n] ^ g.adjacency[x]) | g.red_adjacency[n] | g.red_adjacency[x];

                        red.reset(x);
                        red.reset(n);

                        auto new_degree = static_cast<node_t>(red.count());

                        if (new_degree <= min_degree) {
                            auto new_red = red - g.red_adjacency[n];
                            auto created = new_red - g.red_adjacency[x];

                            for (auto z = created.find_first();
                                 new_degree <= min_degree && z != created.npos; z = created.find_next(z)) {
                                new_degree = max(new_degree, static_cast<node_t>(g.red_adjacency[z].count() + 1));
                            }

                            double new_value = ((double)created.count()) - ((double)(g.red_adjacency[n] & g.red_adjacency[x]).count());
                            if (new_degree <= min_degree) {
                                contraction_list[contractions.size()].emplace_back(new_value + real_device(device), pair<node_t, node_t>(n, x));
                            }
                        }
                    }
                }
            }

            if (contraction_list[contractions.size()].empty()) {
                if ((c_iteration >= num_iterations && c_round >= rounds - 1) || contractions.empty()) {
                    contractions.clear();
                    return {INVALID_NODE, contractions};
                }

                node_t target_depth = INVALID_NODE;
                if (c_iteration >= num_iterations) {
                    for(node_t cc=0; cc < contractions.size(); ++cc) {
                        if (! contraction_list[cc].empty()) {
                            target_depth = cc;
                            break;
                        }
                    }
                    cout << target_depth << endl;
                    c_iteration = 0;
                    ++c_round;
                }

                while(!contractions.empty()) {
                    if (contraction_list[contractions.size()].empty() || device() % 3 == 0 || target_depth < contractions.size()) {
                        contraction_list[contractions.size()].clear();
                        g.restore(contractions.back().second);

                        for (auto z = backtrack_reds.back().find_first(); z != backtrack_reds.back().npos; z = backtrack_reds.back().find_next(z)) {
                            g.add_red_edge(z, contractions.back().first);
                        }
                        contractions.pop_back();
                        backtrack_reds.pop_back();
                    } else {
                        break;
                    }
                }

                assert(target_depth == INVALID_NODE || target_depth == contractions.size());

                if (contraction_list[contractions.size()].empty()) {
                    contractions.clear();
                    return {INVALID_NODE, contractions};
                }
                ++c_iteration;
            }

            assert(!contraction_list[contractions.size()].empty());

            sort(contraction_list[contractions.size()].begin(), contraction_list[contractions.size()].end(), greater<>());
            auto target_contraction = contraction_list[contractions.size()].back().second;
            contraction_list[contractions.size()].pop_back();

            g.remove(target_contraction.second);

            auto red = (g.adjacency[target_contraction.first] ^ g.adjacency[target_contraction.second]) | g.red_adjacency[target_contraction.first]
                       | g.red_adjacency[target_contraction.second];
            red.reset(target_contraction.second);
            red.reset(target_contraction.first);
            auto new_red = red - g.red_adjacency[target_contraction.first];

            for (auto z = new_red.find_first(); z != new_red.npos; z = new_red.find_next(z)) {
                g.add_red_edge(z, target_contraction.first);
            }

            contractions.emplace_back(target_contraction.second, target_contraction.first);
            backtrack_reds.push_back(std::move(new_red));
            assert(contractions.size() == backtrack_reds.size());
        }

        assert(g.available_num == 1);
        assert(contractions.size() == g.num_nodes() - 1);

        return {min_degree, contractions};
    }
};
#endif //TWW_BB_UPPER_BOUNDS_H
