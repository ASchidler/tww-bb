
#ifndef TWW_BB_TWWBB_H
#define TWW_BB_TWWBB_H

#include <iostream>
#include "graph.h"
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <set>

#include <boost/functional/hash.hpp>
#include <utility>
#include <unistd.h>
#include <sys/resource.h>
#include <iomanip>
#include <chrono>
#include <algorithm>

#include "BbParameters.h"
#include "LowerBoundGraph.h"
#include "tools.h"
#include "lower_bounds.h"

namespace tww {
    /** Get a canonical representation of the partition, using only the vertices that took place in a contraction in a specific order.  */
    inline void get_canonical_partition(const vector<node_t>& input, vector<node_t>& output, vector<vector<node_t>>& tmp) {
        output.clear();
        for(auto& ctmp : tmp)
            ctmp.clear();

        for(size_t i=0; i < input.size(); ++i) {
            if (input[i] != i)
                tmp[max(input[i], static_cast<node_t>(i))].push_back(min(input[i],  static_cast<node_t>(i)));
        }

        for(auto i=0; i < tmp.size(); ++i) {
            if (!tmp[i].empty()) {
                output.push_back(i);
                output.insert(output.end(), tmp[i].begin(), tmp[i].end());
            }
        }
    }

    struct Stats {
        explicit Stats(node_t num_nodes) : depths(num_nodes) {
            field_width = std::to_string(SIZE_MAX).length();
        }

        size_t exceeded = 0;
        size_t calls = 0;
        size_t order_filtered = 0;
        size_t cache_filtered = 0;
        size_t isomorphic_filtered = 0;
        size_t quick_isomorphic_filtered = 0;
        size_t field_width;
        size_t orbits = 0;
        size_t twins = 0;
        size_t queue = 0;
        size_t lb_future = 0;
        size_t lb_sub = 0;
        size_t reasons = 0;

        vector<size_t> depths;

        void print(BbParameters& params, node_t ub, node_t lb, bool header=true) {
            if (! params.verbose)
                return;

            if (header) {
                cout    << setw(field_width) << "Calls" << setw(field_width) << "Ordered"<< setw(field_width) << "Quick"
                        << setw(field_width) << "Cached"<< setw(field_width) << "Isomorphic"<< setw(field_width) << "Exceeded"
                        << setw(field_width) << "Partition Cache" << setw(field_width) << "Graph Cache"
                        << setw(field_width) << "P Cache Buckets" << setw(field_width) << "Orbits" << endl;
            }
            cout << setw(field_width) << calls;
            cout << setw(field_width) << order_filtered;
            cout << setw(field_width) << quick_isomorphic_filtered;
            cout << setw(field_width) << cache_filtered;
            cout << setw(field_width) << isomorphic_filtered;
            cout << setw(field_width) << exceeded;
            cout << setw(field_width) << params.cache.get_size();
            cout << setw(field_width) << params.g_cache.get_size();
            cout << setw(field_width) << params.cache.get_buckets();
            cout << setw(field_width) << orbits;
            cout << endl;

            if (header) {
                cout                << setw(field_width) << "Queue Size"
                                    << setw(field_width) << "Twins"
                                    << setw(field_width) << "LB"
                                    << setw(field_width) << "UB"
                                    << setw(field_width) << "Subgraph LB"
                                    << setw(field_width) << "Future LB"
                                    << endl ;
            }
            cout << setw(field_width) << queue;
            cout << setw(field_width) << twins;
            cout << setw(field_width) << lb;
            cout << setw(field_width) << ub;
            cout << setw(field_width) << lb_sub << "/" << reasons;
            cout << setw(field_width) << lb_future
            << endl;

            for(auto n=0; n < depths.size(); n++) {
                if (n%10 == 0)
                    cout << endl;
                cout << setw(field_width) << depths[n];
            }
            cout << endl;
            cout << endl;
        }
    };

    node_t find_tww_rec(node_t ub, node_t lb, BbParameters& ps, Stats& stats, bool heuristic, node_t iso_low, node_t iso_high, bool verbose, long timeout);
    node_t find_tww(Graph& g, node_t ub, node_t lb, bool heuristic, bool verbose, BbParameters& parameters, long timeout);

    /** Checks if the given subgraph has tww ub by checking all possible contractions */
    inline bool subgraph_exceeds(BbParameters& ps, vector<node_t>& nodes, dynamic_bitset<>& cnb, node_t ub, bool stop_rec_call) {
        bool ran = false;
        bool all_exceeded = true;

        // Minimum size required to have red degree ub
        if (nodes.size() >= ub + 2) {
            for (auto in1 = 0; in1 < nodes.size() && all_exceeded; ++in1) {
                auto n1 = nodes[in1];
                assert(n1 != INVALID_NODE);
                assert(cnb.test(n1));
                cnb.reset(n1);

                for (auto in2 = in1 + 1; in2 < nodes.size() && all_exceeded; ++in2) {
                    ran = true;
                    auto n2 = nodes[in2];
                    assert(n2 != INVALID_NODE);
                    assert(n1 != n2);
                    assert(cnb.test(n2));
                    cnb.reset(n2);

                    auto red_nb = ((ps.g.red_adjacency[n1] | ps.g.red_adjacency[n2] |
                                    (ps.g.adjacency[n1] ^ ps.g.adjacency[n2])) & cnb);

                    // The contraction vertex does not exceed the bound?
                    if (red_nb.count() < ub) {
                        // Check other vertices affected by the contraction, their degree might have increased by one.
                        all_exceeded = false;
                        for (auto sub_node: nodes) {
                            if (sub_node != n1 && sub_node != n2 && red_nb.test(sub_node) &&
                                    !ps.g.red_adjacency[n1].test(sub_node) &&
                                    !ps.g.red_adjacency[n2].test(sub_node) &&
                                (ps.g.red_adjacency[sub_node] & cnb).count() == ub - 1) {
                                    all_exceeded = true;
                                    break;
                            }
                        }

                        // If the contraction does not exceed the lower bound, remove n2 and check if the lower bound holds then.
                        if (!all_exceeded && !stop_rec_call) {
                            // Remove n2 and try if it exceeds without n2
                            swap(nodes.back(), nodes[in2]);
                            nodes.pop_back();
                            cnb.set(n1);

                            assert(cnb.count() == nodes.size());
                            auto exceeds = subgraph_exceeds(ps, nodes, cnb, ub, false);
                            if (! exceeds) {
                                nodes.push_back(n2);
                                swap(nodes.back(), nodes[in2]);
                                cnb.set(n2);

                                swap(nodes.back(), nodes[in1]);
                                nodes.pop_back();
                                cnb.reset(n1);
                                exceeds = subgraph_exceeds(ps, nodes, cnb, ub, true);
                                if (! exceeds) {
                                    nodes.push_back(n1);
                                    swap(nodes.back(), nodes[in1]);
                                    cnb.set(n1);
                                }
                            }

                            assert(cnb.count() == nodes.size());

                            return exceeds;
                        }
                        if (!all_exceeded) {
                            cnb.set(n2);
                            break;
                        }
                    }

                    cnb.set(n2);
                }

                cnb.set(n1);
            }
        }

        return ran && all_exceeded;
    }

    inline node_t check_subgraph(const Graph& g, bool use_cache, bool use_order_cache, const vector<node_t>& nodes, node_t ub, node_t lb, long timeout=0, bool initialize_reds=false,
                                 vector<pair<node_t, node_t>>* red_edges= nullptr) {
        Graph ng(nodes.size());
        vector<node_t> node_map(g.num_nodes(), INVALID_NODE);
        dynamic_bitset<> cnb(g.num_nodes());
        vector<node_t> r_map;
        r_map.reserve(nodes.size());

        for(auto n : nodes) {
            node_map[n] = r_map.size();
            r_map.push_back(n);
            cnb.set(n);
        }

        assert(r_map.size() == nodes.size());
        assert(r_map.size() == cnb.count());

        // Use find_first here and add edges for all n1,n2 not just n1 > n2 as n1 or n2 might be deleted.
        for (auto n1: nodes) {
            assert(node_map[n1] != INVALID_NODE);
            for (auto n2 =  g.adjacency[n1].find_first();
                 n2 != g.adjacency[n1].npos; n2 = g.adjacency[n1].find_next(n2)) {
                if (node_map[n2] != INVALID_NODE) {
                    ng.add_edge(node_map[n1], node_map[n2]);
                }
            }

            if (initialize_reds) {
                if (red_edges != nullptr) {
                    for(auto& cre: *red_edges) {
                        if (node_map[cre.first] != INVALID_NODE && node_map[cre.second] != INVALID_NODE) {
                            ng.add_red_edge(node_map[cre.first], node_map[cre.second]);
                        }
                    }
                } else {
                    for (auto n2 = g.red_adjacency[n1].find_first();
                         n2 != g.red_adjacency[n1].npos; n2 = g.red_adjacency[n1].find_next(n2)) {
                        if (node_map[n2] != INVALID_NODE) {
                            ng.add_red_edge(node_map[n1], node_map[n2]);
                        }
                    }
                }
            }
        }

        BbParameters parameters(ng, 0,  false, false, false, false, use_cache, use_order_cache);
        if (initialize_reds) {
            for (node_t n=0; n < ng.num_nodes(); ++n) {
                parameters.red_counts[0][n] = ng.red_adjacency[n].count();
                lb = max(lb, parameters.red_counts[0][n]);
            }
        }

        auto result = find_tww(ng, ub + 1, lb, false, false, parameters, timeout);

        if (result == TWW_TIMEOUT)
            return 0;
        if (result == INVALID_NODE)
            return ub;

        return result;
    }

    inline void subgraph_minimize(BbParameters& ps, vector<node_t>& nodes, dynamic_bitset<>& cnb, node_t ub, vector<pair<node_t, node_t>>& contractions, node_t depth,  vector<node_t>& black_nodes, bool edgesFirst = false, bool full_check = false, bool onlyNodes=false) {
        // This is the case if caching showed exceeding, in that case we may not be able to minimize
        // TODO: Check if these entries actually make sense, e.g., if these occur as subgraphs.

        vector<pair<node_t, node_t>> removed;
        // First try to get rid of unnecessary nodes
        node_t removed_nodes = 0;
        node_t removed_edges = 0;

//        sort(nodes.begin(), nodes.end(), [&](const node_t n1, const node_t n2) {
//           return ((ps.g.red_adjacency[n1] | ps.g.adjacency[n1]) & cnb).count() < ((ps.g.red_adjacency[n2] | ps.g.adjacency[n2]) & cnb).count();
//        });

        for (auto in = 0; in < nodes.size() && !edgesFirst && nodes.size() > ub + 2; ++in) {
            auto cn = nodes[in];
            assert(cnb.test(cn));
            cnb.reset(cn);
            swap(nodes.back(), nodes[in]);
            nodes.pop_back();

            if (!subgraph_exceeds(ps, nodes, cnb, ub, false) && (!full_check ||
                                                                 check_subgraph(ps.g, ps.use_cache, ps.use_order_cache,
                                                                                nodes, ub, ub - 1, 5, true) <
                                                                 ub)) {
                nodes.push_back(cn);
                swap(nodes[in], nodes.back());
                assert(!cnb.test(cn));
                cnb.set(cn);
            } else {
                --in;
                ++removed_nodes;
//                sort(nodes.begin(), nodes.end(), [&](const node_t n1, const node_t n2) {
//                    return ((ps.g.red_adjacency[n1] | ps.g.adjacency[n1]) & cnb).count() < ((ps.g.red_adjacency[n2] | ps.g.adjacency[n2]) & cnb).count();
//                });
            }
        }
        assert(nodes.size() == cnb.count());

        if (!onlyNodes) {
            for (auto cd = depth + 1; cd > 0; --cd) {
                auto &ce = ps.queues[cd - 1]->at(ps.queue_pointers[cd - 1]);
                if (cnb.test(ce.n2)) {
                    if (ce.reds.any()) {
                        auto reds = ce.reds & cnb;

                        if (reds.empty())
                            continue;

                        for (auto cr = reds.find_first();
                             cr != reds.npos; cr = reds.find_next(cr)) {
                            ps.g.remove_red_edge(cr, ce.n2);
                        }

                        if (subgraph_exceeds(ps, nodes, cnb, ub, true) ||
                            (full_check && check_subgraph(ps.g, ps.use_cache,
                                                          ps.use_order_cache,
                                                          nodes, ub,
                                                          ub - 1, 5, true) >=
                                           ub)) {
                            for (auto cr = reds.find_first();
                                 cr != reds.npos; cr = reds.find_next(cr)) {
                                removed.emplace_back(ce.n2, cr);
                                ++removed_edges;
                            }
                        } else {
                            for (auto cr = reds.find_first();
                                 cr != reds.npos; cr = reds.find_next(cr)) {
                                contractions.emplace_back(max(ce.n2, static_cast<node_t>(cr)),
                                                          min(ce.n2, static_cast<node_t>(cr)));
                                ps.g.add_red_edge(cr, ce.n2);
                            }
                        }
                    }
                }
            }

            sort(contractions.begin(), contractions.end());
            contractions.erase(unique(contractions.begin(), contractions.end()), contractions.end());
            for (auto c_idx = contractions.size(); c_idx > 0; --c_idx) {
                auto &cc = contractions[c_idx - 1];
                if (!ps.g.red_adjacency[cc.first].test(cc.second)) {
                    swap(contractions[c_idx - 1], contractions.back());
                    contractions.pop_back();
                }
            }

            for(node_t cn1=0; cn1 < ps.g.num_nodes(); ++cn1) {
                if (! ps.g.is_deleted(cn1) && cnb.test(cn1)) {
                    for (node_t cn2 = cn1 + 1; cn2 < ps.g.num_nodes(); ++cn2) {
                        if (! ps.g.is_deleted(cn2) && cnb.test(cn2)) {
                            if (ps.g.red_adjacency[cn1].test(cn2)) {
                                bool found = false;
                                for (auto& cr : contractions) {
                                    if ((cr.first == cn1 || cr.second == cn1) && (cr.second == cn2 || cr.first == cn2)) {
                                        found = true;
                                        break;
                                    }
                                }
                                assert(found);
                            }
                        }
                    }
                }
            }

            for (auto in = 0; in < nodes.size() && edgesFirst && nodes.size() > ub + 2; ++in) {
                auto cn = nodes[in];
                assert(cnb.test(cn));
                cnb.reset(cn);
                swap(nodes.back(), nodes[in]);
                nodes.pop_back();

                if (!subgraph_exceeds(ps, nodes, cnb, ub, false) && (!full_check || check_subgraph(ps.g, ps.use_cache,
                                                                                                   ps.use_order_cache,
                                                                                                   nodes, ub + 1,
                                                                                                   ub - 1, 5, true, &contractions) <
                                                                                    ub)) {
                    nodes.push_back(cn);
                    swap(nodes[in], nodes.back());
                    assert(!cnb.test(cn));
                    cnb.set(cn);
                } else {
                    --in;
                    ++removed_nodes;
                }
            }

            for (auto i = contractions.size(); i > 0; --i) {
                if (!cnb.test(contractions[i - 1].first) || !cnb.test(contractions[i - 1].second)) {
                    swap(contractions.back(), contractions[i - 1]);
                    contractions.pop_back();
                }
            }

            for (auto cn: nodes) {
                if (!(ps.g.red_adjacency[cn] & cnb).any())
                    black_nodes.push_back(cn);
            }

            for (auto &cp: removed) {
                ps.g.add_red_edge(cp.first, cp.second);
            }
        } else {
            for (auto cn: nodes) {
                auto creds = ps.g.red_adjacency[cn] & cnb;

                for (auto cr = creds.find_next(cn);
                     cr != creds.npos; cr = creds.find_next(cr)) {
                    contractions.emplace_back(max(cn, static_cast<node_t>(cr)), min(cn, static_cast<node_t>(cr)));
                }
            }
        }
    }

     inline node_t find_tww(Graph& g, node_t ub, node_t lb, bool heuristic, bool verbose, BbParameters& parameters, long timeout) {
        auto stats = Stats(g.num_nodes());
        auto result = find_tww_rec(ub, lb, parameters,stats, heuristic, 0, 0, verbose, timeout);

        stats.print(parameters, result, lb, true);

        return result;
    }
}
#endif //TWW_BB_TWWBB_H
