
#include "LowerBoundGraph.h"

namespace tww {
    LowerBoundGraph::LowerBoundGraph(dynamic_bitset<> nodes, const vector<pair<node_t, node_t>> &red_edges,
                                     size_t watched_red, BbParameters &ps, vector<pair<node_t, vector<node_t>>>& black_twins) : watched_red(
            watched_red), ps(ps) {
        for(auto& ce : black_twins) {
            this->black_twins.emplace_back(ce.first, 0);
            this->black_twins.back().second.insert(this->black_twins.back().second.end(), ce.second.begin(), ce.second.end());
        }
        this->red_edges.insert(this->red_edges.end(), red_edges.begin(), red_edges.end());
        this->nodes = std::move(nodes);
        n1 = this->red_edges[watched_red].first;
        n2 = this->red_edges[watched_red].second;
        watched_index = ps.lower_bound_graphs[n1][n2].size();
        ps.lower_bound_graphs[n1][n2].push_back(this);

        ps.all_lower_bound_graphs.push_back(this);

        ps.lower_bound_by_node[n1].push_back(this);
        ps.lower_bound_by_node[n2].push_back(this);
    }

    void LowerBoundGraph::update_entry(node_t depth) {
        auto o_n1 = red_edges[watched_red].first;
        auto o_n2 = red_edges[watched_red].second;

        node_t n_n1 = max(
                ps.partitions[depth+1][o_n1],
                ps.partitions[depth+1][o_n2]);
        node_t n_n2 = min(
                ps.partitions[depth+1][o_n1],
                ps.partitions[depth+1][o_n2]);

        bool was_present = all_present;

        // If we would create a conflict, skip update
        if (n_n1 == n_n2) {
            if (not_subset_witness == INVALID_NODE)
                set_witness(n_n1);
            return;
        }

        // Check if conflict has been resolved
        if (not_subset_witness != INVALID_NODE) {
            node_t cn1 = conflicting_nodes.first != INVALID_NODE ? conflicting_nodes.first : n1;
            node_t cn2 = conflicting_nodes.second != INVALID_NODE ? conflicting_nodes.second : n2;

            if (ps.partitions[depth+1][cn1] == not_subset_witness && ps.partitions[depth+1][cn2] == not_subset_witness) {
                return;
            } else
                unset_witness();
        }

        if (ps.g.red_adjacency[n_n1].test(n_n2) && !all_present && not_subset_witness == INVALID_NODE) {
            size_t new_contraction = SIZE_MAX;
            size_t conflict_contraction = SIZE_MAX;
            node_t c_witness = INVALID_NODE;

            // Find different edge that is not yet present
            for (auto i = 0; i < red_edges.size(); ++i) {
                if (i != watched_red) {
                    auto &cc = red_edges[i];
                    // First check if there is a conflict with that edge
                    if (ps.partitions[depth + 1][cc.first] == ps.partitions[depth + 1][cc.second]) {
                        assert(conflict_contraction == SIZE_MAX || c_witness != INVALID_NODE);
                        if (c_witness == INVALID_NODE) {
                            c_witness = ps.partitions[depth + 1][cc.first];
                            conflict_contraction = i;
                            break;
                        }
                    } else if (!ps.g.red_adjacency[ps.partitions[depth + 1][cc.first]].test(
                            ps.partitions[depth + 1][cc.second])) {
                        // Edge does not occur. Do not break here to ensure that we do actually still have a valid subgraph.
                        new_contraction = i;
                    }
                }
            }

            // No conflict and no non-present red edge found
            if (SIZE_MAX == new_contraction && SIZE_MAX == conflict_contraction) {
                all_present = true;
            } else {
                // Here we have to change the red edge.
                // Sanity check
                assert(watched_red != SIZE_MAX);
                assert(!all_present || not_subset_witness);

                node_t target_d = depth + 1;

                // In case of conflict, check when the two end nodes differed the last time
                if (conflict_contraction != SIZE_MAX) {
                    while (target_d > 0) {
                        --target_d;
                        if (ps.partitions[target_d][red_edges[conflict_contraction].first] !=
                            ps.partitions[target_d][red_edges[conflict_contraction].second])
                            break;
                        else
                            c_witness = ps.partitions[target_d][red_edges[conflict_contraction].first];
                    }
                } else {
                    conflict_contraction = new_contraction;
                }

                // Set conflict data
                if (c_witness != INVALID_NODE) {
                    set_witness(c_witness);
                }

                // Switch to new read edge
                watched_red = conflict_contraction;
                o_n1 = red_edges[watched_red].first;
                o_n2 = red_edges[watched_red].second;

                n_n1 = max(
                    ps.partitions[target_d][o_n1],
                    ps.partitions[target_d][o_n2]);
                n_n2 = min(
                    ps.partitions[target_d][o_n1],
                    ps.partitions[target_d][o_n2]);
            }
        } else if (all_present && !ps.g.red_adjacency[n_n1].test(n_n2)) {
            all_present = false;
        }

        if (n_n1 != n1 || n_n2 != n2) {
            update_entry(n_n1, n_n2);
        }

        // If we found out that all red edges are present, check if we really have all required nodes
        if (!was_present && all_present && not_subset_witness == INVALID_NODE)
            check_subgraph(depth);
    }

    void LowerBoundGraph::update_entry(node_t n_n1, node_t n_n2) {
        assert(n_n1 != n_n2);
        assert(n_n1 < ps.g.num_nodes() && n_n2 < ps.g.num_nodes());
        if (n_n1 != n1 || n_n2 != n2) {
            ps.lower_bound_graphs[n1][n2].back()->watched_index = watched_index;

            swap(ps.lower_bound_graphs[n1][n2].back(),
                 ps.lower_bound_graphs[n1][n2][watched_index]);
            ps.lower_bound_graphs[n1][n2].pop_back();

            watched_index = ps.lower_bound_graphs[n_n1][n_n2].size();
            ps.lower_bound_graphs[n_n1][n_n2].push_back(this);

            if (n1 != n_n1 && n1 != n_n2 && n1 != not_subset_witness) {
                auto sub_idx = std::find(ps.lower_bound_by_node[n1].begin(),
                                         ps.lower_bound_by_node[n1].end(), this);
                assert(sub_idx != ps.lower_bound_by_node[n1].end());
                iter_swap(sub_idx, ps.lower_bound_by_node[n1].rbegin());
                ps.lower_bound_by_node[n1].pop_back();
            }

            if (n2 != n_n1 && n2 != n_n2 && n2 != not_subset_witness) {
                auto sub_idx = std::find(ps.lower_bound_by_node[n2].begin(),
                                         ps.lower_bound_by_node[n2].end(), this);
                assert(sub_idx != ps.lower_bound_by_node[n2].end());
                iter_swap(sub_idx, ps.lower_bound_by_node[n2].rbegin());
                ps.lower_bound_by_node[n2].pop_back();
            }

            if (n1 != n_n1 && n2 != n_n1 && not_subset_witness != n_n1) {
                ps.lower_bound_by_node[n_n1].push_back(this);
            }

            if (n1 != n_n2 && n2 != n_n2 && not_subset_witness != n_n2) {
                ps.lower_bound_by_node[n_n2].push_back(this);
            }

            this->n1 = n_n1;
            this->n2 = n_n2;
        }
    }

    void LowerBoundGraph::set_witness(node_t cn, node_t first_witness, node_t second_witness) {
        assert(not_subset_witness == INVALID_NODE);
        assert(cn != INVALID_NODE);
        if (n1 != cn && n2 != cn) {
            ps.lower_bound_by_node[cn].push_back(this);
        }
        not_subset_witness = cn;
        conflicting_nodes.first = first_witness;
        conflicting_nodes.second = second_witness;
    }

    void LowerBoundGraph::unset_witness() {
        assert(not_subset_witness != INVALID_NODE);
        if (n1 != not_subset_witness && n2 != not_subset_witness) {
            auto sub_idx = std::find(ps.lower_bound_by_node[not_subset_witness].begin(),
                                     ps.lower_bound_by_node[not_subset_witness].end(), this);
            assert(sub_idx != ps.lower_bound_by_node[not_subset_witness].end());
            iter_swap(sub_idx, ps.lower_bound_by_node[not_subset_witness].rbegin());
            ps.lower_bound_by_node[not_subset_witness].pop_back();
        }
        not_subset_witness = INVALID_NODE;
        conflicting_nodes.first = INVALID_NODE;
        conflicting_nodes.second = INVALID_NODE;
    }

    void LowerBoundGraph::check_subgraph(node_t depth) {
        dynamic_bitset<> checker(ps.g.num_nodes());

        node_t witness = INVALID_NODE;
        node_t witness_n1 = INVALID_NODE;
        node_t witness_n2 = INVALID_NODE;

        // Ensure that the nodes exist as distinct nodes
        bool bijective = true;
        for (auto cnn = nodes.find_first();bijective && cnn != nodes.npos;cnn = nodes.find_next(cnn)) {
            // If already set, two nodes are mapped to the same position.
            if (checker.test_set(ps.partitions[depth + 1][cnn])) {
                bool found_alternative = false;
//                for(auto& cb : black_twins) {
//                    if (cb.first == cnn) {
//                        for(auto con : cb.second) {
//                            if (! checker.test_set(ps.partitions[depth+1][con])) {
//                                found_alternative = true;
//                                break;
//                            }
//                        }
//                    }
//                }

                if (! found_alternative) {
                    bijective = false;

                    if (witness == INVALID_NODE) {
                        witness = ps.partitions[depth + 1][cnn];
                        witness_n1 = cnn;

                        // Find second conflicting node
                        for (auto cnn2 = nodes.find_first(); cnn2 < cnn; cnn2 = nodes.find_next(cnn2)) {
                            if (ps.partitions[depth + 1][cnn] == ps.partitions[depth + 1][cnn2]) {
                                witness_n2 = cnn2;
                                break;
                            }
                        }
                        assert(witness_n2 != INVALID_NODE);

                        // Special case, where one node maps to the other.
                        if (witness == witness_n1)
                            witness_n1 = witness_n2;
                        if (witness == witness_n2)
                            witness_n2 = witness_n1;
                    }
                }
            }
        }
        if (bijective) {
            return;
        }

        assert(witness != INVALID_NODE);
        assert(witness_n1 != INVALID_NODE);
        assert(witness_n2 != INVALID_NODE);
        assert(witness_n1 != witness && witness_n2 != witness);
        set_witness(witness, witness_n1, witness_n2);
    }
}
