#include "twwbb2.h"

namespace tww {
    node_t find_tww_rec(node_t ub, node_t lb, BbParameters &ps, Stats &stats, bool heuristic, node_t iso_low, node_t iso_high,
                 bool verbose, long timeout) {
        node_t depth = 0;
        node_t initial_degree = 0;
        for(node_t n=0; n < ps.g.num_nodes(); ++n)
            initial_degree = max(initial_degree, ps.red_counts[0][n]);

        bool initialized = false;
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();

        dynamic_bitset<> old_justified(ps.g.num_nodes());
        dynamic_bitset<> reds(ps.g.num_nodes());
        dynamic_bitset<> c_reds(ps.g.num_nodes());
        vector<node_t> min_degrees(ps.g.num_nodes(), INVALID_NODE);
        vector<char> node_bools(ps.g.num_nodes(), false);

        vector<node_t> canonical_tmp;
        canonical_tmp.reserve(2 * ps.g.num_nodes());
        vector<vector<node_t>> canonical_tmp_working(ps.g.num_nodes());

        for (auto &ctw: canonical_tmp_working)
            ctw.reserve(ps.g.num_nodes());

        for (node_t n = 0; n < ps.g.num_nodes(); n++)
            ps.partitions[0][n] = n;

        // Fill default queue
        if (ps.fast_mode || ps.adaptive_fast_mode) {
            vector<tuple<node_t, node_t, node_t>> static_contraction_list;
            static_contraction_list.reserve(ps.g.num_nodes() * (ps.g.num_nodes() - 1) / 2);

            for (node_t n = 0; n < ps.g.num_nodes(); n++) {
                for (node_t n2 = n + 1; n2 < ps.g.num_nodes(); n2++) {
                    auto l_reds = ps.g.adjacency[n] ^ ps.g.adjacency[n2];
                    l_reds.reset(n2);
                    l_reds.reset(n);
                    auto c_degree = static_cast<node_t>(l_reds.count());

                    static_contraction_list.emplace_back(c_degree, n, n2);
                }
                auto &ce = static_contraction_list.back();
            }

            sort(static_contraction_list.begin(), static_contraction_list.end());

            ps.default_queue.reserve(static_contraction_list.size());
            for (auto &ce: static_contraction_list) {
                ps.default_queue.emplace_back(get<0>(ce), 0, get<1>(ce), get<2>(ce), dynamic_bitset<>(),
                                              dynamic_bitset<>(), ps.g.red_adjacency[get<2>(ce)], 0);
            }
        }

        auto check_contraction = [&](node_t cn, node_t cn2, bool &is_twin, node_t c_depth, QueueEntry *ce) {
            if (ps.orbits.size() > depth && !ps.orbits[depth].empty() && ps.orbits[c_depth][cn] != cn &&
                ps.orbits[c_depth][cn2] != cn2) {
                ++stats.depths[c_depth];
                stats.orbits++;
                return false;
            }

            // First check if the contraction would exceed the bound, only do this in non-fast mode, as lookahead count is not updated otherwise
            if (ps.lookahead_count[cn2][cn] >= ub && ce == nullptr) {
                min_degrees[cn] = min(min_degrees[cn], ps.lookahead_count[cn2][cn]);
                ++stats.exceeded;
                return false;
            }

            reds.reset();
            reds |= ps.g.adjacency[cn];
            reds ^= ps.g.adjacency[cn2];
            reds |= ps.g.red_adjacency[cn];
            reds -= ps.g.red_adjacency[cn2];

            reds.reset(cn2);
            reds.reset(cn);
            assert(!reds.test(cn));

            ////////
            node_t validate_reds = INVALID_NODE;
            if (VALIDATION_MODE) {
                ps.g.remove(cn);
                for (auto nx = reds.find_first(); nx != reds.npos; nx = reds.find_next(nx)) {
                    ps.g.add_red_edge(nx, cn2);
                }

                for (auto nx = 0; nx < ps.g.num_nodes(); ++nx) {
                    if (!ps.g.is_deleted(nx)) {
                        validate_reds = max(validate_reds, static_cast<node_t>(ps.g.red_adjacency[nx].count()));
                    }
                }

                for (auto nx = reds.find_first(); nx != reds.npos; nx = reds.find_next(nx)) {
                    ps.g.remove_red_edge(nx, cn2);
                }

                ps.g.restore(cn);
            }
            //////


            int deg_change = static_cast<int>(reds.count());
            node_t red_count = deg_change;

            if (ps.g.red_adjacency[cn].test(cn2))
                deg_change -= 1;

            assert(ps.queues[depth] == &ps.default_queue || ps.red_counts[c_depth][cn2] < ub);
            if (deg_change + ps.red_counts[c_depth][cn2] >= ub) {
                // There is another assignment further down
                min_degrees[cn] = min(min_degrees[cn], static_cast<node_t>(deg_change +
                                                                           ps.red_counts[c_depth][cn2]));
                ++stats.exceeded;
                assert(validate_reds >= ub);
                return false;
            }

            // Filter equivalent contractions, i.e. if n to n2 leads to the same graph as n to n3 then skip n to n3
            bool prior = false;

            // TODO: Skip this in fast mode?
            if (red_count == 1 && deg_change == 1) {
                for (auto &cp: ps.previous_contractions[c_depth]) {
                    if (cn2 == get<1>(cp) && cn == get<2>(cp) && get<0>(cp) == reds.find_first()) {
                        prior = true;
                        ++stats.quick_isomorphic_filtered;
                        ps.has_contraction[c_depth] = true;
                        break;
                    }
                }
                if (!prior) {
                    ps.previous_contractions[c_depth].emplace_back(cn, cn2, reds.find_first());
                }
            }

            if (prior) {
                return false;
            }

            // Check if any other node's degree exceeds the upper bound
            node_t max_degree = initialized ? ps.current_degree[c_depth - 1] : initial_degree;
            max_degree = max(max_degree, initial_degree);

            node_t max_degree_nodes = 0;

            if (deg_change + ps.red_counts[c_depth][cn2] > max_degree) {
                max_degree = deg_change + ps.red_counts[c_depth][cn2];
                max_degree_nodes = 1;
            } else if (deg_change + ps.red_counts[c_depth][cn2] == max_degree)
                ++max_degree_nodes;

            auto new_reds = reds - ps.g.red_adjacency[cn];

            if (new_reds.count() == 0) {
                auto r1 = ps.g.red_adjacency[cn];
                auto r2 = ps.g.red_adjacency[cn2];
                r1.reset(cn2);
                r2.reset(cn);
                is_twin = r1.is_subset_of(r2) || r2.is_subset_of(r1);
            }

            if (is_twin) {
                stats.twins++;
                if (ps.queues[c_depth] != &ps.default_queue)
                    ps.queues[c_depth]->clear();
            }

            bool exceeded = false;
            for (auto cln = new_reds.find_first();
                 cln != new_reds.npos; cln = new_reds.find_next(cln)) {
                assert(ps.red_counts[c_depth][cln] < ub);

                if (ps.red_counts[c_depth][cln] + 1 >= ub) {
                    exceeded = true;
                    min_degrees[cn] = min(min_degrees[cn],
                                          static_cast<node_t>(ps.red_counts[c_depth][cln] + 1));
                    ++stats.exceeded;
                    break;
                }
                if (ps.red_counts[c_depth][cln] + 1 > max_degree) {
                    max_degree = ps.red_counts[c_depth][cln] + 1;
                    max_degree_nodes = 1;
                } else if (ps.red_counts[c_depth][cln] + 1 == max_degree)
                    ++max_degree_nodes;
            }

            min_degrees[cn] = min(min_degrees[cn], max_degree);

            if (exceeded) {
                assert(! is_twin);
                assert(validate_reds >= ub);
                ++stats.depths[c_depth];
                return false;
            }

            if (ce == nullptr) {
                assert(validate_reds == INVALID_NODE || validate_reds == max_degree || (c_depth > 0 && ps.current_degree[c_depth-1] >= validate_reds) || (c_depth == 0 && initial_degree >= validate_reds));
                assert(ps.queues[c_depth] != &ps.default_queue);
                ps.queues[c_depth]->emplace_back(new_reds.count(), max_degree, cn, cn2, reds,
                                                 std::move(new_reds), ps.g.red_adjacency[cn2], new_reds.count() - (ps.g.red_adjacency[cn] & ps.g.red_adjacency[cn2]).count());
                ps.queues[c_depth]->back().is_twin = is_twin;
                assert(c_depth == 0 || !is_twin || ps.current_degree[c_depth-1] >= max_degree);
            } else {
                ce->reds_count = new_reds.count();
                ce->max_degree = max_degree;
                ce->reds = reds;
                ce->new_reds = std::move(new_reds);
                ce->nonnew_reds = ps.g.red_adjacency[cn2];
            }

            return true;
        };

        vector<char> is_exceeded(ps.g.num_nodes(), false);

        while (true) {
            if (timeout > 0) {
                if (std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - begin).count() >
                    timeout)
                    return TWW_TIMEOUT;
            }

            // "Return" whenever the queue has been processed, we already exceed the upper bound, or only one vertex remains.
            if ((is_exceeded[depth] || ps.queue_pointers[depth] >= ps.queues[depth]->size() || (depth > 0 && ps.current_degree[depth - 1] >= ub) ||
                 ps.g.available_num == 1) && initialized) {
                assert(depth + 1 >= is_exceeded.size() || !is_exceeded[depth + 1]);

                // Everything has been processed... Note that initialized is also true at this point. We can terminate.
                if (depth == 0)
                    break;

                assert(ps.queue_pointers[depth] <= ps.queues[depth]->size());
                stats.queue -= ps.queues[depth]->size() - ps.queue_pointers[depth];

                ps.is_twin[depth] = 0;
                ++stats.depths[depth];
                --depth;

                // We found a better solution
                if (ps.g.available_num == 1 && ps.current_degree[depth] < ub) {
                    assert(ps.best_results[depth+1] < ub);
                    ub = ps.current_degree[depth];
                    ps.best_result.clear();
                    if (ps.proof_log) {
                        ps.proof_file << "C";
                        for (auto ci = 0; ci <= depth; ++ci)
                            ps.proof_file << " (" << ps.r_map[ps.contractions[ci].first] << ","
                                          << ps.r_map[ps.contractions[ci].second] << ")";
                        ps.proof_file << ":E";
                        ps.proof_file << ":" << ub;
                        ps.proof_file << endl;
                    }

                    // This part is to complete the contraction sequence, in case some nodes are remaining.
                    // The order of contractions do not matter at this point, so we just need to figure out which nodes are remaining.
                    for (auto i = 0; i <= depth; i++) {
                        ps.best_result.emplace_back(ps.trace[i], ps.contractions[i].second);
                    }

                    auto last_node = static_cast<node_t>(ps.g.available.find_first());

                    for (auto cn = ps.g.available.find_next(last_node); cn != ps.g.available.npos; cn = ps.g.available.find_next(cn)) {
                        ps.best_result.emplace_back(cn, last_node);
                    }

                    assert(test_sequence(ps.g_copy, ps.best_result) == ps.current_degree[depth]);

                    if (verbose) {
                        for(auto& cc : ps.best_result)
                            cout << +cc.first << "\t";
                        cout << endl;
                        for(auto& cc : ps.best_result)
                            cout << +cc.second << "\t";
                        cout << endl;
                    }
                    if (heuristic || ub <= lb) {
                        return ub;
                    }
                }

                // Propagate best result backwards.
                node_t c_result =  max(ps.best_results[depth+1], ps.max_degree[depth]);
                ps.best_results[depth] = min(ps.best_results[depth], c_result);

                if (ps.best_results[depth+1] >= ub && ps.current_degree[depth] < ub) {
                    if (VALIDATION_MODE) {
                        // Ensure that any subgraph is present.
                        if (is_exceeded[depth+1]) {
                            bool any_found = false;
                            for(auto csg=ps.all_lower_bound_graphs.rbegin(); csg != ps.all_lower_bound_graphs.rend() && !any_found; ++csg) {
                                if ((*csg)->all_present && (*csg)->not_subset_witness == INVALID_NODE) {
                                    bool all_present = true;
                                    for (auto &cre: (*csg)->red_edges) {
                                        if (!ps.g.red_adjacency[cre.first].test(cre.second)) {
                                            all_present = false;
                                            break;
                                        }
                                    }
                                    assert(all_present);
                                    if (all_present) {
                                        any_found = true;
                                    }
                                } else {
                                    bool all_present = true;
                                    for (auto &cre: (*csg)->red_edges) {
                                        if (!ps.g.red_adjacency[cre.first].test(cre.second)) {
                                            all_present = false;
                                            break;
                                        }
                                    }
                                    cout << "Missed" << endl;
                                }
                            }
                            assert(any_found);
                        }
                    }

                    if (VALIDATION_MODE && (ps.use_cache || ps.use_subgraph_lb)) {
                        vector<node_t> nodes;
                        nodes.reserve(ps.g.available_num);
                        for (node_t cx=0; cx < ps.g.num_nodes(); ++cx) {
                            if (!ps.g.is_deleted(cx))
                                nodes.push_back(cx);
                        }

                        auto result = check_subgraph(ps.g, false,
                                                     false,
                                                     nodes, ub,
                                                     ub - 1, 0, true);

                        assert(result >= ub);
                    }

                    // Store the current subgraph as a lower bound.
                    if (!is_exceeded[depth+1] && ps.use_subgraph_lb && !ps.has_contraction[depth+1]) {
                        dynamic_bitset<> cnb = ps.g.available;
                        vector<node_t> nodes;
                        nodes.reserve(ps.g.available_num);
                        for (auto x = cnb.find_first(); x != cnb.npos; x = cnb.find_next(x)) {
                            nodes.push_back(x);
                        }

                        vector<pair<node_t, node_t>> red_edges;

                        vector<node_t> black_nodes;
                        subgraph_minimize(ps, nodes, cnb, ub, red_edges, depth, black_nodes, false, true);
                        if (VALIDATION_MODE) {
                            auto first_result = check_subgraph(ps.g, ps.use_cache,
                                                   ps.use_order_cache,
                                                   nodes, ub,
                                                   ub - 1, 0, true, &red_edges);
                            assert(first_result >= ub);

                        }

                        sort(red_edges.begin(), red_edges.end());
                        assert(nodes.size() == cnb.count());

                        if (red_edges.empty()) {
                            if (ps.best_results[depth+1] > lb) {
                                lb = ps.best_results[depth+1];
                                if (lb >= ub) {
                                    if (ps.verbose)
                                        cout << "Found subgraph whose lower bound matches the upper bound." << endl;
                                    return ub;
                                }
                            }
                        } else {
                            size_t first_red = SIZE_MAX;
                            size_t first_red_idx = SIZE_MAX;

                            // Check how far we can backtrack, i.e., until one red edge is removed.
                            for (auto cd = depth+1; cd > 0; --cd) {
                                auto &cex = ps.queues[cd - 1]->at(ps.queue_pointers[cd - 1]);
                                for (auto i = 0; i < red_edges.size(); ++i) {
                                    auto &cc = red_edges[i];

                                    if ((cex.n2 == cc.first && cex.reds.test(cc.second)) ||
                                        (cex.n2 == cc.second && cex.reds.test(cc.first))) {
                                        assert(cc.first > cc.second);
                                        assert(first_red == SIZE_MAX);
                                        first_red = i;
                                        first_red_idx = cd-1;
                                        break;
                                    }
                                }

                                // Not even one match
                                if (first_red == SIZE_MAX) {
                                    ++stats.lb_sub;
                                    is_exceeded[cd-1] = true;
                                } else {
                                    break;
                                }
                            }

                            // Check necessary contractions
//                                vector<pair<node_t, node_t>> tracked_reds(red_edges);
//                                vector<pair<node_t, node_t>> necessary_contractions;
//
//                                for (auto cd = depth + 1; cd > 0; --cd) {
//                                    auto &cex = ps.queues[cd - 1]->at(ps.queue_pointers[cd - 1]);
//
//                                    bool found_any = false;
//                                    for (auto i = tracked_reds.size(); i > 0; --i) {
//                                        auto &cc = tracked_reds[i - 1];
//
//                                        if ((cex.n2 == cc.first && cex.reds.test(cc.second)) ||
//                                            (cex.n2 == cc.second && cex.reds.test(cc.first))) {
//                                            found_any = true;
//                                            if ((cex.reds.test(cc.second) && cex.new_reds.test(cc.second)) ||
//                                                cex.reds.test(cc.first) && cex.new_reds.test(cc.first)) {
//                                                swap(tracked_reds.back(), tracked_reds[i - 1]);
//                                                tracked_reds.pop_back();
//                                            } else if (cex.reds.test(cc.second)) {
//                                                cc.first = cex.n;
//                                            } else {
//                                                cc.second = cex.n;
//                                            }
//                                        }
//                                    }
//
//                                    if (found_any)
//                                        necessary_contractions.emplace_back(cex.n, cex.n2);
//                                }
//
//                                assert(tracked_reds.empty());

                            assert(first_red != SIZE_MAX);

                            // TODO: Adapt to nodes that may be deleted
                            vector<pair<node_t, vector<node_t>>> black_twins;
                            for (auto cb: black_nodes) {
                                auto cbnb = ps.g.adjacency[cb] & cnb;
                                vector<node_t> cb_tw;

                                for (auto cn = 0; cn < ps.g.num_nodes(); ++cn) {
                                    if (!ps.g.is_deleted(cn) && !cnb.test(cn)) {
                                        if ((ps.g.adjacency[cn] & cnb) == (ps.g.adjacency[cb] & cnb)) {
                                            cb_tw.push_back(cn);
                                        }
                                    }
                                }

                                if (!cb_tw.empty())
                                    black_twins.emplace_back(cb, std::move(cb_tw));
                            }

                            assert(nodes.size() == cnb.count());
                            if (ps.proof_log) {
                                assert(! ps.r_map.empty());
                                ps.proof_file << "S";
                                for(auto ci=0; ci <= depth; ++ci)
                                    ps.proof_file << " (" << ps.r_map[ps.contractions[ci].first] << "," << ps.r_map[ps.contractions[ci].second] << ")";
                                ps.proof_file << ":";

                                sort(nodes.begin(), nodes.end());
                                for (auto cn: nodes) {
                                    ps.proof_file << ps.r_map[cn];
                                    if (cn != nodes.back())
                                        ps.proof_file << " ";
                                }
                                ps.proof_file << ":";
                                for (auto& cc : red_edges) {
                                    ps.proof_file << "(" << ps.r_map[cc.first] << "," << ps.r_map[cc.second] << ")";
                                    if (cc.first != red_edges.back().first || cc.second != red_edges.back().second)
                                        ps.proof_file << " ";
                                }
                                ps.proof_file << ":" << first_red_idx;
                                ps.proof_file << ":" << ub;
                                ps.proof_file << std::endl;

                                ps.proof_file << "C";
                                for(auto ci=0; ci <= first_red_idx; ++ci)
                                    ps.proof_file << " (" << ps.r_map[ps.contractions[ci].first] << "," << ps.r_map[ps.contractions[ci].second] << ")";
                                ps.proof_file << ":G";
                                ps.proof_file << ":" << ub;
                                ps.proof_file << endl;
                            }

                            new LowerBoundGraph(std::move(cnb), red_edges, first_red, ps, black_twins);
                            ++stats.reasons;
                        }
                    } else if (!is_exceeded[depth+1] && !ps.has_contraction[depth+1] && ps.proof_log) {
                        ps.proof_file << "C";
                        for(auto ci=0; ci <= depth; ++ci)
                            ps.proof_file << " (" << ps.r_map[ps.contractions[ci].first] << "," << ps.r_map[ps.contractions[ci].second] << ")";
                        ps.proof_file << ":E";
                        ps.proof_file << ":" << ub;
                        ps.proof_file << endl;
                    }

                    if (ps.use_cache) {
                        if (USE_CANONICAL_PARTITION) {
                            get_canonical_partition(ps.partitions[depth+1], canonical_tmp, canonical_tmp_working);
                            ps.cache.set(canonical_tmp);
                        } else
                            ps.cache.set(ps.partitions[depth+1]);
                    }
                    if (!ps.gcs[depth].empty()) {
                        ps.g_cache.set(std::move(ps.gcs[depth]));
                        ps.gcs[depth] = "";
                    }
                }

                // Undo contraction
                assert(ps.queue_pointers[depth] < ps.queues[depth]->size());
                auto &ce = ps.queues[depth]->at(ps.queue_pointers[depth]);
                for (auto cn = ce.reds.find_first(); cn != ce.reds.npos; cn = ce.reds.find_next(cn)) {
                    ps.g.remove_red_edge(cn, ce.n2);
                }

                ps.g.restore(ce.n);

                if (VALIDATION_MODE) {
                    // Ensure that the subgraph is really present throughout backtracking.
                    // The case where is_exceed[depth] is true can only happen when backtracking after adding the last subgraph.
                    if (is_exceeded[depth]) {
                        auto csg = ps.all_lower_bound_graphs.back();
                        assert(csg->nodes.is_subset_of(ps.g.available));
                        bool all_present = true;
                        for(auto& cre : csg->red_edges) {
                            if (! ps.g.red_adjacency[cre.first].test(cre.second)) {
                                all_present = false;
                                break;
                            }
                        }
                        assert(all_present);
                    }
                }

                if (ps.use_subgraph_lb && depth > 0) {
                    for (auto cn = ce.reds.find_first(); cn != ce.reds.npos; cn = ce.reds.find_next(cn)) {
                        node_t n1 = max(static_cast<node_t>(cn), ce.n2);
                        node_t n2 = min(static_cast<node_t>(cn), ce.n2);

                        for (auto c_idx = ps.lower_bound_graphs[n1][n2].size(); c_idx > 0; --c_idx) {
                            auto cr = ps.lower_bound_graphs[n1][n2][c_idx-1];
                            cr->update_entry(depth-1);
                        }
                    }

                    for (auto c_idx = ps.lower_bound_by_node[ce.n2].size(); c_idx > 0; --c_idx) {
                        auto cr = ps.lower_bound_by_node[ce.n2][c_idx - 1];
                        assert(cr->n1 == ce.n2 || cr->n2 == ce.n2 || cr->not_subset_witness == ce.n2);
                        cr->update_entry(depth-1);

                        if (cr->all_present && cr->not_subset_witness == INVALID_NODE)
                            is_exceeded[depth] = true;
                    }
                }

                for (auto &cp: ps.lookahead_refs[ce.n]) {
                    assert(cp.first != ce.n && cp.second != ce.n);
                    ps.lookahead_count[cp.first][cp.second]++;
                }

                // If we have to backtrack more than one level, do this in the next iteration.
                if (!is_exceeded[depth]) {
                    assert(ps.queue_pointers[depth] < ps.queues[depth]->size());
                    ++ps.queue_pointers[depth];
                    --stats.queue;
                } else {
                    assert(stats.queue >= ps.queues[depth]->size() - ps.queue_pointers[depth]);
                    assert(ps.queue_pointers[depth] <= ps.queues[depth]->size());
                    stats.queue -= ps.queues[depth]->size() - ps.queue_pointers[depth];
                    ps.queue_pointers[depth] = ps.queues[depth]->size();
                }
                is_exceeded[depth+1] = false;
            } else {
                if (VALIDATION_MODE) {
                    for(char cx : is_exceeded)
                        assert(! cx);
                }
                bool generate = true;
                string gc;

                // Perform contraction
                bool subgraph_found = false;
                if (depth > 0 || initialized) {
                    auto *ce = &ps.queues[depth]->at(ps.queue_pointers[depth]);

                    // Is this in fast mode?
                    if (ps.queues[depth] == &ps.default_queue) {
                        if (ps.is_twin[depth]) {
                            assert(ps.queue_pointers[depth] <= ps.queues[depth]->size());
                            stats.queue -= ps.queues[depth]->size() - ps.queue_pointers[depth];
                            ps.queue_pointers[depth] = ps.queues[depth]->size();
                            continue;
                        }
                        while ((ps.g.is_deleted(ce->n) || ps.g.is_deleted(ce->n2)) &&
                               ps.queue_pointers[depth] < ps.queues[depth]->size()) {
                            assert(ps.queue_pointers[depth] < ps.queues[depth]->size());
                            ++ps.queue_pointers[depth];
                            --stats.queue;
                            if (ps.queue_pointers[depth] < ps.queues[depth]->size())
                                ce = &ps.queues[depth]->at(ps.queue_pointers[depth]);
                        }

                        if (ps.queue_pointers[depth] >= ps.queues[depth]->size()) {
                            continue;
                        } else {
                            ce = &ps.queues[depth]->at(ps.queue_pointers[depth]);
                        }

                        // Do not activate this here, it drains a lot of performance.
//                        for (auto &cp: ps.lookahead_refs[ce->n]) {
//                            assert(cp.first != ce->n && cp.second != ce->n);
//                            ps.lookahead_count[cp.first][cp.second]--;
//                        }

                        bool is_twin = false;

                        ps.trace[depth] = ce->n;

                        auto result = check_contraction(ce->n, ce->n2, is_twin, depth, ce);

//                        for (auto &cp: ps.lookahead_refs[ce->n]) {
//                            ps.lookahead_count[cp.first][cp.second]++;
//                        }

                        if (!result) {
                            assert(ps.queue_pointers[depth] < ps.queues[depth]->size());
                            ++ps.queue_pointers[depth];
                            --stats.queue;
                            continue;
                        }

                        if (is_twin) {
                            ps.is_twin[depth] = is_twin ? 1 : 0;
                        }
                    }

                    if (ce->max_degree >= ub) {
                        assert(ps.queue_pointers[depth] < ps.queues[depth]->size());
                        ++ps.queue_pointers[depth];
                        --stats.queue;
                        ++stats.exceeded;
                        continue;
                    }

                    // Adapt partitions
                    for (node_t cn = 0; cn < static_cast<node_t>(ps.partitions[depth + 1].size()); cn++) {
                        if (ps.partitions[depth][cn] == ce->n) {
                            ps.partitions[depth + 1][cn] = ce->n2;
                        } else {
                            ps.partitions[depth + 1][cn] = ps.partitions[depth][cn];
                        }
                    }

                    if (ps.use_cache) {
                        vector<node_t> &c_part = USE_CANONICAL_PARTITION ? canonical_tmp : ps.partitions[depth + 1];
                        if (USE_CANONICAL_PARTITION) {
                            get_canonical_partition(ps.partitions[depth + 1], canonical_tmp, canonical_tmp_working);
                        }

                        if (ps.cache.get(c_part)) {
                            ++stats.cache_filtered;
                            assert(ps.queue_pointers[depth] < ps.queues[depth]->size());
                            ++ps.queue_pointers[depth];
                            --stats.queue;
                            ps.has_contraction[depth] = true;

                            if (VALIDATION_MODE) {
                                vector<node_t> sub_nodes;
                                ps.g.remove(ce->n);
                                for (auto nx = ce->reds.find_first(); nx != ce->reds.npos; nx = ce->reds.find_next(nx)) {
                                    ps.g.add_red_edge(nx, ce->n2);
                                }

                                sub_nodes.reserve(ps.g.available_num);
                                for(node_t sn=0; sn < ps.g.num_nodes(); ++sn) {
                                    if (! ps.g.is_deleted(sn) && sn != ce->n)
                                        sub_nodes.push_back(sn);
                                }
                                auto sub_result = check_subgraph(ps.g, ps.use_cache, ps.use_order_cache, sub_nodes, ub, ub-1, 0, true);
                                assert(sub_result >= ub);
                                for (auto nx = ce->reds.find_first(); nx != ce->reds.npos; nx = ce->reds.find_next(nx)) {
                                    ps.g.remove_red_edge(nx, ce->n2);
                                }

                                ps.g.restore(ce->n);
                            }

                            if (ps.proof_log) {
                                assert(! ps.r_map.empty());
                                ps.proof_file << "C";
                                for (auto ci = 0; ci < depth; ++ci)
                                    ps.proof_file << " (" << ps.r_map[ps.contractions[ci].first] << ","
                                                  << ps.r_map[ps.contractions[ci].second] << ")";
                                ps.proof_file << " (" << ps.r_map[ce->n] << ","
                                              << ps.r_map[ce->n2] << ")";
                                ps.proof_file << ":C";
                                ps.proof_file << ":" << ub;
                                ps.proof_file << endl;
                            }

                            continue;
                        }
                    }

                    ++stats.calls;
                    if (stats.calls % 100000 == 0) {
                        stats.print(ps, ub, lb, true);
                    }

                    copy(ps.red_counts[depth].begin(), ps.red_counts[depth].end(),
                         ps.red_counts[depth + 1].begin());

                    ps.current_degree[depth] =
                            depth > 0 ? max(ps.current_degree[depth - 1], ce->max_degree) : ce->max_degree;

                    assert(ps.current_degree[depth] < ub);

                    // Contract
                    // Since we have a contraction, the previous node is not a leaf in the search tree.
                    ps.has_contraction[depth] = true;

                    ps.g.remove(ce->n);
                    for (auto &cp: ps.lookahead_refs[ce->n]) {
                        assert(cp.first != ce->n && cp.second != ce->n);
                        ps.lookahead_count[cp.first][cp.second]--;
                    }

                    ps.max_degree[depth] = 0;

                    ps.trace[depth] = ce->n;

                    // The change in degree, without taking into account that the degree may decrease!
                    ps.deg_changes[depth] = 0;

                    // Contract
                    ps.reduced[depth] = ps.g.red_adjacency[ce->n] & ps.g.red_adjacency[ce->n2];
                    ps.contractions[depth] = pair<node_t, node_t>(ce->n, ce->n2);

                    for (auto cn = ce->reds.find_first(); cn != ce->reds.npos; cn = ce->reds.find_next(cn)) {
                        ps.g.add_red_edge(cn, ce->n2);
                        ++ps.deg_changes[depth];
                        if (ce->new_reds.test(cn)) {
                            ++ps.red_counts[depth + 1][cn];
                        }
                    }

                    // Move subgraph watchers to contraction vertex
                    if (ps.use_subgraph_lb) {
                        // First check if any of the newly created red edges matches a watcher.
                        for (auto cn = ce->reds.find_first(); cn != ce->reds.npos; cn = ce->reds.find_next(cn)) {
                            // Check if any subgraph edge occurs
                            node_t n1 = max(ce->n2, static_cast<node_t>(cn));
                            node_t n2 = min(ce->n2, static_cast<node_t>(cn));

                            for (auto idx = ps.lower_bound_graphs[n1][n2].size(); idx > 0; --idx) {
                                auto cr = ps.lower_bound_graphs[n1][n2][idx - 1];

                                // Sanity check that the nodes in the watcher match the pointers
                                assert(cr->n1 == n1 && cr->n2 == n2);

                                // If the nodes are not a subset anymore, nothing to do
                                if (cr->not_subset_witness != INVALID_NODE || cr->all_present) {
                                    continue;
                                }

                                cr->update_entry(depth);

                                if (generate && cr->all_present && cr->not_subset_witness == INVALID_NODE) {
                                    generate = false;
                                    ++stats.lb_sub;
                                    subgraph_found = true;
                                    if (ps.proof_log) {
                                        ps.proof_file << "C";
                                        for (auto ci = 0; ci <= depth; ++ci)
                                            ps.proof_file << " (" << ps.r_map[ps.contractions[ci].first] << ","
                                                          << ps.r_map[ps.contractions[ci].second] << ")";
                                        ps.proof_file << ":G";
                                        ps.proof_file << ":" << ub;
                                        ps.proof_file << endl;
                                    }
                                }
                            }
                        }

                        // TODO: Do we need to update this if generate is already false?
                        // Here we check if any of the red edges involving n can be transferred to n2
                        for (auto c_idx = ps.lower_bound_by_node[ce->n].size(); c_idx > 0; --c_idx) {
                            auto cr = ps.lower_bound_by_node[ce->n][c_idx - 1];

                            assert(cr->not_subset_witness == ce->n || cr->n1 == ce->n || cr->n2 == ce->n);
                            if (cr->not_subset_witness != INVALID_NODE)
                                continue;

                            // If both ends of the red edge map to the same vertex, subgraph cannot be found.
                            cr->update_entry(depth);

                            if (generate && cr->all_present && cr->not_subset_witness == INVALID_NODE) {
                                generate = false;
                                ++stats.lb_sub;
                                subgraph_found = true;

                                if (ps.proof_log) {
                                    assert(!ps.r_map.empty());
                                    ps.proof_file << "C";
                                    for (auto ci = 0; ci <= depth; ++ci)
                                        ps.proof_file << " (" << ps.r_map[ps.contractions[ci].first] << ","
                                                      << ps.r_map[ps.contractions[ci].second] << ")";
                                    ps.proof_file << ":G";
                                    ps.proof_file << ":" << ub;
                                    ps.proof_file << endl;
                                }
                            }
                        }

                        if (VALIDATION_MODE && subgraph_found) {
                            vector<node_t> sub_nodes;
                            sub_nodes.reserve(ps.g.available_num);
                            for(node_t sn=0; sn < ps.g.num_nodes(); ++sn) {
                                if (! ps.g.is_deleted(sn))
                                    sub_nodes.push_back(sn);
                            }
                            auto sub_result = check_subgraph(ps.g, ps.use_cache, ps.use_order_cache, sub_nodes, ub, ub-1, 0, true);
                            assert(sub_result >= ub);
                        }
                    }

                    ps.red_counts[depth + 1][ce->n2] += ps.deg_changes[depth];

                    assert(!ps.g.red_adjacency[ce->n].test(ce->n));
                    assert(!ps.g.red_adjacency[ce->n2].test(ce->n2));

                    // Check for which nodes the red degree actually decreased
                    if (ps.g.red_adjacency[ce->n].test(ce->n2)) {
                        ps.reduced[depth].set(ce->n2);
                    }

                    for (auto cn = ps.reduced[depth].find_first();
                         cn != ps.reduced[depth].npos; cn = ps.reduced[depth].find_next(cn)) {
                        assert(ps.red_counts[depth + 1][cn] > 0);
                        ps.red_counts[depth + 1][cn]--;
                    }

                    for(auto cn=0; cn < ps.g.num_nodes(); ++cn) {
                        if (! ps.g.is_deleted(cn)) {
                            ps.max_degree[depth] = max(ps.max_degree[depth], ps.red_counts[depth + 1][cn]);
                            if (VALIDATION_MODE) {
                                assert(ps.red_counts[depth+1][cn] == ps.g.red_adjacency[cn].count());
                            }
                        }
                    }
                    assert(depth == 0 || ! ce->is_twin || ps.max_degree[depth] <= ps.current_degree[depth-1]);

                    // The default for best result is ub (in case no contraction happens), or the maximum that can be achieved within the graph.
                    if (depth + 1 < ps.best_results.size()) {
                        ps.best_results[depth + 1] = min(ub, ps.g.available_num > 2 ? static_cast<node_t>(ps.g.available_num - 2) : (node_t)0);
                    }

                    // Reordering check for cache
                    // Caching to avoid recalculating known results
                    if (depth > 0 && ps.use_cache && ps.use_order_cache && generate && (ps.red_counts[depth+1][ce->n2] != ps.current_degree[depth] || !ps.reduced[depth].test(ce->n2))) {
                        node_t min_idx = 0;
                        node_t contr_count = ps.red_counts[depth + 1][ce->n2];
                        c_reds.reset();
                        c_reds |= ce->new_reds;

                        for (node_t cd = depth; cd > 0 && min_idx == 0; cd--) {
                            auto c_c1 = ps.contractions[cd - 1].first;
                            auto c_c2 = ps.contractions[cd - 1].second;
                            // The degree of n or n2 was reduced in the step
                            bool c_n1_reduced = ps.reduced[cd - 1].test(ce->n);
                            bool c_n2_reduced = ps.reduced[cd - 1].test(ce->n2);

                            // First case: would a red edge have been created, Second case: will a red edge move from n to n2
                            bool c1_was_red = ps.contractions_edges[ce->n2][ce->n].test(c_c1);
                            bool c2_was_red = ps.contractions_edges[ce->n2][ce->n].test(c_c2);
                            bool c1_n1_present = ps.g.red_adjacency[c_c1].test(ce->n);
                            bool c1_n2_present = ps.g.red_adjacency[c_c1].test(ce->n2);
                            bool c2_n1_present = ps.queues[cd-1]->at(ps.queue_pointers[cd-1]).nonnew_reds.test(ce->n);
                            bool c2_n2_present = ps.queues[cd-1]->at(ps.queue_pointers[cd-1]).nonnew_reds.test(ce->n2);
                            
                            /* In these cases, the red degree would increase by one after reordering:
                             * c1 will be created as a new red edge.
                             * The red degree of n2 reduced in this contraction, hence the decrease will happen later.
                             * The red degree of n reduced, but not n2, hence one extra red edge exists after the contraction.
                             * The red edges between n, n2, c1, c2 are mutually exclusive, leading to one extra red edge after contraction.
                            */
                            if (
                                    (c1_was_red && !c1_n2_present) ||
                                    (c2_was_red && !c2_n2_present) ||
                                    c_n2_reduced || c_n1_reduced ||
                                    (c1_n1_present && !c1_n2_present && ce->n != c_c2) ||
                                    (c2_n1_present && !c2_n2_present && ce->n2 != c_c2) ||
                                    false
                            ) {
                                // If we reordered the current contraction here, we would exceed the bound?
                                ++contr_count;
                                if (contr_count >= ps.current_degree[depth]) {
                                    min_idx = cd;
                                    break;
                                }
                            }

                            // In case the removed vertex would get a red edge, its red degree would increase
                            // TODO: And not reduced?
                            if (c1_was_red) {
                                c_reds.set(c_c1);
                            }

                            // In case we created a red edge to n or n2 at this contraction, the red edge is not counted from here on we have to adjust for that
                            if (c2_was_red && (ps.queues[cd-1]->at(ps.queue_pointers[cd-1]).reds.test(ce->n) || ps.queues[cd-1]->at(ps.queue_pointers[cd-1]).reds.test(ce->n2))) {
                                c_reds.set(c_c2);
                            }

                            // In case that n or n2 are contraction vertices, check the transferred red edges, as they might now be duplicated
                            if (c_c2 == ce->n || c_c2 == ce->n2)
                                c_reds |= (ps.queues[cd-1]->at(ps.queue_pointers[cd-1]).reds - ps.queues[cd-1]->at(ps.queue_pointers[cd-1]).new_reds) & ps.contractions_edges[ce->n2][ce->n];

                            // Check which vertices would exceed the upper bound
                            for (auto cn = c_reds.find_first(); cn != c_reds.npos; cn = c_reds.find_next(cn)) {
                                // First case, any of the newly created red edges connect to a vertex that is already at the limit
                                if (ps.red_counts[cd-1][cn] == ps.current_degree[depth]) {
                                    min_idx = cd;
                                    break;
                                }
                            }
                        }

                        if (min_idx < depth) {
                            if (VALIDATION_MODE) {
                                for(int c_min_idx=depth; c_min_idx >= min_idx; --c_min_idx) {
                                    vector<pair<node_t, node_t>> test_contractions;
                                    test_contractions.reserve(depth);
                                    for (node_t i = 0; i < depth; ++i) {
                                        if (i == c_min_idx)
                                            test_contractions.push_back(ps.contractions[depth]);
                                        test_contractions.push_back(ps.contractions[i]);
                                        if (i >= c_min_idx &&
                                            test_contractions.back().second == ps.contractions[depth].first)
                                            test_contractions.back().second = ps.contractions[depth].second;
                                    }
                                    if (c_min_idx == depth) {
                                        test_contractions.push_back(ps.contractions[depth]);
                                    }
                                    auto test_result = test_sequence(ps.g_copy, test_contractions);

                                    assert(test_result <= ps.current_degree[depth]);
                                }
                            }

                            for (node_t cd = (ps.full_order ? 1 : min_idx); cd < depth; cd++) {
                                for (node_t i = 0; i < ps.g.num_nodes(); i++) {
                                    if (ps.partitions[cd][i] == ps.contractions[depth].first) {
                                        ps.c_old_pat[depth + 1][i] = ps.contractions[depth].second;
                                    } else {
                                        ps.c_old_pat[depth + 1][i] = ps.partitions[cd][i];
                                    }
                                }

                                vector<node_t> &c_part = USE_CANONICAL_PARTITION ? canonical_tmp : ps.c_old_pat[depth + 1];
                                if (USE_CANONICAL_PARTITION) {
                                    get_canonical_partition(ps.c_old_pat[depth + 1], canonical_tmp,
                                                            canonical_tmp_working);
                                }
                                if (ps.cache.get(c_part)) {
                                    bool is_valid = cd >= min_idx;
                                    if (! is_valid) {
                                        vector<pair<node_t, node_t>> test_contractions;
                                        test_contractions.reserve(cd);
                                        for (node_t i = 0; i < depth; ++i) {
                                            if (i == cd)
                                                test_contractions.push_back(ps.contractions[depth]);
                                            test_contractions.push_back(ps.contractions[i]);
                                            if (i >= cd &&
                                                test_contractions.back().second == ps.contractions[depth].first)
                                                test_contractions.back().second = ps.contractions[depth].second;
                                        }
                                        if (cd == depth) {
                                            test_contractions.push_back(ps.contractions[depth]);
                                        }
                                        auto test_result = test_sequence(ps.g_copy, test_contractions);
                                        if (test_result <= ps.current_degree[depth])
                                            is_valid = true;
                                    }

                                    if (is_valid) {
                                        ++stats.order_filtered;
                                        generate = false;

                                        if (ps.proof_log) {
                                            assert(!ps.r_map.empty());
                                            ps.proof_file << "C";
                                            for (auto ci = 0; ci <= depth; ++ci)
                                                ps.proof_file << " (" << ps.r_map[ps.contractions[ci].first] << ","
                                                              << ps.r_map[ps.contractions[ci].second] << ")";
                                            ps.proof_file << ":" << "O";
                                            ps.proof_file << ":" << cd;
                                            ps.proof_file << ":" << ub;
                                            ps.proof_file << endl;
                                        }

                                        break;
                                    }
                                }
                            }
                        }
                    }

                    if (generate) {
                        if (depth > iso_low && depth < iso_high) {
                            while (ps.orbits.size() <= depth)
                                ps.orbits.emplace_back();
                            ps.orbits[depth].resize(ps.g.num_nodes());
                            gc = ps.g.get_canonical(ps.labeling, ps.orbits[depth]);
                            ps.gcs[depth] = gc;
                            if (ps.g_cache.get(gc)) {
                                ++stats.isomorphic_filtered;
                                ++stats.depths[depth];
                                generate = false;
                            }
                        }
                    }

                    ++depth;
                    if (ps.queues[depth] != &ps.default_queue)
                        ps.queues[depth]->clear();
                    if (!generate)
                        ps.has_contraction[depth] = true;

                    ps.queue_pointers[depth] = 0;
                }

                // Create queue of next contractions
                if (generate) {
                    if (depth == 0 && !initialized) {
                        if (ps.orbits.empty())
                            ps.orbits.emplace_back(ps.g.num_nodes());
                        ps.g.get_orbits(ps.orbits[0]);
                    }

                    bool twin = false;
                    ps.previous_contractions[depth].clear();
                    ps.has_contraction[depth] = subgraph_found ? 1 : 0;
                    ps.current_degree[depth] = depth == 0 ? 0 : ps.current_degree[depth-1];

                    if (ps.fast_mode) {
                    } else if (depth > 0 && ps.adaptive_fast_mode && ps.current_degree[depth - 1] == ub -
                                                                                                     1) { // This line switches to fast mode, if we already reached the upper bound, no need to sort the
                        ps.queues[depth] = &ps.default_queue;
                    } else {
                        ps.queues[depth] = ps.queue_entries[depth];
                        ps.queues[depth]->clear();

                        for (node_t n = 0; n < ps.g.num_nodes() && !twin; ++n) {
                            min_degrees[n] = INVALID_NODE;

                            if (!ps.g.is_deleted(n)) {
                                if (depth > 0)
                                    assert(ps.red_counts[depth][n] <= ps.current_degree[depth - 1]);
                                assert(ps.red_counts[depth][n] < ub);

                                for (auto &cp: ps.lookahead_refs[n]) {
                                    assert(cp.first != n && cp.second != n);
                                    ps.lookahead_count[cp.first][cp.second]--;
                                }

                                ps.trace[depth] = n;

                                if (ps.tnb_mode) {
                                    dynamic_bitset<> cnb = ps.g.adjacency[n] | ps.g.red_adjacency[n];
                                    dynamic_bitset<> ctnb = cnb;
                                    for (auto cn2=cnb.find_first(); cn2 != cnb.npos; cn2 = cnb.find_next(cn2))
                                        ctnb |= ps.g.adjacency[cn2] | ps.g.red_adjacency[cn2];
                                    ctnb.reset(n);
                                    for (auto n2=ctnb.find_next(n); n2 != ctnb.npos && !twin; n2 = ctnb.find_next(n2))
                                        check_contraction(n, n2, twin, depth, nullptr);

                                } else {
                                    for (node_t n2 = n + 1; n2 < ps.g.num_nodes() && !twin; ++n2) {
                                        if (!ps.g.is_deleted(n2))
                                            check_contraction(n, n2, twin, depth, nullptr);
                                    }
                                }

                                assert(!twin || ps.queues[depth]->size() == 1);

                                for (auto &cp: ps.lookahead_refs[n]) {
                                    ps.lookahead_count[cp.first][cp.second]++;
                                }
                            }
                        }

                        assert(!twin || ps.queues[depth]->size() == 1);
                        // We eliminate one node per contraction, if the best contraction for a node exceeds what we can reduce, we will exceed in the future.
                        if (!twin && (ps.orbits.size() < depth + 1 ||  ps.orbits[depth].empty())) {
                            sort(min_degrees.begin(), min_degrees.end());
                            for (auto i = 0; i < min_degrees.size() && min_degrees[i] != INVALID_NODE; i++) {
                                if (min_degrees[i] - i >= ub) {
                                    ++stats.lb_future;
                                    ps.queues[depth]->clear();
                                    break;
                                }
                            }
                        }

                        assert(ps.queues[depth] != &ps.default_queue);
                        // If we are already at ub-1 no need to sort, as we cannot improve by more than one
                        if (depth == 0 || ps.current_degree[depth - 1] < ub - 1) {
                            sort(ps.queues[depth]->begin(), ps.queues[depth]->end());
                        }
                        if (!ps.has_contraction[depth])
                            ps.has_contraction[depth] = static_cast<char>(!ps.queues[depth]->empty());
                    }
                    stats.queue += ps.queues[depth]->size();
                    initialized = true;
                }

                if (!generate && ps.queues[depth] == &ps.default_queue)
                    ps.queue_pointers[depth] = ps.queues[depth]->size();
            }
        }

        return ub;
    }
};