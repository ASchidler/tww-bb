//
// Created by asc on 09.11.22.
//

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
#include "sat_encoding.h"
#include "sat_structure.h"
#include <unistd.h>
#include <sys/resource.h>
#include <iomanip>

namespace tww {
    size_t counter;

    template<typename T>
    struct VectorHash {
        std::size_t operator()(const vector<T>& f) const {
            return boost::hash_range(f.begin(), f.end());
        }
    };

    template<typename T>
    struct VectorEqual {
        bool operator()(const vector<T> &lhs, const vector<T> &rhs) const {
            if (lhs.size() != rhs.size())
                return false;
            for (auto i=0; i < lhs.size(); i++) {
                if (lhs[i] != rhs[i])
                    return false;
            }

            return true;
        }
    };

    struct QueueEntry {
        QueueEntry( node_t reds_count,
                    node_t max_degree,
                    node_t n,
                    node_t n2,
                    dynamic_bitset<> reds,
                    dynamic_bitset<> new_reds) : reds_count(reds_count), max_degree(max_degree), n(n), n2(n2), reds(std::move(reds)), new_reds(std::move(new_reds)) {
        }

        node_t reds_count;
        node_t max_degree;
        node_t n;
        node_t n2;
        dynamic_bitset<> reds;
        dynamic_bitset<> new_reds;

        bool operator < (const QueueEntry& rh) const {
            return (max_degree < rh.max_degree ||
                    (max_degree == rh.max_degree && reds_count < rh.reds_count) ||
                    (max_degree == rh.max_degree && reds_count == rh.reds_count && n < rh.n) ||
                    (max_degree == rh.max_degree && reds_count == rh.reds_count && n == rh.n && n2 < rh.n2)
            );
        }
    };

    template <
            class T,
            class Hash = std::hash<T>,
            class KeyEqual = std::equal_to<T>
    >
    class MemoryAwareCache {
    private:
        unordered_map<T, pair<node_t, size_t>, Hash, KeyEqual> _cache;
        size_t c_counter = 0;
        multiset<size_t, std::greater<>> sizes;
        size_t maximum;
    public:
        explicit MemoryAwareCache(size_t maximum) : maximum(maximum) {
            _cache.reserve(maximum);
        }

        size_t get_size() {
            return _cache.size();
        }

        size_t get_buckets() {
            return _cache.bucket_count();
        }

        bool get(T& val, node_t& outp) {
            auto tg = _cache.find(val);

            if (tg == _cache.end())
                return false;

            tg->second.second = c_counter++;
            outp = tg->second.first;
            return true;
        }

        void set(T val, node_t entry) {
            if (_cache.size() >= maximum) { // _cache.size() + 100 >= _cache.max_load_factor() * _cache.bucket_count()) {
//                size_t total = (size_t)sysconf(_SC_AVPHYS_PAGES) * (size_t)sysconf( _SC_PAGESIZE);
//                cout << "Memory: " << total / 1024 / 1024 / 1024 << endl;

                // TODO: This does not decrease the size much, as the space is still reserved, check load factor??
//                if (total / 1024 / 1024 / 1024 <= 1) {
                    size_t target = _cache.size() / 2;
                    sizes.clear();

                    for(auto& ce: _cache) {
                        sizes.insert(ce.second.second);
                        if (sizes.size() > target)
                            sizes.erase(sizes.begin());
                    }

                    size_t c_minimum = *sizes.begin();

                    for(auto it=_cache.begin(); it != _cache.end();) {
                        if (it->second.second <= c_minimum) {
                            auto td = it;
                            ++it;
                            _cache.erase(td);
                        } else {
                            ++it;
                        }
                    }
//                }
            }
            _cache.emplace(std::move(val), pair<node_t, size_t>(entry, c_counter++));
        }
    };

    struct BbParameters {
        explicit BbParameters(Graph& g, node_t sat_depth, bool verbose) :
        g(g), g_cache(0), cache((7000000000 / (sizeof(node_t) * g.num_nodes() + 2 * sizeof(size_t) + sizeof(node_t))) * 2/3),
        max_degrees(g.num_nodes()), red_counts(g.num_nodes()), verbose(verbose), queues(g.num_nodes()),
        previous_contractions(g.num_nodes()), c_partitions(g.num_nodes(), vector<node_t>(g.num_nodes())), c_old_pat(g.num_nodes(), vector<node_t>(g.num_nodes())),
        labeling(g.num_nodes()), orbits(g.num_nodes()), queue_pointers(g.num_nodes()), best_results(g.num_nodes()),
        current_degree(g.num_nodes()), gcs(g.num_nodes()),
//        old_partitions(g.num_nodes(), dynamic_bitset<>(g.num_nodes())),
        deg_changes(g.num_nodes()),
        partitions(g.num_nodes(), vector<node_t>(g.num_nodes())){
            red_counts = vector<vector<node_t>>(g.num_nodes(), vector<node_t>(g.num_nodes()));
            fill(red_counts[0].begin(), red_counts[0].end(), 0);

            for (node_t i=0; i < g.num_nodes(); i++)
                partitions[0][i] = i;

            trace = vector<node_t> (g.num_nodes());
            reduced = vector<dynamic_bitset<>>(g.num_nodes(), dynamic_bitset<>(g.num_nodes()));
            // TODO: Cache could be separated into different depths...

            contractions = vector<pair<node_t, node_t>>(g.num_nodes());

            depths = vector<node_t>(g.num_nodes());

            lookahead_refs.resize(g.num_nodes());
            contractions_edges.resize(g.num_nodes());
            for(node_t n2=0; n2 < g.num_nodes(); n2++) {
                lookahead_count.emplace_back(n2);
                for(node_t n=0; n < n2; n++) {
                    auto reds = g.adjacency[n] ^ g.adjacency[n2];
                    reds.reset(n);
                    reds.reset(n2);
                    lookahead_count[n2][n] = reds.count();
                    for(auto cn=reds.find_first(); cn != reds.npos; cn = reds.find_next(cn)) {
                        lookahead_refs[cn].emplace_back(n2, n);
                    }
                    contractions_edges[n2].emplace_back(std::move(reds));
                }
            }

            if (sat_depth > 0) {
                encoding = make_unique<SatEncoding>(g);
            }

            best_result.reserve(g.num_nodes());
        }
        bool verbose;
        Graph& g;
        vector<vector<node_t>> red_counts;
//        vector<node_t> partition;
        MemoryAwareCache<vector<node_t>, VectorHash<node_t>, VectorEqual<node_t>> cache;
//        unordered_map<vector<node_t>, node_t, VectorHash<node_t>, VectorEqual<node_t>> cache;
        vector<node_t> trace;
        vector<dynamic_bitset<>> reduced;
        vector<node_t> depths;
        vector<pair<node_t, node_t>> contractions;
        vector<vector<dynamic_bitset<>>> contractions_edges;
        vector<vector<node_t>> lookahead_count;
        vector<vector<pair<node_t, node_t>>> lookahead_refs;
        unique_ptr<SatEncoding> encoding;
        MemoryAwareCache<string> g_cache;
        vector<node_t> max_degrees;
        vector<vector<QueueEntry>> queues;
        vector<vector<pair<node_t, int>>> previous_contractions;
        vector<vector<node_t>> c_partitions;
        vector<vector<node_t>> c_old_pat;
        vector<node_t> labeling;
        vector<node_t> orbits;
        vector<size_t> queue_pointers;
        vector<node_t> best_results;
        vector<node_t> current_degree;
        vector<string> gcs;
//        vector<dynamic_bitset<>> old_partitions;
        vector<node_t> deg_changes;
        vector<vector<node_t>> partitions;
        vector<pair<node_t, node_t>> best_result;
    };

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

        vector<size_t> depths;

        void print(BbParameters& params, bool header=true) {
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
                cout                 << setw(field_width) << "Queue Size"
                                     << setw(field_width) << "Twins"
                                     << setw(field_width) << "LB"
                                     << endl ;
            }
            cout << setw(field_width) << queue;
            cout << setw(field_width) << twins;
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

    node_t find_tww_rec(node_t ub, BbParameters& ps, Stats& stats, bool heuristic, node_t iso_low, node_t iso_high, bool verbose) {
        node_t depth = 0;
        bool initialized = false;

        dynamic_bitset<> old_justified(ps.g.num_nodes());
        dynamic_bitset<> reds(ps.g.num_nodes());
        dynamic_bitset<> c_reds(ps.g.num_nodes());
        vector<node_t> min_degrees(ps.g.num_nodes());
        vector<char> node_bools(ps.g.num_nodes(), false);

        for(node_t n=0; n < ps.g.num_nodes(); n++)
            ps.partitions[0][n] = n;

        while(true) {
            // "Return"
            if (ps.queue_pointers[depth] >= ps.queues[depth].size() && initialized) {
                stats.queue -= ps.queues[depth].size();
                if (depth == 0)
                    break;

                ps.cache.set(ps.partitions[depth], max(ps.current_degree[depth], ps.best_results[depth]));
                if (!ps.gcs[depth].empty()) {
                    ps.g_cache.set(std::move(ps.gcs[depth]), max(ps.current_degree[depth], ps.best_results[depth]));
                    ps.gcs[depth] = "";
                }
                --depth;
                assert(ps.queue_pointers[depth] < ps.queues[depth].size());

                auto& ce = ps.queues[depth][ps.queue_pointers[depth]];
                // Undo contraction
                // TODO: Is red, new red better as normal containers?
                for (auto cn = ce.reds.find_first(); cn != ce.reds.npos; cn = ce.reds.find_next(cn)) {
                    ps.g.red_adjacency[ce.n2].reset(cn);
                    ps.g.red_adjacency[cn].reset(ce.n2);
                }

                for (auto &cp: ps.lookahead_refs[ce.n]) {
                    assert(cp.first !=ce. n && cp.second != ce.n);
                    ps.lookahead_count[cp.first][cp.second]++;
                }
                ps.g.restore(ce.n);

                auto overall_result = max(ps.best_results[depth], ps.current_degree[depth]);
                if (overall_result < ub) {
                    ub = overall_result;
                    ps.best_result.clear();
                    fill(node_bools.begin(), node_bools.end(), false);
                    for (auto i = 0; i <= depth; i++) {
                        ps.best_result.emplace_back(ps.trace[i], ps.contractions[i].second);
                        node_bools[ps.trace[i]] = true;
                    }

                    for(node_t cn=0; cn < ps.g.num_nodes()-1; ++cn) {
                        if (!node_bools[cn]) {
                            ps.best_result.emplace_back(cn, ps.g.num_nodes()-1);
                        }
                    }

                    if (verbose) {
                        cout << "Improved bound to " << +ps.current_degree[depth - 1] << endl;
                        for (auto i = 0; i < depth + 2; i++) {
                            cout << +ps.trace[i] << "\t";
                        }
                        cout << endl;
                        for (auto i = 0; i < depth + 2; i++) {
                            cout << +ps.contractions[i].second << "\t";
                        }
                        cout << endl;
                    }
                }
                if (depth > 0)
                    ps.best_results[depth-1] = min(overall_result, ps.best_results[depth-1]);
                ++ps.queue_pointers[depth];
            } else {
                bool generate = true;
                bool orbits_filled = false;
                string gc;

                // Perform contraction
                if (depth > 0 || initialized) {
                    auto &ce = ps.queues[depth][ps.queue_pointers[depth]];

                    if (ce.max_degree >= ub) {
                        ++ps.queue_pointers[depth];
                        ++stats.exceeded;
                        continue;
                    }

                    // Adapt partitions
                    for (node_t cn = 0; cn < ps.partitions[depth+1].size(); cn++) {
                        if (ps.partitions[depth][cn] == ce.n) {
                            ps.partitions[depth+1][cn] = ce.n2;
                        } else {
                            ps.partitions[depth+1][cn] = ps.partitions[depth][cn];
                        }
                    }

                    {
                        node_t c_cb = 0;
                        if (ps.cache.get(ps.partitions[depth+1], c_cb)) {
                            ps.best_results[depth] = min(ps.best_results[depth], c_cb);
                            ++stats.cache_filtered;
                            ++ps.queue_pointers[depth];

                            continue;
                        }
                    }

                    ++stats.calls;
                    if (stats.calls % 100000 == 0)
                        stats.print(ps, true);

                    copy(ps.red_counts[depth].begin(), ps.red_counts[depth].end(),
                         ps.red_counts[depth+1].begin());

                    ps.current_degree[depth] =
                            depth > 0 ? max(ps.current_degree[depth - 1], ce.max_degree) : ce.max_degree;

                    // Contract
                    ps.g.remove(ce.n);
                    for (auto &cp: ps.lookahead_refs[ce.n]) {
                        assert(cp.first != ce.n && cp.second != ce.n);
                        ps.lookahead_count[cp.first][cp.second]--;
                    }

                    ps.trace[depth] = ce.n;

                    // The change in degree, without taking into account that the degree may decrease!
                    ps.deg_changes[depth] = 0;

                    // Contract
                    ps.reduced[depth] = ps.g.red_adjacency[ce.n] & ps.g.red_adjacency[ce.n2];
                    ps.contractions[depth] = pair<node_t, node_t>(ce.n, ce.n2);

                    for (auto cn = ce.reds.find_first(); cn != ce.reds.npos; cn = ce.reds.find_next(cn)) {
                        ps.g.red_adjacency[ce.n2].set(cn);
                        ps.g.red_adjacency[cn].set(ce.n2);
                        ps.deg_changes[depth]++;
                        if (ce.new_reds.test(cn)) {
                            ++ps.red_counts[depth+1][cn];
                        }
                    }
                    ps.red_counts[depth+1][ce.n2] += ps.deg_changes[depth];

                    assert(!ps.g.red_adjacency[ce.n].test(ce.n));
                    assert(!ps.g.red_adjacency[ce.n2].test(ce.n2));

                    // Check for which nodes the red degree actually decreased
                    if (ps.g.red_adjacency[ce.n].test(ce.n2)) {
                        ps.reduced[depth].set(ce.n2);
                    }

                    for (auto cn = ps.reduced[depth].find_first();
                         cn != ps.reduced[depth].npos; cn = ps.reduced[depth].find_next(cn)) {
                        assert(ps.red_counts[depth+1][cn] > 0);
                        ps.red_counts[depth+1][cn]--;
                    }

                    // Reordering check for cache
                    // Caching to avoid recalculating known results
                    if (depth > 0) {
                        node_t min_idx = 0;
                        node_t contr_count = ps.red_counts[depth+1][ce.n2];
                        c_reds.reset();
                        c_reds |= ce.new_reds;

                        for (node_t cd = depth; cd > 0; cd--) {
                            auto c_c = ps.contractions[cd - 1].first;
                            bool c_was_red = ps.contractions_edges[ce.n2][ce.n].test(c_c);
                            bool c_reduced = ps.reduced[cd - 1].test(ce.n) || ps.reduced[cd - 1].test(ce.n2);

                            // Check if contraction n and n2 would exceed the upper bound
                            if (c_reduced || c_was_red) {
                                ++contr_count;
                                if (contr_count >= ub) {
                                    min_idx = cd;
                                    break;
                                }
                            }

                            // Check which vertices would exceed the upper bound
                            if (c_was_red && !c_reduced) {
                                for (auto cn = c_reds.find_first(); cn != c_reds.npos; cn = c_reds.find_next(cn)) {
                                    if (ps.red_counts[cd][cn] == ps.current_degree[depth] &&
                                        ps.red_counts[cd+1][cn] < ps.current_degree[depth]) {
                                        min_idx = cd;
                                        break;
                                    }
                                }
                                if (cd - 1 >= 0 && ps.red_counts[cd - 1][c_c] == ps.current_degree[depth]) {
                                    min_idx = cd;
                                    break;
                                }
                                c_reds.set(c_c);
                            }
                        }

                        if (min_idx < depth) {
                            for (node_t cd = min_idx; cd < depth; cd++) {
//                                copy(ps.partitions[cd+1].begin(), ps.partitions[cd+1].end(), ps.c_old_pat[depth+1].begin());

                                for (node_t i = 0; i < ps.g.num_nodes(); i++) {
                                    if (ps.c_old_pat[depth+1][i] == ps.contractions[depth].first) {
                                        ps.c_old_pat[depth+1][i] = ps.contractions[depth].second;
                                    } else {
                                        ps.c_old_pat[depth+1][i] = ps.partitions[cd+1][i];
                                    }
                                }

                                node_t cache_r;
                                if (ps.cache.get(ps.c_old_pat[depth+1], cache_r)) {
                                    if (max(ps.current_degree[depth], cache_r) >= ub) {
                                        ++stats.order_filtered;
                                        generate = false;
                                        break;
                                    }
                                }
                            }
                        }
                    }

                    if (generate) {
                        if (depth > iso_low && depth < iso_high) {
                            gc = ps.g.get_canonical(ps.labeling, ps.orbits);
                            ps.gcs[depth] = gc;
                            orbits_filled = true;
                            node_t c_x = 0;
                            if (ps.g_cache.get(gc, c_x)) {
                                ++stats.isomorphic_filtered;
                                ++stats.depths[depth];
                                generate = false;
                                ps.best_results[depth] = min(c_x, ps.best_results[depth]);
                            }
                        }

                        // Reached the end
                        if (depth > 0 && depth >= ps.g.num_nodes() - ps.current_degree[depth - 1] - 1) {
                            ps.best_results[depth - 1] = min(ps.best_results[depth - 1], ps.current_degree[depth]);
                            generate = false;
                        } else {
                            ps.best_results[depth] = ub;
                        }
                    }
                    ++depth;
                    ps.queues[depth].clear();
                    ps.queue_pointers[depth] = 0;
                }

                // Create queue of next contractions
                if (generate) {
                    if (depth == 0 && !initialized) {
                        orbits_filled = true;
                        ps.g.get_orbits(ps.orbits);
                    }

                    bool twin = false;
                    for (node_t n = 0; n < ps.g.num_nodes() && !twin; ++n) {
                        min_degrees[n] = INVALID_NODE;
                        if (!ps.g.is_deleted(n)) {
                            ps.previous_contractions[depth].clear();

                            for (auto &cp: ps.lookahead_refs[n]) {
                                assert(cp.first != n && cp.second != n);
                                ps.lookahead_count[cp.first][cp.second]--;
                            }

                            ps.g.remove(n);
                            ps.trace[depth] = n;

                            // TODO: We could actually compute the percentage done out of all possible contractions
                            for (node_t n2 = n + 1; n2 < ps.g.num_nodes() && !twin; ++n2) {
                                if (!ps.g.is_deleted(n2)) {
                                    if (orbits_filled && ps.orbits[n] != n && ps.orbits[n2] != n2) {
                                        ++stats.depths[depth];
                                        stats.orbits++;
                                        continue;
                                    }

                                    // First check if the contraction would exceed the bound
                                    if (ps.lookahead_count[n2][n] >= ub) {
                                        min_degrees[n] = min(min_degrees[n], ps.lookahead_count[n2][n]);
                                        ++stats.exceeded;
                                        continue;
                                    }

                                    reds.reset();
                                    reds |= ps.g.adjacency[n];
                                    reds ^= ps.g.adjacency[n2];
                                    reds |= ps.g.red_adjacency[n];
                                    reds -= ps.g.red_adjacency[n2];

                                    reds.reset(n2);
                                    assert(!reds.test(n));

                                    int deg_change = reds.count();
                                    node_t red_count = deg_change;
                                    if (ps.g.red_adjacency[n].test(n2))
                                        deg_change -= 1;

                                    assert(ps.red_counts[depth][n2] < ub);
                                    if (deg_change + ps.red_counts[depth][n2] >= ub) {
                                        min_degrees[n] = min(min_degrees[n], static_cast<node_t>(deg_change + ps.red_counts[depth][n2]));
                                        ++stats.exceeded;
                                        continue;
                                    }

                                    // Filter equivalent contractions, i.e. if n to n2 leads to the same graph as n to n3 then skip n to n3
                                    bool prior = false;
                                    if (red_count == 1) {
                                        for (auto &cp: ps.previous_contractions[depth]) {
                                            if (cp.first == deg_change &&
                                                (cp.second == INVALID_NODE || reds.test(cp.second))) {
                                                prior = true;
                                                ++stats.quick_isomorphic_filtered;
                                                break;
                                            }
                                        }
                                        if (!prior) {
                                            ps.previous_contractions[depth].emplace_back(deg_change,
                                                                                         red_count == 0 ? INVALID_NODE
                                                                                                        : reds.find_first());
                                        }
                                    }

                                    if (prior) {
                                        continue;
                                    }

                                    // Check if any other node's degree exceeds the upper bound
                                    node_t max_degree = initialized ? ps.current_degree[depth-1] : 0;
                                    if (deg_change + ps.red_counts[depth][n2] > max_degree)
                                        max_degree = deg_change + ps.red_counts[depth][n2];

                                    auto new_reds = reds - ps.g.red_adjacency[n];

                                    twin = deg_change <= 0 && new_reds.count() == 0;
                                    if (twin)
                                        stats.twins++;

                                    bool exceeded = false;
                                    for (auto cn = new_reds.find_first();
                                         cn != new_reds.npos; cn = new_reds.find_next(cn)) {
                                        assert(ps.red_counts[depth][cn] < ub);

                                        if (ps.red_counts[depth][cn] + 1 >= ub) {
                                            exceeded = true;
                                            min_degrees[n] = min(min_degrees[n], static_cast<node_t>(ps.red_counts[depth][cn] + 1));
                                            ++stats.exceeded;
                                            break;
                                        }
                                        if (ps.red_counts[depth][cn] + 1 > max_degree) {
                                            max_degree = ps.red_counts[depth][cn] + 1;
                                        }
                                    }

                                    assert(!twin || !exceeded);

                                    if (exceeded) {
                                        ++stats.depths[depth];
                                        continue;
                                    }
                                    min_degrees[n] = min(min_degrees[n], max_degree);
                                    if (twin)
                                        ps.queues[depth].clear();

                                    ps.queues[depth].emplace_back(new_reds.count(), max_degree, n, n2, reds,
                                                                  std::move(new_reds));
                                }
                            }

                            ps.g.restore(n);
                            for (auto &cp: ps.lookahead_refs[n]) {
                                ps.lookahead_count[cp.first][cp.second]++;
                            }
                        }
                    }
                    assert(!twin || ps.queues[depth].size() == 1);
                    if (! twin) {
                        sort(min_degrees.begin(), min_degrees.end());
                        for(auto i=0; i < min_degrees.size() && min_degrees[i] != INVALID_NODE; i++) {
                            if (min_degrees[i] - i >= ub) {
                                ++stats.lb_future;
                                ps.queues[depth].clear();
                                break;
                            }
                        }
                    }
                    stats.queue += ps.queues[depth].size();
                    sort(ps.queues[depth].begin(), ps.queues[depth].end());
                    initialized = true;
                }
            }
        }

        return ub;
    }

     node_t find_tww(Graph& g, node_t ub, bool heuristic, bool verbose, BbParameters& parameters) {
        auto stats = Stats(g.num_nodes());
//        auto result = find_tww_rec(ub,parameters,stats, heuristic, 14, 25);
         auto result = find_tww_rec(ub,parameters,stats, heuristic, 0, 0, verbose);
        if (verbose)
            cout << "Final result: " << +result << endl;
        stats.print(parameters, true);
        return result;
    }
}
#endif //TWW_BB_TWWBB_H
