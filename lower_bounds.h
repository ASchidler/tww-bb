#include <random>
#include "twwbb2.h"
#include "graph.h"
#include <queue>

#ifndef TWW_BB_LOWER_BOUNDS_H
#define TWW_BB_LOWER_BOUNDS_H
namespace tww {
    class LowerBounds {
    private:
        std::mt19937 device;
        std::uniform_real_distribution<double> real_device;
        vector<double> sampled_values;

        /** Checks if the given subgraph has tww ub by checking all possible contractions */
        static bool
        subgraph_exceeds(const Graph &g, vector<node_t> &nodes, dynamic_bitset<> &cnb, node_t ub, bool stop_rec_call) {
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

                        auto red_nb = ((g.red_adjacency[n1] | g.red_adjacency[n2] |
                                        (g.adjacency[n1] ^ g.adjacency[n2])) & cnb);

                        // The contraction vertex does not exceed the bound?
                        if (red_nb.count() < ub) {
                            // Check other vertices affected by the contraction, their degree might have increased by one.
                            all_exceeded = false;
                            for (auto sub_node: nodes) {
                                if (sub_node != n1 && sub_node != n2 && red_nb.test(sub_node) &&
                                    !g.red_adjacency[n1].test(sub_node) &&
                                    !g.red_adjacency[n2].test(sub_node) &&
                                    (g.red_adjacency[sub_node] & cnb).count() == ub - 1) {
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
                                auto exceeds = subgraph_exceeds(g, nodes, cnb, ub, false);
                                if (!exceeds) {
                                    nodes.push_back(n2);
                                    swap(nodes.back(), nodes[in2]);
                                    cnb.set(n2);

                                    swap(nodes.back(), nodes[in1]);
                                    nodes.pop_back();
                                    cnb.reset(n1);
                                    exceeds = subgraph_exceeds(g, nodes, cnb, ub, true);
                                    if (!exceeds) {
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

        static void subgraph_minimize(const Graph &g, vector<node_t> &nodes, dynamic_bitset<> &cnb, node_t ub) {
            for (auto in = 0; in < nodes.size() && nodes.size() > ub + 2; ++in) {
                auto cn = nodes[in];
                assert(cnb.test(cn));
                cnb.reset(cn);
                swap(nodes.back(), nodes[in]);
                nodes.pop_back();

                if (!subgraph_exceeds(g, nodes, cnb, ub, false)) {
                    nodes.push_back(cn);
                    swap(nodes[in], nodes.back());
                    assert(!cnb.test(cn));
                    cnb.set(cn);
                } else {
                    --in;
                }
            }
            assert(nodes.size() == cnb.count());
        }

        vector<node_t> degrees;

        inline void fill_degrees(const Graph &g) {
            if (degrees.empty()) {
                degrees.resize(g.num_nodes());
                for (node_t n = 0; n < g.num_nodes(); ++n) {
                    degrees[n] = g.adjacency[n].count();
                }
            }
        }

        vector<node_t> min_red_degrees;
        vector<vector<node_t>> min_red_degrees_nb;

        inline void fill_min_red_degrees(const Graph &g) {
            if (min_red_degrees.empty()) {
                min_red_degrees.resize(g.num_nodes(), INVALID_NODE);
                min_red_degrees_nb.resize(g.num_nodes());
                for (node_t n = 0; n < g.num_nodes(); ++n) {
                    dynamic_bitset<> cmin;
                    auto cnb = dynamic_bitset<>(g.num_nodes());
                    for (auto x = g.adjacency[n].find_first();
                         x != g.adjacency[n].npos; x = g.adjacency[n].find_next(x)) {
                        cnb |= g.adjacency[x];
//                        auto diff = g.adjacency[n] ^ g.adjacency[x];
//                        diff.reset(n);
//                        diff.reset(x);
//                        if (diff.count() < min_red_degrees[n]) {
//                            min_red_degrees[n] = static_cast<node_t>(diff.count());
//                            cmin = diff;
//                        }
                    }
                    cnb.reset(n);
                    for (auto x = cnb.find_first();
                         x != cnb.npos; x = cnb.find_next(x)) {
                        auto diff = g.adjacency[n] ^ g.adjacency[x];
                        diff.reset(n);
                        diff.reset(x);
                        if (diff.count() < min_red_degrees[n]) {
                            min_red_degrees[n] = static_cast<node_t>(diff.count());
                            cmin = diff;
                        }
                    }
                    for (auto z = cmin.find_first(); z != cmin.npos; z = cmin.find_next(z))
                        min_red_degrees_nb[z].push_back(n);
                }
            }
        }

        vector<pair<node_t, dynamic_bitset<>>> cliques;
        size_t clique_idx = 0;

        inline void fill_cliques(const Graph &g) {
            fill_degrees(g);
            vector<node_t> degeneracy(g.num_nodes(), 0);
            vector<pair<node_t, node_t>> c_degrees;
            c_degrees.reserve(g.num_nodes());
            dynamic_bitset<> done(g.num_nodes());
            vector<node_t> ordered_nodes;
            ordered_nodes.reserve(g.num_nodes());

            for (node_t n = 0; n < g.num_nodes(); ++n)
                c_degrees.emplace_back(degrees[n], n);

            priority_queue<tuple<node_t, double, node_t>, vector<tuple<node_t, double, node_t>>, greater<>> q;
            sort(c_degrees.begin(), c_degrees.end());

            for (auto &ce: c_degrees) {
                q.emplace(ce.first, 0, ce.second);
                degeneracy[ce.second] = ce.first;
            }

            // Order nodes in order of degeneracy
            size_t c_degeneracy = 0;
            while (!q.empty()) {
                auto element = q.top();
                q.pop();
                if (!done.test(get<2>(element))) {

                    ordered_nodes.emplace_back(get<2>(element));
                    if (get<0>(element) > c_degeneracy)
                        c_degeneracy = get<0>(element);

                    done.set(get<2>(element));
                    degeneracy[get<2>(element)] = c_degeneracy;

                    auto newNb = g.adjacency[get<2>(element)] - done;
                    for (auto nb = newNb.find_first(); nb != dynamic_bitset<>::npos; nb = newNb.find_next(nb)) {
                        degeneracy[nb] -= 1;
                        q.emplace(degeneracy[nb], 0, nb);
                    }
                }
            }
            reverse(ordered_nodes.begin(), ordered_nodes.end());

            cliques.reserve(g.num_nodes());

            // Greedily add to clique
            for (auto n: ordered_nodes) {
                bool found = false;

                for (auto &cc: cliques) {
                    if (g.adjacency[n].test(cc.first) && cc.second.is_subset_of(g.adjacency[n])) {
                        cc.second.set(n);
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    cliques.emplace_back(n, g.num_nodes());
                    cliques.back().second.set(n);
                }
            }

            sort(cliques.begin(), cliques.end(),
                 [](const pair<node_t, dynamic_bitset<>> &e1, pair<node_t, dynamic_bitset<>> &e2) {
                     return e1.second.count() > e2.second.count();
                 });
        }

    public:
        explicit LowerBounds(const Graph &g) : device(1), real_device(0, 1), sampled_values(g.num_nodes()) {

        }

        /** Tries to find a subgraph where the initial contractions all violate a bound */
        static pair<node_t, dynamic_bitset<>> find_lb1_subgraph(const Graph &g) {
            dynamic_bitset<> lb_graph(g.num_nodes());
            lb_graph.flip();

            vector<pair<node_t, node_t>> degrees;
            degrees.reserve(g.num_nodes());
            for (node_t n = 0; n < g.num_nodes(); ++n)
                degrees.emplace_back(g.adjacency[n].count(), n);
            sort(degrees.begin(), degrees.end(), greater<>());
            node_t lb = 0;

            vector<node_t> nodes;
            dynamic_bitset<> cnb(g.num_nodes());
            nodes.reserve(g.num_nodes());
            bool changed = true;
            while (changed) {
                nodes.clear();
                cnb.reset();
                cnb.flip();

                for (auto &cn: degrees) {
                    nodes.push_back(cn.second);
                }

                changed = subgraph_exceeds(g, nodes, cnb, lb + 1, false);
                if (changed) {
                    lb_graph = cnb;
                    ++lb;
                }
            }

            if (lb > 0) {
                nodes.clear();
                for (auto x = lb_graph.find_first(); x != lb_graph.npos; x = lb_graph.find_next(x)) {
                    nodes.push_back(x);
                }
            }

            return {lb, lb_graph};
        }

        /** Constructs a subgraph using weighted random nodes based on the nodes degrees */
        pair<vector<node_t>, dynamic_bitset<>> degree_sampling(const Graph &g, const node_t num_nodes, bool random) {
            double max_value = 0;
            node_t max_node = INVALID_NODE;
            fill_degrees(g);

            for (node_t n = 0; n < g.num_nodes(); ++n) {
                if (random)
                    sampled_values[n] = -log2(real_device(device)) / (double) (degrees[n]);
                else
                    sampled_values[n] = 1.0 / ((double) degrees[n] + real_device(device));

                if (sampled_values[n] > max_value) {
                    max_value = sampled_values[n];
                    max_node = n;
                }
            }
            assert(max_node != INVALID_NODE);

            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            priority_queue<pair<double, node_t>> q;
            vector<char> added(g.num_nodes(), false);

            q.emplace(0, max_node);
            node_t added_nodes = 0;

            while (added_nodes < min(num_nodes, g.num_nodes()) && !q.empty()) {
                auto n = q.top().second;
                q.pop();
                cnb.set(n);
                cnodes.push_back(n);
                ++added_nodes;

                for (auto y = g.adjacency[n].find_first();
                     y != g.adjacency[n].npos; y = g.adjacency[n].find_next(y)) {
                    if (!added[y]) {
                        q.emplace(sampled_values[y], y);
                        added[y] = true;
                    }
                }

                if (!added[n]) {
                    added[n] = true;
                }
            }

            return {cnodes, cnb};
        }

        /** Constructs a subgraph using weighted random nodes based on the red degree of contracting the next with the current vertex */
        pair<vector<node_t>, dynamic_bitset<>> red_sampling(Graph &g, node_t num_nodes, bool random) {
            double max_value = 0;
            node_t max_node = INVALID_NODE;
            fill_degrees(g);

            for (node_t n = 0; n < g.num_nodes(); ++n) {
                if (random)
                    sampled_values[n] = -log2(real_device(device)) / (double) (degrees[n]);
                else
                    sampled_values[n] = 1.0 / (degrees[n] + real_device(device));

                if (sampled_values[n] > max_value) {
                    max_value = sampled_values[n];
                    max_node = n;
                }
            }

            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            priority_queue<pair<double, node_t>> q;
            vector<char> added(g.num_nodes(), false);

            q.emplace(0, max_node);
            node_t added_nodes = 0;

            while (added_nodes < min(num_nodes, g.num_nodes()) && !q.empty()) {
                auto n = q.top().second;
                q.pop();
                if (!added[n]) {
                    cnb.set(n);
                    cnodes.push_back(n);
                    ++added_nodes;
                    added[n] = true;


                    for (auto y = g.adjacency[n].find_first();
                         y != g.adjacency[n].npos; y = g.adjacency[n].find_next(y)) {
                        if (!added[y]) {
                            auto diff = (g.adjacency[y] ^ g.adjacency[n]);
                            diff.reset(n);
                            diff.reset(y);
                            q.emplace(random ? -log2(real_device(device)) / (double) diff.count() : 1.0 /
                                                                                                    ((double) diff.count() +
                                                                                                     real_device(
                                                                                                             device)),
                                      y);
                        }
                    }
                }
            }

            return {cnodes, cnb};
        }

        /** Constructs a subgraph using weighted random nodes based on the minimum red degree */
        pair<vector<node_t>, dynamic_bitset<>> minred_sampling(Graph &g, node_t num_nodes, bool random) {
            fill_min_red_degrees(g);
            double max_value = 0;
            node_t max_node = INVALID_NODE;

            for (node_t n = 0; n < g.num_nodes(); ++n) {
                if (random) {
                    sampled_values[n] = -log2(real_device(device)) / (double) min_red_degrees[n];
                } else {
                    sampled_values[n] = 1.0 / (min_red_degrees[n] + real_device(device));
                }

                if (sampled_values[n] > max_value) {
                    max_value = sampled_values[n];
                    max_node = n;
                }
            }

            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            priority_queue<pair<double, node_t>> q;
            vector<char> added(g.num_nodes(), false);

            q.emplace(0, max_node);
            node_t added_nodes = 0;

            while (added_nodes < min(num_nodes, g.num_nodes()) && !q.empty()) {
                auto n = q.top().second;
                q.pop();
                cnb.set(n);
                cnodes.push_back(n);
                ++added_nodes;

                for (auto y = g.adjacency[n].find_first();
                     y != g.adjacency[n].npos; y = g.adjacency[n].find_next(y)) {
                    if (!added[y]) {
                        q.emplace(random ? sampled_values[y] : 1.0 / (sampled_values[y] + real_device(device)), y);
                        added[y] = true;
                    }
                }

                if (!added[n]) {
                    added[n] = true;
                }
            }

            return {cnodes, cnb};
        }

        /** Constructs a subgraph using weighted random nodes based on the minimum red degree with the nodes already in the subgraph */
        pair<vector<node_t>, dynamic_bitset<>> minred_nb_sampling(Graph &g, node_t num_nodes, bool random) {
            fill_min_red_degrees(g);
            double max_value = 0;
            node_t max_node = INVALID_NODE;
            for (node_t n = 0; n < g.num_nodes(); ++n) {
                sampled_values[n] = random ? -log2(real_device(device)) / (double) min_red_degrees[n] : 1.0 /
                                                                                                        (min_red_degrees[n] +
                                                                                                         real_device(
                                                                                                                 device));

                if (sampled_values[n] > max_value) {
                    max_value = sampled_values[n];
                    max_node = n;
                }
            }

            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            priority_queue<pair<double, node_t>, vector<pair<double, node_t>>, greater<>> q;
            vector<char> added(g.num_nodes(), false);

            q.emplace(0, max_node);
            node_t added_nodes = 0;

            while (added_nodes < min(num_nodes, g.num_nodes()) && !q.empty()) {
                auto n = q.top().second;
                q.pop();
                if (!added[n]) {
                    cnb.set(n);
                    cnodes.push_back(n);
                    ++added_nodes;
                    added[n] = true;

                    for (auto y = g.adjacency[n].find_first();
                         y != g.adjacency[n].npos; y = g.adjacency[n].find_next(y)) {
                        if (!added[y]) {
                            auto intersection = g.adjacency[y] & cnb;
                            auto diff = (g.adjacency[y] ^ g.adjacency[n]) & cnb;
                            diff.reset(n);
                            diff.reset(y);

                            q.emplace(random ? -log2(real_device(device)) / (double) diff.count() : 1.0 /
                                                                                                    ((double) diff.count() +
                                                                                                     real_device(
                                                                                                             device)),
                                      y);
                        }
                    }
                }
            }

            return {cnodes, cnb};
        }


        pair<vector<node_t>, dynamic_bitset<>> maxdegree_nb(Graph &g, node_t num_nodes) {
            fill_degrees(g);

            node_t max_degree = 0;
            node_t max_node = INVALID_NODE;

            for (node_t n = 0; n < g.num_nodes(); ++n) {
                if (max_node == INVALID_NODE || degrees[n] > max_degree ||
                    (degrees[n] == max_degree && real_device(device) < 0.5)) {
                    max_degree = degrees[n];
                    max_node = n;
                }
            }

            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            priority_queue<tuple<node_t, double, node_t>, vector<tuple<node_t, double, node_t>>, greater<>> q;
            vector<char> added(g.num_nodes(), false);

            q.emplace(0, 0, max_node);
            node_t added_nodes = 0;

            while (added_nodes < min(num_nodes, g.num_nodes()) && !q.empty()) {
                auto n = get<2>(q.top());
                q.pop();
                if (!added[n]) {
                    added[n] = true;
                    cnb.set(n);
                    cnodes.push_back(n);
                    ++added_nodes;
                    for (auto y = g.adjacency[n].find_first();
                         y != g.adjacency[n].npos; y = g.adjacency[n].find_next(y)) {
                        if (!added[y]) {
                            q.emplace((g.adjacency[y] & cnb).count(), degrees[y] + real_device(device), y);
                        }
                    }
                }
            }

            return {cnodes, cnb};
        }

        pair<vector<node_t>, dynamic_bitset<>> minred_nb(Graph &g, node_t num_nodes) {
            node_t max_degree = 0;
            node_t max_node = INVALID_NODE;

            for (node_t n = 0; n < g.num_nodes(); ++n) {
                if (degrees[n] == INVALID_NODE || degrees[n] > max_degree ||
                    (degrees[n] == max_degree && real_device(device) < 0.5)) {
                    max_degree = degrees[n];
                    max_node = n;
                }
            }

            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            priority_queue<tuple<node_t, double, node_t>, vector<tuple<node_t, double, node_t>>, greater<>> q;
            vector<char> added(g.num_nodes(), false);

            q.emplace(0, 0, max_node);
            node_t added_nodes = 0;

            while (added_nodes < min(num_nodes, g.num_nodes()) && !q.empty()) {
                auto n = get<2>(q.top());
                q.pop();
                if (!added[n]) {
                    added[n] = true;
                    cnb.set(n);
                    cnodes.push_back(n);
                    ++added_nodes;
                    for (auto y = g.adjacency[n].find_first();
                         y != g.adjacency[n].npos; y = g.adjacency[n].find_next(y)) {
                        if (!added[y]) {
                            auto shared = g.adjacency[y] & cnb;
                            node_t min_deg = INVALID_NODE;
                            for (auto z = shared.find_first(); z != shared.npos; z = shared.find_next(z)) {
                                auto reds = (g.adjacency[y] ^ g.adjacency[z]) & cnb;
                                reds.reset(y);
                                reds.reset(z);
                                min_deg = min(min_deg, static_cast<node_t>(reds.count()));
                            }
                            q.emplace(min_deg, degrees[y] + real_device(device), y);
                        }
                    }
                }
            }

            return {cnodes, cnb};
        }

        pair<vector<node_t>, dynamic_bitset<>> cliques_lb(Graph &g, node_t num_nodes) {
            fill_cliques(g);
            priority_queue<pair<double, node_t>> q;
            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            vector<char> added(g.num_nodes(), false);

            for (auto cn = cliques[clique_idx].second.find_first();
                 cn != cliques[clique_idx].second.npos; cn = cliques[clique_idx].second.find_next(cn))
                q.emplace(0, cn);

            node_t added_nodes = 0;
            cnb |= cliques[clique_idx].second;

            if (clique_idx < cliques.size() - 1)
                ++clique_idx;
            else
                clique_idx = 0;

            while (added_nodes < min(num_nodes, g.num_nodes()) && !q.empty()) {
                auto n = q.top().second;
                q.pop();
                if (!added[n]) {
                    added[n] = true;
                    cnb.set(n);
                    cnodes.push_back(n);
                    ++added_nodes;
                    for (auto y = g.adjacency[n].find_first();
                         y != g.adjacency[n].npos; y = g.adjacency[n].find_next(y)) {
                        if (!added[y]) {
                            q.emplace(abs(0.5 -
                                          (double) (g.adjacency[y] & cnb).count() / (double) g.adjacency[y].count()),
                                      y);
                        }
                    }
                }
            }

            return {cnodes, cnb};
        }

        pair<vector<node_t>, dynamic_bitset<>> peel_degree(Graph &g, node_t num_nodes) {
            fill_degrees(g);
            vector<std::set<node_t>> buckets(g.num_nodes());
            vector<node_t> bucket_map(g.num_nodes());
            vector<char> removed(g.num_nodes(), false);
            node_t c_num_nodes = g.num_nodes();

            for (node_t n = 0; n < g.num_nodes(); ++n) {
                buckets[degrees[n]].insert(n);
                bucket_map[n] = degrees[n];
            }

            node_t c_degree = 0;

            while (c_num_nodes > num_nodes) {
                while (buckets[c_degree].empty()) {
                    ++c_degree;
                }

                auto n = *buckets[c_degree].begin();
                buckets[c_degree].erase(n);
                removed[n] = true;
                --c_num_nodes;

                for (auto on = g.adjacency[n].find_first();
                     on != g.adjacency[n].npos; on = g.adjacency[n].find_next(on)) {
                    if (!removed[on]) {
                        buckets[bucket_map[on]].erase(on);
                        --bucket_map[on];
                        buckets[bucket_map[on]].insert(on);
                        if (bucket_map[on] < c_degree)
                            --c_degree;
                    }
                }
            }

            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            for (node_t n = 0; n < g.num_nodes(); ++n) {
                if (!removed[n]) {
                    cnb.set(n);
                    cnodes.push_back(n);
                }
            }

            return {cnodes, cnb};
        }

        pair<vector<node_t>, dynamic_bitset<>> peel_minred(Graph &g, node_t num_nodes) {
            fill_min_red_degrees(g);
            vector<std::set<node_t>> buckets(g.num_nodes());
            vector<node_t> bucket_map(g.num_nodes());
            vector<char> removed(g.num_nodes(), false);
            node_t c_num_nodes = g.num_nodes();

            for (node_t n = 0; n < g.num_nodes(); ++n) {
                buckets[min_red_degrees[n]].insert(n);
                bucket_map[n] = min_red_degrees[n];
            }

            node_t c_degree = 0;

            while (c_num_nodes > num_nodes) {
                while (buckets[c_degree].empty()) {
                    ++c_degree;
                }

                auto n = *buckets[c_degree].begin();
                buckets[c_degree].erase(n);
                removed[n] = true;
                --c_num_nodes;

                for (auto on: min_red_degrees_nb[n]) {
                    if (!removed[on]) {
                        buckets[bucket_map[on]].erase(on);
                        --bucket_map[on];
                        buckets[bucket_map[on]].insert(on);
                        if (bucket_map[on] < c_degree)
                            --c_degree;
                    }
                }
            }

            vector<node_t> cnodes;
            dynamic_bitset<> cnb(g.num_nodes());
            for (node_t n = 0; n < g.num_nodes(); ++n) {
                if (!removed[n]) {
                    cnb.set(n);
                    cnodes.push_back(n);
                }
            }

            return {cnodes, cnb};
        }
    };

//
//pair<vector<node_t>, dynamic_bitset<>> peel_red(Graph& g, node_t num_nodes, node_t best_lb) {
//    bool ran = false;
//    bool all_exceeded = true;
//    node_t c_num_nodes = g.num_nodes();
//    dynamic_bitset<> cnb;
//    cnb.flip();
//
//    // Minimum size required to have red degree ub
//    if (c_num_nodes >= best_lb + 2 && ) {
//        for (auto in1 = 0; in1 < nodes.size() && all_exceeded; ++in1) {
//            auto n1 = nodes[in1];
//            assert(n1 != INVALID_NODE);
//            assert(cnb.test(n1));
//            cnb.reset(n1);
//
//            for (auto in2 = in1 + 1; in2 < nodes.size() && all_exceeded; ++in2) {
//                ran = true;
//                auto n2 = nodes[in2];
//                assert(n2 != INVALID_NODE);
//                assert(n1 != n2);
//                assert(cnb.test(n2));
//                cnb.reset(n2);
//
//                auto red_nb = ((g.red_adjacency[n1] | g.red_adjacency[n2] |
//                                (g.adjacency[n1] ^ g.adjacency[n2])) & cnb);
//
//                // The contraction vertex does not exceed the bound?
//                if (red_nb.count() < ub) {
//                    // Check other vertices affected by the contraction, their degree might have increased by one.
//                    all_exceeded = false;
//                    for (auto sub_node: nodes) {
//                        if (sub_node != n1 && sub_node != n2 && red_nb.test(sub_node) &&
//                            !g.red_adjacency[n1].test(sub_node) &&
//                            !g.red_adjacency[n2].test(sub_node) &&
//                            (g.red_adjacency[sub_node] & cnb).count() == ub - 1) {
//                            all_exceeded = true;
//                            break;
//                        }
//                    }
//
//                    // If the contraction does not exceed the lower bound, remove n2 and check if the lower bound holds then.
//                    if (!all_exceeded && !stop_rec_call) {
//                        // Remove n2 and try if it exceeds without n2
//                        swap(nodes.back(), nodes[in2]);
//                        nodes.pop_back();
//                        cnb.set(n1);
//
//                        assert(cnb.count() == nodes.size());
//                        auto exceeds = subgraph_exceeds(g, nodes, cnb, ub, false);
//                        if (! exceeds) {
//                            nodes.push_back(n2);
//                            swap(nodes.back(), nodes[in2]);
//                            cnb.set(n2);
//
//                            swap(nodes.back(), nodes[in1]);
//                            nodes.pop_back();
//                            cnb.reset(n1);
//                            exceeds = subgraph_exceeds(g, nodes, cnb, ub, true);
//                            if (! exceeds) {
//                                nodes.push_back(n1);
//                                swap(nodes.back(), nodes[in1]);
//                                cnb.set(n1);
//                            }
//                        }
//
//                        assert(cnb.count() == nodes.size());
//
//                        return exceeds;
//                    }
//                    if (!all_exceeded) {
//                        cnb.set(n2);
//                        break;
//                    }
//                }
//
//                cnb.set(n2);
//            }
//
//            cnb.set(n1);
//        }
//    }
//
//    return ran && all_exceeded;
//}
};
#endif //TWW_BB_LOWER_BOUNDS_H
