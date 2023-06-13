//
// Created by asc on 26.11.22.
//

#ifndef TWW_BB_SAT_ENCODING_H
#define TWW_BB_SAT_ENCODING_H

#include "cadical/cadical.hpp"
#include "cadical/signal.hpp"
#include "graph.h"
#include "tww.h"
#include "tools.h"
#include <queue>

namespace tww {
    class OutputLearner : public CaDiCaL::Learner {
    private:
        unordered_map<int, string> mapping;

    public:
        OutputLearner() : CaDiCaL::Learner() {

        }

        bool learning (int size) override {
//            if (size > 20)
//                return false;
            cout << size << " ";
            return true;
        }
        void learn (int lit) override {
            if (lit != 0) {
                auto out = mapping.find(abs(lit));
                if (out != mapping.end()) {
                    if (lit < 0)
                        cout << "-";

                    cout << out->second << " ";
                } else {
                    cout << lit << " ";
                }
            } else {
                cout << endl;
            }
        }

        void add_mapping(int lit, const string& name) {
            mapping.emplace(lit, name);
        }

        void add_vars (const string prefix, vector<vector<int>>& vars) {
            for(auto i1=0; i1 < vars.size(); i1++) {
                for(auto i2=0; i2 < vars[i1].size(); i2++) {
                    if (vars[i1][i2] != 0) {
                        std::stringstream fmt;
                        fmt << prefix << "_" << +i1 << "_" << +i2;
                        add_mapping(vars[i1][i2], fmt.str());
                    }
                }
            }
        }

        void add_vars3(const string prefix, vector<vector<vector<int>>>& vars) {
            for(auto i1=0; i1 < vars.size(); i1++) {
                for(auto i2=0; i2 < vars[i1].size(); i2++) {
                    for(auto i3=0; i3 < vars[i2].size(); i3++) {
                        if (vars[i1][i2][i3] != 0) {
                            std::stringstream fmt;
                            fmt << prefix << "_" << +i1 << "_" << +i2;
                            add_mapping(vars[i1][i2][i3], fmt.str());
                        }
                    }
                }
            }
        }
    };

    class SatEncoding {
        CaDiCaL::Solver* solver = nullptr;
        Graph g;
        vector<vector<vector<int>>> red;
        vector<vector<int>> ord;
        vector<vector<int>> merge;
        vector<vector<int>> real_merge;
        vector<vector<int>> merged_edge;
        vector<vector<int>> card_vars;
        vector<vector<vector<int>>> counters;
        vector<vector<int>> ord_vars;
        vector<vector<int>> red_count;
        vector<vector<int>> merge_exists;
        vector<int> tmp_vars;
        int cvars = 0;
        size_t cclauses = 0;
        node_t cub = INVALID_NODE;
        vector<vector<vector<node_t>>> differences;
        vector<vector<vector<pair<node_t, node_t>>>> edge_sources;

        std::shared_ptr<vector<int>>
        createTotalizer(const vector<int> &literals, const node_t ub) {
            queue<std::unique_ptr<vector<int>>> currentVars;
            for (const auto &clit: literals) {
                currentVars.push(std::move(std::make_unique<vector<int>>()));
                currentVars.back()->push_back(clit);
            }

            while (currentVars.size() > 1) {
                auto l = std::move(currentVars.front());
                currentVars.pop();
                auto r = std::move(currentVars.front());
                currentVars.pop();

                auto minub = ub+1 < l->size() + r->size() ? ub + 1 : static_cast<node_t>(l->size() + r->size());

                auto newVars = make_unique<vector<int>>();
                newVars->reserve(minub);

                for (unsigned int i = 0; i < minub; i++) {
                    newVars->push_back(++cvars);
                }
                solver->reserve(cvars);

                auto minub2 = minub < r->size() ? minub : r->size();
                for (unsigned int j = 0; j < minub2; ++j) {
                    solver->add(-r->at(j));
                    solver->add(newVars->at(j));
                    solver->add(0);
                    ++cclauses;
                }

                minub2 = minub < l->size() ? minub : l->size();
                for (int i = 0; i < minub2; ++i) {
                    solver->add(-l->at(i));
                    solver->add(newVars->at(i));
                    solver->add(0);
                    ++cclauses;
                }

                for (int i = 1; i <= minub2; ++i) {
                    auto minj = minub - i < r->size() ? minub - i : r->size();
                    for (int j = 1; j <= minj; ++j) {
                        solver->add(-l->at(i - 1));
                        solver->add(-r->at(j - 1));
                        solver->add(newVars->at(i + j - 1));
                        solver->add(0);
                        ++cclauses;
                    }
                }

                currentVars.push(std::move(newVars));
            }

            return {std::move(currentVars.front())};
        }

        inline void init_vars(node_t steps, node_t d) {
            for(node_t t=0; t < steps-1; t++) {
                for (node_t n = 0; n < g.num_nodes(); n++) {
                    merge[t][n] = ++cvars;
                    ord[t][n] = ++ cvars;
                    red_count[t][n] = ++cvars;
                    merge_exists[t][n] = ++cvars;
                    if (t > 0) {
                        merged_edge[t][n] = ++cvars;
                    }

                    for(node_t n2 = n+1; n2 < g.num_nodes(); n2++) {
                        red[t][n][n2] = ++cvars;
                    }

                    for (node_t x=1; x <= d; x++) {
                        counters[t][n][x] = ++cvars;
                    }
                }
            }
            for(node_t n1=0; n1 < g.num_nodes(); n1++) {
                for (node_t n2=n1+1; n2 < g.num_nodes(); n2++) {
                    real_merge[n1][n2] = ++cvars;
                }
            }
            solver->reserve(cvars);
        }

        vector<int> encode_amo_seq(const vector<int>& vars) {
            vector<int> new_vars(vars.size());
            if (vars.empty())
                return new_vars;

            new_vars[0] = vars[0];
            for(auto x=1; x < vars.size(); x++)
                new_vars[x] = ++cvars;

            solver->reserve(cvars);

            for (auto x=1; x < vars.size(); x++) {
                solver->add(-new_vars[x-1]);
                solver->add(-vars[x]);
                solver->add(0);
                ++cclauses;

                solver->add(-vars[x]);
                solver->add(new_vars[x]);
                solver->add(0);
                ++cclauses;

                solver->add(-new_vars[x-1]);
                solver->add(new_vars[x]);
                solver->add(0);
                ++cclauses;
            }

            return new_vars;
        }

        inline int tred(node_t t, node_t n, node_t n2) {
            return (n < n2 ? red[t][n][n2] : red[t][n2][n]);
        }

        inline void encode_order(node_t steps) {
            tmp_vars.resize(g.num_nodes());
            for(node_t t=0; t < steps-1; t++) {
                if (t < g.num_nodes()-1) {
                    solver->add(-ord[t][g.num_nodes()-1]);
                    solver->add(0);
                    ++cclauses;
                }

                for(node_t n=0; n < g.num_nodes(); n++) {
                    solver->add(ord[t][n]);
                    tmp_vars[n] = ord[t][n];
                }
                solver->add(0);
                ++cclauses;

                encode_amo_seq(tmp_vars);
            }

            tmp_vars.resize(steps - 1);
            for(node_t n=0; n < g.num_nodes(); n++) {
                for(node_t t=0; t < steps-1; t++) {
                    tmp_vars[t] = ord[t][n];
                }
                auto cv = encode_amo_seq(tmp_vars);
                for(auto x=0; x < cv.size(); x++) {
                    ord_vars[n][x] = cv[x];
                }

                for(node_t t=0; t < steps-1; t++) {
                    for(node_t t2=0; t2 <= t; t2++) {
                        solver->add(ord[t2][n]);
                    }
                    solver->add(-ord_vars[n][t]);
                    solver->add(0);
                    ++cclauses;
                }
            }
        };

        inline void encode_merge(node_t steps) {
            tmp_vars.resize(g.num_nodes());
            for(node_t t=0; t < steps-1; t++) {
                for(node_t n=0; n < g.num_nodes(); n++) {
                    tmp_vars[n] = merge[t][n];
                    solver->add(merge[t][n]);
                }
                solver->add(0);
                ++cclauses;
                encode_amo_seq(tmp_vars);

                for(node_t n=0; n < g.num_nodes(); n++) {
                    // Do not merge with yourself
                    solver->add(-ord_vars[n][t]);
                    solver->add(-merge[t][n]);
                    solver->add(0);
                    ++cclauses;

                    // Lex ordering
                    solver->add(-merge[t][n]);
                    for (node_t n2=0; n2 < n; n2++) {
                        solver->add(ord[t][n2]);
                    }
                    solver->add(0);
                    ++cclauses;

                    for(node_t n2=n+1; n2 < g.num_nodes(); n2++) {
                        solver->add(-ord[t][n]);
                        solver->add(-merge[t][n2]);
                        solver->add(real_merge[n][n2]);
                        solver->add(0);
                        ++cclauses;
                    }
                }

                if (t > 0) {
                    for (node_t n=0; n < g.num_nodes(); n++) {
                        for (node_t n2=0; n2 < g.num_nodes(); n2++) {
                            if (n == n2)
                                continue;

                            assert(merged_edge[t][n2] != 0);
                            assert(tred(t-1, n2, n) != 0);
                            assert(tred(t-1, n, n2) != 0);

                            solver->add(-ord[t][n]);
                            solver->add(-tred(t-1, n, n2));
                            solver->add(merged_edge[t][n2]);
                            solver->add(0);
                            ++cclauses;

                            solver->add(-ord[t][n]);
                            solver->add(tred(t-1, n, n2));
                            solver->add(-merged_edge[t][n2]);
                            solver->add(0);
                            ++cclauses;
                        }
                    }
                }
            }

            for(node_t n=0; n < g.num_nodes()-2; n++) {
                solver->add(ord_vars[n][steps-2]);
                solver->add(real_merge[n][g.num_nodes()-1]);
                solver->add(0);
                ++cclauses;

                tmp_vars.resize(g.num_nodes()-n-1);
                for(node_t n2=n+1; n2<g.num_nodes(); n2++) {
                    tmp_vars[n2-n-1] = real_merge[n][n2];
                }
                encode_amo_seq(tmp_vars);
            }
        }

        inline void encode_red(node_t d, node_t steps) {
            if (differences.empty()) {
                differences = vector<vector<vector<node_t>>>(g.num_nodes(), vector<vector<node_t>>(g.num_nodes()));
                edge_sources = vector<vector<vector<pair<node_t, node_t>>>>(g.num_nodes(),
                                                                            vector<vector<pair<node_t, node_t>>>(
                                                                                    g.num_nodes()));

                for (node_t n = 0; n < g.num_nodes(); n++) {
                    for (node_t n2 = n + 1; n2 < g.num_nodes(); n2++) {
                        auto diff = g.adjacency[n] ^ g.adjacency[n2];
                        diff.reset(n);
                        diff.reset(n2);

                        differences[n][n2].reserve(diff.count());
                        for (auto nx = diff.find_first(); nx != diff.npos; nx = diff.find_next(nx)) {
                            auto n3 = static_cast<node_t>(nx);
                            differences[n][n2].push_back(n3);
                            edge_sources[min(n, n3)][max(n, n3)].emplace_back(n, n2);
                            edge_sources[min(n2, n3)][max(n2, n3)].emplace_back(n, n2);
                        }
                    }
                }
            }

            for(node_t n=0; n < g.num_nodes(); n++) {
                for(node_t t=0; t < steps-1; t++) {
                    for(node_t n2=n+1; n2 < g.num_nodes(); n2++) {
                        // Prohibit initial contractions that immediately violate d
                        auto& diff = differences[n][n2];

                        // Create new edges
                        for (auto n3: diff) {
                            if (t > 0) {
                                solver->add(-ord_vars[n][t]);
                                solver->add(ord_vars[n2][t]);
                                solver->add(ord_vars[n3][t]);
                            } else {
                                solver->add(-ord[t][n]);
                            }

                            solver->add(-real_merge[n][n2]);
                            solver->add(tred(t, n2, n3));
                            solver->add(0);
                            ++cclauses;
                        }

                        // Ensure red edges are created for a reason
                        for(auto cn : {n , n2}) {
                            solver->add(-tred(t, n, n2));
                            solver->add(-merge[t][cn]);
                            for (auto &cp : edge_sources[min(n, n2)][max(n, n2)]) {
                                if (cp.second == cn)
                                    solver->add(ord[t][cp.first]);
                            }

                            if (t > 0) {
                                solver->add(merged_edge[t][cn == n ? n2 : n]);
                                solver->add(tred(t-1, n, n2));
                            }
                            solver->add(0);
                            ++cclauses;
                        }

                        if (t > 0) {
                            solver->add(tred(t-1, n, n2));
                        }
                        solver->add(-tred(t, n, n2));
                        solver->add(merge[t][n2]);
                        solver->add(merge[t][n]);
                        solver->add(0);
                        ++cclauses;
                    }

                    // Maintain all other red edges
                    if (t > 0) {
                        for(node_t n2=0; n2 < g.num_nodes(); n2++) {
                            if (n == n2)
                                continue;

                            if (n < n2) {
                                solver->add(ord[t][n]);
                                solver->add(ord[t][n2]);
                                solver->add(-tred(t-1, n, n2));
                                solver->add(tred(t, n, n2));
                                solver->add(0);
                                ++cclauses;

                                solver->add(-tred(t, n, n2));
                                solver->add(-ord[t][n2]);
                                solver->add(0);
                                ++cclauses;

                                solver->add(-tred(t, n, n2));
                                solver->add(-ord[t][n]);
                                solver->add(0);
                                ++cclauses;
                            }

                            solver->add(-merge[t][n]);
                            solver->add(-merged_edge[t][n2]);
                            solver->add(tred(t, n, n2));
                            solver->add(0);
                            ++cclauses;
                        }
                    }
                }
            }
        }

        inline void encode_vertex_counters(node_t d, node_t steps) {
            for (node_t t=0; t < steps-1; t++) {
                for (node_t n=0; n < g.num_nodes(); n++) {
                    // Move merge targets
                    for(node_t n2=0; n2 < g.num_nodes(); n2++) {
                        if (n != n2) {
                            solver->add(-merge[t][n2]);
                            solver->add(-tred(t, n, n2));
                            solver->add(red_count[t][n]);
                            solver->add(0);
                            ++cclauses;
                        }
                    }

                    // Transfer from card constraint
                    for (node_t x=1; x <= d; x++) {
                        assert(counters[t][n][x] != 0);
                        assert(card_vars[t][x-1] != 0);
                        assert(merge[t][n]!=0);
                        solver->add(-merge[t][n]);
                        solver->add(-card_vars[t][x-1]);
                        solver->add(counters[t][n][x]);
                        solver->add(0);
                        ++cclauses;
                    }
                }
            }

            if (d == 0)
                return;

            // Handle other counters
            for (node_t t=0; t < steps-1; t++) {
                for (node_t n=0; n < g.num_nodes(); n++) {
                    auto src = merged_edge[t][n];
                    auto tgt = merge_exists[t][n];

                    if (t==0) {
                        solver->add(merge[t][n]);
                        solver->add(-red_count[t][n]);
                        solver->add(counters[t][n][1]);
                        solver->add(0);
                        ++cclauses;
                    } else {
                        auto prefix  = [&] () {
                            solver->add(merge[t][n]);
                            solver->add(src);
                            solver->add(tgt);
                            solver->add(-red_count[t][n]);
                        };

                        // Increase counters
                        prefix();
                        solver->add(counters[t][n][1]);
                        solver->add(0);
                        ++cclauses;

                        for(node_t x=1; x < d; x++) {
                            prefix();
                            solver->add(-counters[t-1][n][x]);
                            solver->add(counters[t][n][x+1]);
                            solver->add(0);
                            ++cclauses;
                        }
                        //Exceeding
                        prefix();
                        solver->add(-counters[t-1][n][d]);
                        solver->add(0);
                        ++cclauses;

                        // Maintain
                        for(node_t x=1; x < d+1; x++) {
                            solver->add(merge[t][n]);
                            solver->add(-counters[t-1][n][x]);
                            solver->add(src);
                            solver->add(counters[t][n][x]);
                            solver->add(0);
                            ++cclauses;

                            solver->add(merge[t][n]);
                            solver->add(-counters[t-1][n][x]);
                            solver->add(tgt);
                            solver->add(counters[t][n][x]);
                            solver->add(0);
                            ++cclauses;
                        }

                        // Ensure counter never decreases by more than 1
                        for (node_t x=2; x < d+1; x++) {
                            solver->add(-counters[t-1][n][x]);
                            solver->add(counters[t][n][x-1]);
                            solver->add(0);
                            ++cclauses;
                        }
                    }

                    // Encode aux var
                    for(node_t n2=0; n2 < g.num_nodes(); n2++) {
                        if (n != n2 && t > 0) {
                            solver->add(-merge[t][n2]);
                            solver->add(-tred(t-1, n, n2));
                            solver->add(tgt);
                            solver->add(0);
                            ++cclauses;

                            solver->add(-merge[t][n2]);
                            solver->add(tred(t-1, n, n2));
                            solver->add(-tgt);
                            solver->add(0);
                            ++cclauses;
                        }
                    }
                }
            }
        }

        inline void encode_counters(node_t d, node_t steps) {
            tmp_vars.resize(g.num_nodes());
            for(node_t t=0; t < steps-1; t++) {
                for(node_t n=0; n < g.num_nodes(); n++) {
                    tmp_vars[n] = red_count[t][n];
                }
                auto vars = createTotalizer(tmp_vars, d);
                solver->add(-vars->at(d));
                solver->add(0);
                ++cclauses;
                for(auto n=0; n < vars->size(); n++) {
                    card_vars[t][n] = vars->at(n);
                }
            }
        }

        inline void encode_sb(node_t d, node_t steps) {
            vector<vector<int>> critical(g.num_nodes(), vector<int>(g.num_nodes()));

            for(node_t t=1; t < steps-1; t++) {
                for (node_t n = 0; n < g.num_nodes(); n++) {
                    critical[t][n] = ++cvars;
                }
            }

            for(node_t t=2; t < steps-1; t++) {
                for (node_t n = 0; n < g.num_nodes(); n++) {
                    solver->add(-critical[t][n]);
                    solver->add(counters[t][n][d]);
                    solver->add(0);
                    ++cclauses;

                    solver->add(-critical[t][n]);
                    solver->add(-counters[t - 1][n][d]);
                    solver->add(0);
                    ++cclauses;

                    solver->add(-critical[t][n]);
                    solver->add(counters[t-2][n][d]);
                    solver->add(0);
                    ++cclauses;

                    solver->add(-counters[t-2][n][d]);
                    solver->add(counters[t-1][n][d]);
                    solver->add(-counters[t][n][d]);
                    solver->add(critical[t][n]);
                    solver->add(0);
                    ++cclauses;
                }
            }

            for(node_t t=1; t < steps-1; ++t) {
                for (node_t n = 0; n < g.num_nodes(); ++n) {
                    for(node_t n2=0; n2 < n; ++n2) {
                        solver->add(-ord[t][n2]);
                        solver->add(-ord[t-1][n]);
                        if (t > 1) {
                            for (node_t n3 = 0; n3 < g.num_nodes(); ++n3) {
                                solver->add(critical[t - 1][n3]);
                            }
                        } else {
                            for (node_t n3 = 0; n3 < g.num_nodes(); ++n3) {
                                solver->add(counters[t][n3][d]);
                            }
                        }
                        solver->add(card_vars[t][d]);
                        solver->add(0);
                        ++cclauses;
                    }
                }
            }
        }

        inline void static_hints(node_t d, node_t steps) {
            for(node_t n=0; n < g.num_nodes(); n++) {
                for (node_t n2 = n + 1; n2 < g.num_nodes(); n2++) {
                    auto &diff = differences[n][n2];
                    if (diff.size() > d+1) {
                        for (node_t t = 0; t < steps - 1; t++) {
                            // Prohibit initial contractions that immediately violate d
                            if (t + 1 < diff.size() - d) {
                                solver->add(-ord[t][n]);
                                solver->add(-real_merge[n][n2]);
                                solver->add(0);
                                ++cclauses;
                            }
                        }
                    }
                }
            }
        }

    public:
        explicit SatEncoding(Graph& g) : g(g), tmp_vars(g.num_nodes()) {
            merge = vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes()));
            red = vector<vector<vector<int>>>(g.num_nodes(), vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes())));
            ord = vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes()));
            ord_vars = vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes()));
            real_merge = vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes()));
            card_vars = vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes()));
            merged_edge = vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes()));
            counters = vector<vector<vector<int>>>(g.num_nodes(), vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes())));
            red_count = vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes()));
            merge_exists = vector<vector<int>>(g.num_nodes(), vector<int>(g.num_nodes()));

            g = g.copy(false);
        }

        pair<node_t, vector<pair<node_t, node_t>>> run(node_t ub, const vector<pair<node_t, node_t>>& contractions, const node_t step, const bool sb) {
            pair<node_t, vector<pair<node_t, node_t>>> result;
            result.first = INVALID_NODE;

            while(true) {
                if (cub != ub) {
                    delete solver;
                    solver = new CaDiCaL::Solver();

                    node_t step_limit = g.num_nodes() - ub;
                    cclauses = 0;
                    cvars=0;
                    init_vars(step_limit, ub - 1);

                    encode_order(step_limit);
                    encode_merge(step_limit);
                    encode_red(ub-1, step_limit);
                    encode_counters(ub-1, step_limit);
                    encode_vertex_counters(ub - 1, step_limit);
                    static_hints(ub-1, step_limit);
                    if (sb)
                        encode_sb(ub-1, step_limit);

                    cout << "Encoding done " << solver->vars() << "/" << cclauses << endl;
                    cub = ub;
                }

                solver->reset_assumptions();
                for (node_t t = 0; t < step; t++) {
                    assert(ord[t][contractions[t].first] != merge[t][contractions[t].second]);
                    solver->assume(ord[t][contractions[t].first]);
                    solver->assume(merge[t][contractions[t].second]);
                }

                // Use orbits to restrict initial contractions
                if (step == 0) {
                    vector<node_t> orbits(g.num_nodes());
                    g.get_orbits(orbits);
                    for(node_t n=0; n < g.num_nodes(); n++) {
                        if (orbits[n] == n)
                            solver->add(ord[0][n]);
                    }
                    solver->add(0);
                    ++cclauses;
                }

//                OutputLearner learn;
//                learn.add_vars("o", ord);
//                learn.add_vars("m", merge);
//                learn.add_vars("r", real_merge);
//                learn.add_vars("v", ord_vars);
//                learn.add_vars("c", card_vars);
//                learn.add_vars("r", red_count);
//                learn.add_vars("e", merged_edge);
//                learn.add_vars("x", merge_exists);
//                learn.add_vars3("cc", counters);
//                learn.add_vars3("re", red);

//                solver->connect_learner(&learn);

                auto ret = solver->solve();

                if (ret == 10) {
                    result.second.reserve(g.num_nodes());
                    result.second.clear();
                    dynamic_bitset<> seen(g.num_nodes());

                    for (node_t t = 0; t < g.num_nodes() - ub - 1u; t++) {
                        for (node_t n = 0; n < g.num_nodes(); n++) {
                            if (solver->val(ord[t][n]) > 0) {
                                assert(result.second.size() <= t);
                                result.second.emplace_back(n, INVALID_NODE);
                                seen.set(n);
                            }
                        }
                        assert(result.second.size() == t+1);
                        for (node_t n = 0; n < g.num_nodes(); n++) {
                            if (solver->val(merge[t][n]) > 0) {
                                assert(result.second[t].second == INVALID_NODE);
                                result.second[t].second = n;
                            }
                        }
                    }

                    // This is for testing, note that the asserts may fail as reds edges to deleted vertices can happen...
                    seen.reset();
                    for(node_t t=0; t < g.num_nodes()-ub-1u; t++) {
                        node_t merged = 0;
                        for(node_t n=0; n < g.num_nodes(); n++) {
                            if (solver->val(red_count[t][n]) > 0)
                                merged++;

                            node_t reds = 0;
                            for(node_t n2=0; n2 < g.num_nodes(); n2++) {
                                if (n != n2 && !seen.test(n2)) {
                                    if (solver->val(tred(t, n, n2)) > 0) {
                                        reds++;
                                    }
                                }
                            }
                            assert(reds < ub);
                            if (reds > 0)
                                assert(solver->val(counters[t][n][reds]) > 0);
                        }
                        assert(merged < ub);
                        seen.set(result.second[t].first);
                    }

                    node_t prev_node = INVALID_NODE;
                    for(node_t n=0; n < g.num_nodes(); n++) {
                        if (! seen.test(n)) {
                            if (prev_node != INVALID_NODE)
                                result.second.emplace_back(prev_node, n);
                            prev_node = n;
                        }
                    }

                    result.first = test_sequence(g, result.second);
                    ub = result.first;

                    cout << "Found " << +result.first << endl;

                    if (ub == 0)
                        return result;
                } else {
                    cout << "UNSAT" << endl;
                    return result;
                }
            }
        }
    };
}


#endif //TWW_BB_SAT_ENCODING_H