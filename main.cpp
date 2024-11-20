#ifndef TWW_BB_MAIN
#define TWW_BB_MAIN

#include <iostream>
#include <string>
#include "twwbb2.h"
#include "graph.h"
#include <chrono>
#include "upper_bounds.h"
#include "lower_bounds.h"


using namespace std;
using namespace tww;

std::function<void(int)> shutdown_handler;
void signal_handler(int signal) { shutdown_handler(signal); }

int main(int argc, char* argv[]) {
    bool verbosity = false;
    bool print_tww = false;
    bool adaptive_fast_mode = false;
    bool use_cache = false;
    bool use_order_check = false;
    bool use_lb = false;
    node_t fast_limit = 250;
    long lb_timeout = 60;
    int special_graph = 0;
    node_t start_ub = INVALID_NODE;
    string proof_path = "";
    bool full_order = false;

    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();

    int last_parameter = 0;
    bool use_subgraph_lb = false;
    size_t cache_size = 7;
    bool tnb_nb = false;

    for(auto i=1; i < argc; ++i) {
        last_parameter = i;
        if (string(argv[i]) == "-v")
            verbosity = true;
        else if (string(argv[i]) == "-g")
            use_subgraph_lb = true;
        else if (string(argv[i]) == "-p")
            adaptive_fast_mode = true;
        else if (string(argv[i]) == "-c")
            use_cache = true;
        else if (string(argv[i]) == "-o")
            use_order_check = true;
        else if (string(argv[i]) == "-d")
            use_lb = true;
        else if (string(argv[i]) == "-b")
            tnb_nb = true;
        else if (string(argv[i]) == "-f")
            full_order = true;
        else if (string(argv[i]) == "-r") {
            ++i;
            proof_path = string(argv[i]);
            last_parameter = i;
        } else if (string(argv[i]) == "-l") {
            ++i;
            fast_limit = stoi(string(argv[i]), nullptr);
            last_parameter = i;
        }  else if (string(argv[i]) == "-n") {
            ++i;
            special_graph = stoi(string(argv[i]), nullptr);
            last_parameter = i;
        } else if (string(argv[i]) == "-u") {
            ++i;
            start_ub = stoi(string(argv[i]), nullptr);
            last_parameter = i;
        } else if (string(argv[i]) == "-e") {
            ++i;
            cache_size = stoul(string(argv[i]), nullptr);
            last_parameter = i;
        } else if (string(argv[i]) == "-t") {
            ++i;
            lb_timeout = stoul(string(argv[i]), nullptr);
            last_parameter = i;
        }
        else if (string(argv[i]) == "-w")
            print_tww = true;
        else {
            last_parameter = i - 1;
        }
    }

    auto filename = last_parameter < argc-1 ? string(argv[argc-1]) : "";

    if (verbosity)
        cout << filename << endl;

    auto pick_graph = [&]() {
        if (special_graph == 0)
            return Graph::parse(filename);
        if (special_graph == 1)
            return tww::create_grid(7, 7);
        if (special_graph == 2)
            return tww::prime_paley(277);
        if (special_graph == 3)
            return create_rook(20);
        if (special_graph == 4)
            return create_line(25);
        return create_knight(5);
    };

    auto parsed_g = pick_graph();

    Graph* g = &parsed_g;
    Graph og = g->copy(true);

    if (verbosity)
        cout << +og.num_nodes() << " Vertices " << og.num_edges() << " Edges" << endl;

    vector<pair<node_t, node_t>> twin_width_pp;
    dynamic_bitset<> comp_found(g->num_nodes());
    comp_found.set();

    bool changed = true;
    while (changed) {
        changed = false;
        for (node_t n1 = 0; n1 < parsed_g.num_nodes(); ++n1) {
            if (g->is_deleted(n1))
                continue;

            for (node_t n2 = n1 + 1; n2 < parsed_g.num_nodes(); ++n2) {
                if (parsed_g.is_deleted(n2))
                    continue;

                bool is_adj = parsed_g.adjacency[n1].test(n2);
                if ((is_adj && (parsed_g.adjacency[n1] ^ parsed_g.adjacency[n2]).count() == 2) ||
                    (!is_adj && parsed_g.adjacency[n1] == parsed_g.adjacency[n2])) {
                    twin_width_pp.emplace_back(n1, n2);
                    parsed_g.remove(n1);
                    comp_found.reset(n1);
                    changed = true;
                    break;
                }
            }
        }
    }

    if (verbosity)
        cout << "Preprocessed " << twin_width_pp.size() << " vertices." << endl;

    vector<node_t> q;
    vector<vector<node_t>> components;
    vector<node_t> single_vertices;
    q.reserve(g->num_nodes());

    while(comp_found.any()) {
        vector<node_t> new_comp;
        q.push_back(comp_found.find_first());
        comp_found.reset(q.back());

        while(! q.empty()) {
            auto cn = q.back();
            q.pop_back();
            new_comp.push_back(cn);

            for(auto cb=parsed_g.adjacency[cn].find_first(); cb != parsed_g.adjacency[cn].npos; cb = parsed_g.adjacency[cn].find_next(cb)) {
                if (comp_found.test(cb)) {
                    comp_found.reset(cb);
                    q.push_back(cb);
                }
            }
        }
        sort(new_comp.begin(), new_comp.end());
        components.push_back(std::move(new_comp));
    }

    if (verbosity)
        cout << "Found " << components.size() << " components" << std::endl;

    node_t overallub = 0;
    node_t overalllb = 0;

    vector<node_t> r_map(parsed_g.num_nodes(), INVALID_NODE);
    vector<node_t> node_map_pp(parsed_g.num_nodes());

    sort(components.begin(), components.end(), [&](const vector<node_t>& a, const vector<node_t>& b) {return a.size() < b.size();});

    for(auto& cp : components) {
        if (cp.size() == 1) {
            single_vertices.push_back(cp[0]);
        } else {
            node_map_pp.clear();
            g = new Graph(cp.size());

            for (auto n1: cp) {
                r_map[n1] = node_map_pp.size();
                node_map_pp.push_back(n1);
                for (auto n2 = parsed_g.adjacency[n1].find_first();
                     n2 < n1 && n2 != parsed_g.adjacency[n1].npos; n2 = parsed_g.adjacency[n1].find_next(n2)) {
                    if(r_map[n2] != INVALID_NODE)
                        g->add_edge(r_map[n1], r_map[n2]);
                }

                for (auto n2 = parsed_g.red_adjacency[n1].find_first();
                     n2 < n1 && n2 != parsed_g.red_adjacency[n1].npos; n2 = parsed_g.red_adjacency[n1].find_next(n2)) {
                    if(r_map[n2] != INVALID_NODE)
                        g->add_red_edge(r_map[n1], r_map[n2]);
                }
            }

            if (verbosity)
                cout << "Running component with " << g->num_nodes() << " vertices and " << g->num_edges() << " edges." << endl;

            pair<node_t, vector<pair<node_t, node_t>>> sub_result;

            node_t ub = min(static_cast<node_t>(g->num_nodes() - 1), start_ub);
            vector<pair<node_t, node_t>> best_contractions;

            auto ub_res = greedy(*g);
            if (ub_res.first <= ub) {
                ub = ub_res.first;
                best_contractions.clear();
                best_contractions.insert(best_contractions.end(), ub_res.second.begin(), ub_res.second.end());
            }

            auto ub_result = greedy2(*g, ub);
            if (ub_result.first < ub) {
                ub = ub_result.first;
                best_contractions.clear();
                best_contractions.insert(best_contractions.end(), ub_result.second.begin(), ub_result.second.end());
            }

            auto ub_result2 = greedy3(*g, ub);
            if (ub_result2.first < ub) {
                ub = ub_result2.first;
                best_contractions.clear();
                best_contractions.insert(best_contractions.end(), ub_result2.second.begin(), ub_result2.second.end());
            }

            node_t lb = overalllb;
            if (use_lb) {
                LowerBounds lbs(*g);

                if (g->num_nodes() < 1000) {
                    lb = lbs.find_lb1_subgraph(*g).first;
                    if (verbosity)
                        cout << "LB1: " << lb << endl;
                }

                std::chrono::steady_clock::time_point lb_begin = std::chrono::steady_clock::now();
                long time_passed = 0;
                for(node_t target_nodes = 20; target_nodes < g->num_nodes()-1 && time_passed < lb_timeout && lb < ub; target_nodes += 5) {
                    for (auto crun = 0; crun < 37  && time_passed < lb_timeout; ++crun) {
                        pair<vector<node_t>, dynamic_bitset<>> csub;
                        string method;
                        if (crun < 1) {
                            csub = lbs.peel_degree(*g, target_nodes);
                            method = "Peel DG";
                        } else if (crun < 2) {
                            csub = lbs.peel_minred(*g, target_nodes);
                            method = "Peel RD";
                        } else if (crun < 7) {
                            csub = lbs.degree_sampling(*g, target_nodes, crun != 2);
                            method = "Sample DG";
                        } else if (crun < 12) {
                            csub = lbs.red_sampling(*g, target_nodes, crun != 7);
                            method = "Sample RD";
                        } else if (crun < 17) {
                            csub = lbs.minred_sampling(*g, target_nodes, crun != 12);
                            method = "Sample RD";
                        } else if (crun < 22) {
                            csub = lbs.minred_nb_sampling(*g, target_nodes, crun != 17);
                            method = "Sample RD NB";
                        } else if (crun < 27) {
                            csub = lbs.maxdegree_nb(*g, target_nodes);
                            method = "DG NB";
                        } else if (crun < 32) {
                            csub = lbs.minred_nb(*g, target_nodes);
                            method = "RD NB";
                        } else {
                            csub = lbs.cliques_lb(*g, target_nodes);
                            method = "CQ";
                        }

                        // Use UB + 1, as we cannot have any optimal results that is larger than ub. Using ub would also be valid, but ub + 1 provides a solution as a sanity check.
                        auto next_lb = tww::check_subgraph(*g, use_cache, use_order_check, csub.first,
                                                           ub, lb, lb_timeout - time_passed);
                        lb = max(lb, next_lb);
                        if (verbosity)
                            cout << "LB " << method << ": " << next_lb << endl;
                        time_passed = std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - lb_begin).count();
                        assert(lb <= ub);
                    }
                }

                if (! best_contractions.empty()) {
                    std::chrono::steady_clock::time_point ub_begin = std::chrono::steady_clock::now();
                    time_passed = 0;

                    for(int x=0; x < 10000 && time_passed < lb_timeout && lb < ub; ++x) {
                        auto ub_result4 = greedy4(*g, ub);
                        if (ub_result4.first < ub) {
                            ub = ub_result4.first;
                            best_contractions.clear();
                            best_contractions.insert(best_contractions.end(), ub_result4.second.begin(), ub_result4.second.end());
                            time_passed = 0;
                        } else {
                            time_passed = std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - ub_begin).count();
                        }
                    }
                }
            }

            sub_result.first = ub;
            sub_result.second.insert(sub_result.second.begin(), best_contractions.begin(), best_contractions.end());
            if (!best_contractions.empty())
                assert(test_sequence(*g, best_contractions) == ub);

            if (verbosity) {
                cout << "UB: " << ub << endl;
            }

            assert(lb <= ub);

            if (ub > lb && overallub < ub) {
                BbParameters parameters(*g, 0, verbosity, g->num_nodes() >= fast_limit && !adaptive_fast_mode, use_subgraph_lb,
                                        adaptive_fast_mode, use_cache, use_order_check, cache_size, tnb_nb, &node_map_pp, proof_path, full_order);
                parameters.best_result.insert(parameters.best_result.begin(), ub_result.second.begin(), ub_result.second.end());
                if (!proof_path.empty()) {
                    for (auto& ct : twin_width_pp) {
                        parameters.proof_file << "T " << ct.first << " " << ct.second << std::endl;
                    }
                }
                for (node_t n=0; n < g->num_nodes(); ++n) {
                    parameters.red_counts[0][n] = g->red_adjacency[n].count();
                    lb = max(lb, parameters.red_counts[0][n]);
                }
                auto sub_tww = tww::find_tww(*g, ub, overallub < lb ? lb : overallub, false, verbosity, parameters, 0);
                overalllb = max(overalllb, sub_tww);

                if (sub_tww < sub_result.first) {
                    sub_result.first = sub_tww;
                    sub_result.second.clear();
                    sub_result.second.insert(sub_result.second.end(), parameters.best_result.begin(), parameters.best_result.end());
                }

                if (verbosity) {
                    cout << "BB-Result: " << sub_tww << endl;
                }
            }

            overallub = max(overallub, sub_result.first);

            for (auto &cc: sub_result.second) {
                twin_width_pp.emplace_back(node_map_pp[cc.first], node_map_pp[cc.second]);
            }
            single_vertices.push_back(node_map_pp[sub_result.second.back().second]);

            if (verbosity) {
                std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
                std::cout << "Time: " << std::chrono::duration_cast<std::chrono::seconds>(end - begin).count() << " s"
                          << std::endl;
            }

            if (!twin_width_pp.empty())
                delete g;
        }
    }

    if (verbosity || print_tww)
        cout << "Final Result: " << +overallub << endl;

    if (!twin_width_pp.empty()) {
        for (auto &cc: twin_width_pp)
            cout << +(cc.second + 1) << " " << +(cc.first + 1) << endl;

        for(int i=0; i < single_vertices.size() - 1; ++i) {
            cout << +(single_vertices.back()+1) << " " << +(single_vertices[i]+1) << std::endl;
            twin_width_pp.emplace_back(single_vertices[i], single_vertices.back());
        }

        auto check_result = test_sequence(og, twin_width_pp);

        assert(check_result == overallub);
        if (check_result != overallub)
            cerr << "ERROR, wrong result: " << check_result << " actual width, " << overallub << " reported width." << endl;
    }

    return 0;
}

#endif