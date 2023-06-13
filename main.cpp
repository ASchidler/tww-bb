#include <iostream>
#include <string>
#include "twwbb2.h"
#include "graph.h"
#include "tools.h"
#include "sat_encoding.h"
#include <chrono>
#include <csignal>

using namespace std;
using namespace tww;

std::function<void(int)> shutdown_handler;
void signal_handler(int signal) { shutdown_handler(signal); }

int main(int argc, char* argv[]) {
    bool verbosity = false;
    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
    auto filename = argc > 1 && argv[argc-1][0] != '-' ? string(argv[argc-1]) : "";

    for(auto i=1; i < argc; ++i) {
        if (string(argv[i]) == "-v")
            verbosity = true;
    }

    if (verbosity)
        cout << filename << endl;

    bool use_sat = argc > 2 && string(argv[1]) == "-s";
    bool use_sb = argc > 3 && string(argv[2]) == "-b";

    auto parsed_g = Graph::parse(filename);
//    auto g = tww::create_grid(7, 7);
//    auto g = tww::prime_paley(73);
//    auto g = tww::create_rook(20);
//    auto g = create_line(25);
//    auto g = create_knight(5);
    Graph* g = &parsed_g;

    if (verbosity)
        cout << +parsed_g.num_nodes() << " Vertices " << parsed_g.num_edges() << " Edges" << endl;

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

    vector<node_t> r_map(parsed_g.num_nodes());
    vector<node_t> node_map_pp(parsed_g.num_nodes());
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
                    g->add_edge(r_map[n1], r_map[n2]);
                }
            }

            auto parameters = BbParameters(*g, 0, verbosity);

//            bool output_done = false;
//    shutdown_handler = [&](int signum=0) {
//        if (output_done)
//            return;
//
//        output_done = true;
//
//
//    };

//    std::signal(SIGTERM, signal_handler);
            if (verbosity)
                cout << "Running component with " << g->num_nodes() << " vertices and " << g->num_edges() << " edges." << endl;
            if (use_sat) {
                SatEncoding enc(*g);
                vector<pair<node_t, node_t>> dummy;
                auto ub = tww::find_tww(*g, g->num_nodes() - 1, true, verbosity, parameters);
                cout << "UB " << +ub << endl;
                overallub = max(overallub, ub);
                auto result = enc.run(min(ub + 1, g->num_nodes() - 1), dummy, 0, use_sb);
                cout << "Final result: " << +result.first << endl;
            } else {
                auto sub_result = tww::find_tww(*g, g->num_nodes() - 1, false, verbosity, parameters);
                overallub = max(overallub, sub_result);
                if (verbosity) {
                    cout << "Result: " << sub_result << endl;
                    cout << "Calls: " << tww::counter << endl;
                }

                for (auto &cc: parameters.best_result) {
                    twin_width_pp.emplace_back(node_map_pp[cc.first], node_map_pp[cc.second]);
                }
                single_vertices.push_back(node_map_pp[parameters.best_result.back().second]);
            }
            if (verbosity) {
                std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
                std::cout << "Time: " << std::chrono::duration_cast<std::chrono::seconds>(end - begin).count() << " s"
                          << std::endl;
            }


//    shutdown_handler(0);
            if (!twin_width_pp.empty())
                delete g;
        }
    }

    if (verbosity)
        cout << "Final Result: " << +overallub << endl;

    if (!twin_width_pp.empty()) {
        for (auto &cc: twin_width_pp)
            cout << +(cc.second + 1) << " " << +(cc.first + 1) << endl;

        for(int i=0; i < single_vertices.size() - 1; ++i) {
            cout << +(single_vertices.back()+1) << " " << +(single_vertices[i]+1) << std::endl;
        }
    }
    return 0;
}
