
#ifndef TWW_BB_TOOLS_H
#define TWW_BB_TOOLS_H
#include "graph.h"

using namespace std;

namespace tww {
    Graph create_grid(node_t x, node_t y);

    Graph create_reduced_grid(node_t extra);
    Graph create_rook(node_t n);

    Graph create_knight(node_t n);

    Graph create_line(node_t n);

    Graph prime_paley(node_t p);

    /** Generates the paley graph for p^2 */
    Graph prime_square_paley(node_t p);

    node_t test_sequence(Graph& og, vector<pair<node_t, node_t>>& contr);
}

#endif //TWW_BB_TOOLS_H
