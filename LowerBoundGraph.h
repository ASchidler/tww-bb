#ifndef TWW_BB_LOWERBOUNDGRAPH_H
#define TWW_BB_LOWERBOUNDGRAPH_H

#include "BbParameters.h"

namespace tww {
    struct BbParameters;

    class LowerBoundGraph {
    public:
        void update_entry(node_t depth);
        explicit LowerBoundGraph(dynamic_bitset<> nodes, const vector<pair<node_t, node_t>> &red_edges,
                                 size_t watched_red, BbParameters &ps, vector<pair<node_t, vector<node_t>>>& black_twins);

        /** There is always only one red watched. */
        size_t watched_red;
        bool all_present = true;
        node_t not_subset_witness = INVALID_NODE;
        pair<node_t, node_t> conflicting_nodes = {INVALID_NODE, INVALID_NODE};

        node_t n1;
        node_t n2;

        size_t watched_index = SIZE_MAX;

        dynamic_bitset<> nodes;
        vector<pair<node_t, node_t>> red_edges;

        BbParameters& ps;

        void update_entry(node_t n_n1, node_t n_n2);

    private:
        vector<pair<node_t, vector<node_t>>> black_twins;
        void unset_witness();
        void set_witness(node_t cn, node_t first_witness=INVALID_NODE, node_t second_witness=INVALID_NODE);
        void check_subgraph(node_t depth);
    };
}


#endif //TWW_BB_LOWERBOUNDGRAPH_H
