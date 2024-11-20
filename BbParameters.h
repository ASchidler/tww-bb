
#ifndef TWW_BB_BBPARAMETERS_H
#define TWW_BB_BBPARAMETERS_H

#include "tww.h"
#include "graph.h"
#include "MemoryAwareCache.h"
#include "LowerBoundGraph.h"

namespace tww {
    struct LowerBoundGraph;

    struct QueueEntry {
        QueueEntry( node_t reds_count,
                    node_t max_degree,
                    node_t n,
                    node_t n2,
                    dynamic_bitset<> reds,
                    dynamic_bitset<> new_reds,
                    dynamic_bitset<> nonnew_reds,
                    node_t max_degree_nodes) : reds_count(reds_count), max_degree(max_degree), n(n), n2(n2), reds(std::move(reds)), new_reds(std::move(new_reds)), nonnew_reds(std::move(nonnew_reds)),
                    max_degree_nodes(max_degree_nodes) {
        }

        void copy(const QueueEntry& ce) {
            reds_count = ce.reds_count;
            max_degree = ce.max_degree;
            max_degree_nodes = ce.max_degree_nodes;
            n = ce.n;
            n2 = ce.n2;
            reds = ce.reds;
            new_reds = ce.new_reds;
            nonnew_reds = ce.nonnew_reds;
        }

        node_t reds_count;
        node_t max_degree;
        node_t max_degree_nodes;
        node_t n;
        node_t n2;
        dynamic_bitset<> reds;
        dynamic_bitset<> new_reds;
        dynamic_bitset<> nonnew_reds;
        bool is_twin = false;

        bool operator < (const QueueEntry& rh) const {
//            return (max_degree < rh.max_degree ||
//                    (max_degree == rh.max_degree && reds_count < rh.reds_count) ||
//                    (max_degree == rh.max_degree && max_degree_nodes < rh.max_degree_nodes && reds_count == rh.reds_count) ||
//                    (max_degree == rh.max_degree && max_degree_nodes == rh.max_degree_nodes && reds_count == rh.reds_count && n < rh.n) ||
//                    (max_degree == rh.max_degree && max_degree_nodes == rh.max_degree_nodes && reds_count == rh.reds_count && n == rh.n && n2 < rh.n2)
//            );
            return (max_degree < rh.max_degree ||
                    (max_degree == rh.max_degree && max_degree_nodes < rh.max_degree_nodes) ||
                    (max_degree == rh.max_degree && max_degree_nodes == rh.max_degree_nodes && reds_count < rh.reds_count) ||
                    (max_degree == rh.max_degree && max_degree_nodes == rh.max_degree_nodes && reds_count == rh.reds_count && n < rh.n) ||
                    (max_degree == rh.max_degree && max_degree_nodes == rh.max_degree_nodes && reds_count == rh.reds_count && n == rh.n && n2 < rh.n2)
            );
//            return (max_degree < rh.max_degree ||
//                    (max_degree == rh.max_degree && reds_count < rh.reds_count) ||
//                    (max_degree == rh.max_degree && reds_count == rh.reds_count && n < rh.n) ||
//                    (max_degree == rh.max_degree && reds_count == rh.reds_count && n == rh.n && n2 < rh.n2)
//            );
        }
    };

    struct BbParameters {
        explicit BbParameters(Graph& g, node_t sat_depth, bool verbose, bool fast_mode, bool use_subgraph_lb, bool adaptive_fast_mode,
                              bool use_cache, bool use_order_check, size_t cache_size=7, bool tnb_mode=false, vector<node_t>* r_map=nullptr, string proof_file_path="", bool full_order=false) :
                g(g), g_copy(g.copy(true)), g_cache(0), cache((cache_size * 1000000000 / (sizeof(node_t) * g.num_nodes() + 2 * sizeof(size_t) + sizeof(node_t))) * 2/3),
                red_counts(g.num_nodes()), verbose(verbose), queues(g.num_nodes()), queue_entries(g.num_nodes()),
                previous_contractions(g.num_nodes()), c_partitions(g.num_nodes(), vector<node_t>(g.num_nodes())), c_old_pat(g.num_nodes(), vector<node_t>(g.num_nodes())),
                labeling(g.num_nodes()), queue_pointers(g.num_nodes()), best_results(g.num_nodes(), g.num_nodes()),
                current_degree(g.num_nodes()), gcs(g.num_nodes()),
//        old_partitions(g.num_nodes(), dynamic_bitset<>(g.num_nodes())),
                deg_changes(g.num_nodes()),
                partitions(g.num_nodes(), vector<node_t>(g.num_nodes())), fast_mode(fast_mode), is_twin(g.num_nodes(), false),
                use_subgraph_lb(use_subgraph_lb), adaptive_fast_mode(adaptive_fast_mode), use_cache(use_cache),
                use_order_cache(use_order_check), has_contraction(g.num_nodes(), false), max_degree(g.num_nodes(), 0),
                lower_bound_by_node(g.num_nodes()), tnb_mode(tnb_mode), proof_log(!proof_file_path.empty()), full_order(full_order){
            red_counts = vector<vector<node_t>>(g.num_nodes(), vector<node_t>(g.num_nodes(), 0));
            fill(red_counts[0].begin(), red_counts[0].end(), 0);

            if (proof_log)
                proof_file.open(proof_file_path);

            for (node_t i=0; i < g.num_nodes(); i++)
                partitions[0][i] = i;

            trace = vector<node_t> (g.num_nodes(), 0);
            reduced = vector<dynamic_bitset<>>(g.num_nodes(), dynamic_bitset<>(g.num_nodes()));
            // TODO: Cache could be separated into different depths...

            contractions = vector<pair<node_t, node_t>>(g.num_nodes());

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

            if (use_subgraph_lb) {
                lower_bound_graphs.resize(g.num_nodes() + 1);

                for(node_t n2=0; n2 < g.num_nodes(); n2++) {
                    lower_bound_graphs[n2].resize(n2);
                }
            }

            best_result.reserve(g.num_nodes());


            for(node_t n=0; n < g.num_nodes(); n++) {
                if(fast_mode) {
                    queues[n] = &default_queue;
                } else {
                    queue_entries[n] =  new vector<QueueEntry>();
                    queues[n] = queue_entries[n];
                }
            }

            if (r_map != nullptr)
                this->r_map.insert(this->r_map.end(), r_map->begin(), r_map->end());
        }

        ~BbParameters();

        /** Log output enabled or not */
        bool verbose;
        /** The input graph */
        Graph& g;
        /** An unmodified copy of the input graph */
        Graph g_copy;
        /** Keeps track of the red degree for each vertex */
        vector<vector<node_t>> red_counts;
        /** The cache used to avoid rerunning the same trigraphs */
        MemoryAwareCache<vector<node_t>, VectorHash<node_t>, VectorEqual<node_t>> cache;
//        unordered_map<vector<node_t>, node_t, VectorHash<node_t>, VectorEqual<node_t>> cache;
        /** Keeps track of the contraction vertices */
        vector<node_t> trace;
        /** The vertices whose red degree decreased for each depth */
        vector<dynamic_bitset<>> reduced;
        /** Keeps track of the contractions */
        vector<pair<node_t, node_t>> contractions;
        vector<vector<dynamic_bitset<>>> contractions_edges;
        /** Contains for each contraction a lower bound on the red degree of the contraction vertex */
        vector<vector<node_t>> lookahead_count;
        /** Contains for each vertex the contractions that create a red edge to this vertex */
        vector<vector<pair<node_t, node_t>>> lookahead_refs;
        /** A cache that uses the canonical ordering of the graph as key */
        MemoryAwareCache<string> g_cache;
        /** The queues for each depth */
        vector<vector<QueueEntry>*> queues;
        /** The queues for each depth, as a reference. While queues might change where it points to queue_entries remains the same */
        vector<vector<QueueEntry>*> queue_entries;
        /** Used to find previous contractions that are the same as the current one */
        vector<vector<tuple<node_t, node_t, node_t>>> previous_contractions;
        /** Keeps track of the partition induced by the contractions */
        vector<vector<node_t>> c_partitions;
        /** Temporary variable used in conjunction with the partition */
        vector<vector<node_t>> c_old_pat;
        /** The canonical labeling as found by nauty */
        vector<node_t> labeling;
        /** The orbits as identified by nauty */
        vector<vector<node_t>> orbits;
        /** The index in the queue for each depth */
        vector<size_t> queue_pointers;
        /** The best maximum red degree for each depth over all seen contraction sequences. */
        vector<node_t> best_results;
        /** The maximum red degree seen until this depth. */
        vector<node_t> current_degree;
        /** Canonical representation for the trigraph at each depth */
        vector<string> gcs;

        bool full_order;

        vector<node_t> deg_changes;
        vector<vector<node_t>> partitions;
        vector<pair<node_t, node_t>> best_result;
        vector<QueueEntry> default_queue;
        /** Fast mode uses only one queue for all depths and is created for large graphs, where creating n queues is prohibitive */
        bool fast_mode;

        /** Use two-neighborhood instead of all vertices, makes the result not guaranteed optimal */
        bool tnb_mode;

        /** Keeps track for each depth if the contraction is a twin. Used if fast_mode is true */
        vector<char> is_twin;
        /** Keeps a list of lower bound trigraphs referenced by one of the not-yet-existing red edges */
        vector<vector<vector<LowerBoundGraph*>>> lower_bound_graphs;
        /** A list of all lower bound graphs */
        vector<LowerBoundGraph*> all_lower_bound_graphs;
        /* A list of all lower bound graphs, referenced by a missing node */
        vector<vector<LowerBoundGraph*>> lower_bound_by_node;

        /** If true, trigraphs that cannot be contracted anymore are collected as lower bounds */
        bool use_subgraph_lb;
        /** If true, once we reach ub-1 we enter fast mode */
        bool adaptive_fast_mode;
        /** If true, caching is used */
        bool use_cache;
        /** If true, we try to reorder the contractions to get a cache hit */
        bool use_order_cache;

        /** Keeps track if for the current depth, any successor contractions were performed */
        vector<char> has_contraction;

        vector<node_t> max_degree;

        bool proof_log;
        ofstream proof_file;
        vector<node_t> r_map;
    };
} // tww

#endif //TWW_BB_BBPARAMETERS_H
