#include "BbParameters.h"

using namespace  std;

namespace tww {
    BbParameters::~BbParameters() {
        if (!fast_mode) {
            for (auto &queue_entry: queue_entries) {
                delete queue_entry;
            }
        }
        for (auto cg: all_lower_bound_graphs)
            delete cg;
        if (proof_log)
            proof_file.close();
    }
} // tww