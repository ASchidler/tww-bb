#ifndef TWW_BB_TWW_H
#define TWW_BB_TWW_H
#include <cctype>
#include <stdint.h>

#define VALIDATION_MODE false
#define USE_CANONICAL_PARTITION true

typedef uint16_t  node_t;
#define INVALID_NODE UINT16_MAX
#define TWW_TIMEOUT (INVALID_NODE-1)

#endif //TWW_BB_TWW_H
