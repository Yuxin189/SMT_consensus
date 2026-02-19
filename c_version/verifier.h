#ifndef VERIFIER_H
#define VERIFIER_H

#include <z3.h>
#include "common.h"
#include "config.h"

/* Returns: 2 = verified (no cex), 1 = cex found (cex filled), 0 = solver unknown (e.g. interrupted by Ctrl+C). */
int verify(Z3_context ctx, const protocol_t *protocol, const int patterns[][NUM_NODES],
           counter_example_t *cex, timing_t *timing);

#endif /* VERIFIER_H */
