#ifndef VERIFIER_H
#define VERIFIER_H

#include <z3.h>
#include "common.h"
#include "config.h"

/* Returns: 2 = verified, 1 = cex found, 0 = solver unknown */
int verify(Z3_context ctx, const protocol_t *protocol, const int *patterns,
           counter_example_t *cex, timing_t *timing);

#endif /* VERIFIER_H */
