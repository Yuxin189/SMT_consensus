#ifndef SYNTHESIZER_H
#define SYNTHESIZER_H

#include <z3.h>
#include "common.h"
#include "config.h"

/* Synthesize Atomic Commit protocol from ALL counter_examples. Returns true if sat. */
bool synthesize(Z3_context ctx, const counter_example_t *counter_examples, int num_cex,
                const int *patterns, protocol_t *protocol, timing_t *timing);

#endif /* SYNTHESIZER_H */
