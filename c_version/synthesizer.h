#ifndef SYNTHESIZER_H
#define SYNTHESIZER_H

#include <z3.h>
#include "common.h"
#include "config.h"

/* Synthesize protocol from ALL counter_examples (same as v2 Python). Returns true if sat and protocol filled. */
bool synthesize(Z3_context ctx, const counter_example_t *counter_examples, int num_cex,
                const int patterns[][NUM_NODES], protocol_t *protocol, timing_t *timing);

#endif /* SYNTHESIZER_H */
