#ifndef CONFIG_H
#define CONFIG_H

#define NUM_NODES 3
#define NUM_ROUNDS 3

/* NUM_PATTERNS = 3^NUM_NODES (same as Python itertools.product([0,1,2], repeat=NUM_NODES)) */
#if NUM_NODES == 3
#define NUM_PATTERNS 27
#elif NUM_NODES == 4
#define NUM_PATTERNS 81
#elif NUM_NODES == 5
#define NUM_PATTERNS 243
#else
#error "Define NUM_PATTERNS for your NUM_NODES (3^NUM_NODES)"
#endif

/* Message values: 0/1 received, 2 = missing */

#endif /* CONFIG_H */
