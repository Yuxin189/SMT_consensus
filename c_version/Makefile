CC = gcc
CFLAGS = -O3 -Wall -Wextra -std=c11
LDFLAGS = -lz3

# Z3 paths: try pkg-config, then Z3_PREFIX, then Python z3 package
Z3_CFLAGS := $(shell pkg-config --cflags z3 2>/dev/null)
Z3_LDFLAGS := $(shell pkg-config --libs z3 2>/dev/null)
ifneq ($(Z3_CFLAGS),)
  CFLAGS += $(Z3_CFLAGS)
  LDFLAGS = $(Z3_LDFLAGS)
else
  # Fallback: Z3_PREFIX or Python z3 package path
  Z3_PREFIX ?= $(shell python3 -c "import z3, os; p=os.path.join(os.path.dirname(z3.__file__)); print(p)" 2>/dev/null || echo "/usr/local")
  CFLAGS += -I$(Z3_PREFIX)/include
  LDFLAGS = -L$(Z3_PREFIX)/lib -lz3 -Wl,-rpath,$(Z3_PREFIX)/lib
endif

SRCS = main.c common.c system_model.c synthesizer.c verifier.c
OBJS = $(SRCS:.c=.o)
TARGET = cegis

.PHONY: all clean run

all: $(TARGET)

$(TARGET): $(OBJS)
	$(CC) $(OBJS) -o $@ $(LDFLAGS)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(TARGET) generated_protocol_c.c

run: $(TARGET)
	@Z3LIB=$$(python3 -c "import z3, os; print(os.path.join(os.path.dirname(z3.__file__), 'lib'))" 2>/dev/null); \
	if [ -n "$$Z3LIB" ] && [ -d "$$Z3LIB" ]; then \
		DYLD_LIBRARY_PATH="$$Z3LIB:$$DYLD_LIBRARY_PATH" LD_LIBRARY_PATH="$$Z3LIB:$$LD_LIBRARY_PATH" ./$(TARGET); \
	else \
		./$(TARGET); \
	fi
