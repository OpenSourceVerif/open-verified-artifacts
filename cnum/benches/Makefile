# SPDX-License-Identifier: GPL-2.0-only

.PHONY: build run clean

V ?= 0

ifeq ($(V), 0)
	Q := @
	print := @echo
else
	Q :=
	print = @true
endif

CC ?= gcc
CFLAGS := -std=gnu23 -Wall -Wpedantic -Wextra -Wshadow -MMD -MP
LDFLAGS :=

BIN := cnum.out
SRCS := $(wildcard *.c)
OBJS := $(SRCS:.c=.o)
DEPS := $(SRCS:.c=.d)

ifdef DEBUG
	CFLAGS += -g -O0 -fsanitize=address,undefined
	LDFLAGS += -fsanitize=address,undefined
else
	CFLAGS += -O2
endif

build: $(BIN)

$(BIN): $(OBJS)
	$(print) "  LD  $@"
	$(Q)$(CC) $^ $(LDFLAGS) -o $@

%.o: %.c
	$(print) "  CC  $@"
	$(Q)$(CC) $(CFLAGS) -c $< -o $@

-include $(DEPS)

clean:
	rm -rf $(BIN) $(OBJS) $(DEPS)
