# Interval (Byte-Swap Interval Abstract Domain)

## Structure

### 64-bit Byte-Swap Verification:

* `z3_verify_bswap_unsigned.cpp`: Z3 formal verification for 64-bit unsigned bswap on Interval domain.
* `z3_verify_bswap_signed.cpp`: Z3 formal verification for 64-bit signed bswap on Interval domain.

### 16-bit Byte-Swap Verification:

* `z3_verify_bswap16_unsigned.cpp`: Z3 formal verification for 16-bit unsigned bswap on Interval domain.
* `z3_verify_bswap16_signed.cpp`: Z3 formal verification for 16-bit signed bswap on Interval domain (with interval splitting for zero-crossing cases).

## Description

This directory contains correctness verification for byte-swap (bswap) operations on interval abstract domains using the Z3 SMT solver.

Each verification file checks: given an input interval `[lb, ub]`, whether the algorithm-computed output interval `[min, max]` can completely cover all possible `bswap(x)` values (where `x ∈ [lb, ub]`).

The verification uses a counter-example search approach: it attempts to find a counter-example where `bswap(x)` falls outside the algorithm-computed range. If Z3 returns UNSAT, the algorithm is proven correct.

