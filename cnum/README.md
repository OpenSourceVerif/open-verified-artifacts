# CNum (Circular Number Abstract Domain)

## Overview

This directory contains Z3 formal verification for the CNum abstract domain used in the BPF verifier.

CNum represents a set of unsigned integers using a circular arc model: a base point and a size along the circular 2^T number ring. This allows efficient representation of ranges that may cross the UT_MAX/0 boundary.

## Background

The CNum data structure and operations are defined in the Linux kernel BPF verifier:
- `kernel/bpf/cnum_defs.h`: Core type definitions and operations
- `kernel/bpf/cnum.c`: Instantiation for 32-bit and 64-bit

## Install

### Dependencies

- **Python 3.8+**
- **Z3 Theorem Prover 4.8+**

Install Z3 via pip:

```bash
pip install z3-solver
```

## Verification

### Z3 Verification Files (Python)

Each file implements a counter-example guided verification using Z3's QF_BV theory.

#### 32-bit:

- `z3_verify_cnum32_add.py`: Verifies that for all `x ∈ ci` and `y ∈ cj`, `x +_{32} y ∈ cnum32_add(ci, cj)`.
- `z3_verify_cnum32_negate.py`: Verifies that for all `x ∈ ci`, `-x ∈ cnum32_negate(ci)`.

#### 64-bit:

- `z3_verify_cnum64_add.py`: Same property as above for 64-bit arithmetic.
- `z3_verify_cnum64_negate.py`: Same property as above for 64-bit arithmetic.

### Running Verification

Run all verifications:

```bash
make verify
```

Run individual verifications:

```bash
make verify-32-add
make verify-32-negate
make verify-64-add
make verify-64-negate
```

Or run directly with Python:

```bash
python z3_verify_cnum32_add.py
python z3_verify_cnum32_negate.py
python z3_verify_cnum64_add.py
python z3_verify_cnum64_negate.py
```

### Verification Theorem

```
forall ci, cj, x, y in BV_T:
  ci is non-empty and cj is non-empty and
  contains_T(ci, x) and contains_T(cj, y)
  implies contains_T(cnum_T_add(ci, cj), x +_T y)
```

### Key Properties Verified

- **Correctness**: All concrete values in the operands produce results contained in the abstract result.
- **Soundness**: The abstract result never excludes any possible concrete result.
- **Overflow handling**: Both `add` and `negate` correctly handle wrap-around on the circular domain.
- **Normalize invariant**: The `normalize` function correctly canonicalizes representation edge cases.
