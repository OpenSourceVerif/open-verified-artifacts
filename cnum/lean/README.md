# CNum (Circular Number Abstract Domain)

## Overview

This directory contains a Lean formal verification for the CNum abstract domain
used in the BPF verifier.

CNum represents a set of unsigned integers using a circular arc model: a base
point and a size along the circular 2^T number ring. This allows efficient
representation of ranges that may cross the UT_MAX/0 boundary.

## Background

The CNum data structure and operations are defined in the Linux kernel BPF
verifier:

- `kernel/bpf/cnum_defs.h`: Core type definitions and operations
- `kernel/bpf/cnum.c`: Instantiation for 32-bit and 64-bit

## Install

### Dependencies

- **Lean 4 v4.31.0**

For installing lean I recommend following the tutorial at
<https://lean-lang.org/install/manual/>, or to use the nix flake on this
directory to install it automatically:

```bash
nix develop
```

## Verification

The file [Cnum/Basic.lean](./Cnum/Basic.lean) contains a `Cnum` structure that
mimics the Linux kernel implementation, and the proofs that the new `contains`,
`normalize` functions preserve soundness.

To test check the proofs, you can simply build the module with:

```bash
lake build
```
