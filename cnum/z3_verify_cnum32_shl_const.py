# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_shl_const (cnum_def.h, T=32)
#
# Theorem: forall ci, x, k:
#         ci non-empty, k is unsigned
#         implies (x << (k & (T-1))) in shl_const(ci, k)
#
# C implementation (from cnum_def.h, lines 223-251, 292-310):
#
#   trunc(cnum, bits_to_keep):
#       if empty(cnum)                  -> EMPTY
#       if top(cnum)                    -> UNBOUNDED
#       if cnum.size > UT_MAX - cnum.base   // crosses UT_MAX boundary
#           return from_urange(0, (1 << bits_to_keep) - 1)   // [MODIFIED: was UT_MAX << bits_to_keep]
#       start_high = cnum.base >> bits_to_keep
#       end_high   = (cnum.base + cnum.size) >> bits_to_keep
#       if start_high == end_high:
#           // low bits continuous
#           mask = (1ULL << bits_to_keep) - 1
#           return from_urange(cnum.base & mask, (cnum.base + cnum.size) & mask)
#       elif start_high + 1 == end_high:
#           // high bits differ by 1 -> low bits are [0, 2^bits_to_keep - 1]
#           return from_urange(0, (1ULL << bits_to_keep) - 1)
#       else:
#           return UNBOUNDED
#
#   shl_const(cnum, k):
#       if empty(cnum)                  -> EMPTY
#       k &= T-1                        // normalize shift amount
#       if cross_unsigned_limit(cnum)  -> {0, UT_MAX << k}
#       bits_to_keep = T - k
#       truncated_cnum = trunc(cnum, bits_to_keep)
#       if top(truncated_cnum)          -> UNBOUNDED
#       return from_urange(truncated_cnum.base << k, (truncated_cnum.base + truncated_cnum.size) << k)
#
#   from_urange(lo, hi): if lo > hi -> EMPTY; else {base=lo, size=hi-lo}
#
#   cross_unsigned_limit(cnum):
#       false if empty or top ({0, UT_MAX})
#       true  if contains(UT_MAX) && contains(0)
#
#   contains(cnum, v):
#       if empty -> false
#       if urange_overflow -> v >= base || v <= base+size (wrapped)
#       else -> v >= base && v <= base+size

from z3 import *
import time

def main():
    t0 = time.monotonic()

    T = 32
    UT_MAX_VAL = (1 << T) - 1
    UT_MAX = BitVecVal(UT_MAX_VAL, T)
    # EMPTY = {UT_MAX, UT_MAX} -- sentinel: base == size == UT_MAX
    EMPTY_base = UT_MAX
    EMPTY_size = UT_MAX
    # UNBOUNDED (top) = {0, UT_MAX} -- represents all 32-bit values
    TOP_base   = BitVecVal(0, T)
    TOP_size   = UT_MAX

    # Symbolic inputs
    ci_base = BitVec("ci_base", T)
    ci_size = BitVec("ci_size", T)
    k       = BitVec("k", T)
    x       = BitVec("x", T)

    # ---- Primitive helpers ----

    def is_empty(base, size):
        # EMPTY = {UT_MAX, UT_MAX}
        return And(base == EMPTY_base, size == EMPTY_size)

    def is_top(base, size):
        # UNBOUNDED = {0, UT_MAX}
        return And(base == TOP_base, size == TOP_size)

    def is_const(base, size):
        # Single value: size == 0
        return size == BitVecVal(0, T)

    def urange_overflow(base, size):
        # [base, base+size] overflows 32-bit wrap-around
        return UGT(size, UT_MAX - base)

    def contains(base, size, v):
        """True iff unsigned value v is in the circular range [base, base+size]."""
        empty = is_empty(base, size)
        ov    = urange_overflow(base, size)
        # base+size as C uint32_t: wrap on overflow
        sum_wrapped = (base + size) & UT_MAX
        return If(empty, False,
                  If(ov,
                     Or(UGE(v, base), ULE(v, sum_wrapped)),
                     And(UGE(v, base), ULE(v, base + size))))

    def cross_unsigned_limit(base, size):
        """
        True iff the range contains both UT_MAX and 0.
        Excludes empty and top ({0, UT_MAX}).
        In C: contains(UT_MAX) && contains(0)
        """
        return If(Or(is_empty(base, size), is_top(base, size)),
                  False,
                  And(contains(base, size, UT_MAX),
                      contains(base, size, BitVecVal(0, T))))

    # ---- Preconditions ----
    ci_empty = is_empty(ci_base, ci_size)

    # ci_upper = ci.base + ci.size  (C uint32_t wrap)
    ci_upper = (ci_base + ci_size) & UT_MAX

    # ---- normalize shift amount ----
    # C: k &= T-1
    k_norm = k & BitVecVal(T - 1, T)

    # ---- cross_unsigned_limit(ci) ----
    ci_cul = cross_unsigned_limit(ci_base, ci_size)

    # ---- Step 1: cross_unsigned_limit(ci) early-return path ----
    # C: if cross_unsigned_limit(ci) -> return {0, UT_MAX << k}
    # {0, UT_MAX << k} as from_urange: base=0, size=UT_MAX<<k
    cul_res_base = BitVecVal(0, T)
    cul_res_size = UT_MAX << k_norm

    # ---- Step 2: trunc(ci, bits_to_keep) where bits_to_keep = T - k ----
    # C: ut bits_to_keep = T - k
    bits_to_keep = T - k_norm

    # C: if cnum.size > UT_MAX - cnum.base -> from_urange(0, (1 << bits_to_keep) - 1)
    # Note: in the context of shl_const, this is the "crosses boundary" check inside trunc,
    # but since shl_const already checked cross_unsigned_limit(cnum) and returned above,
    # the cnum here (ci) does NOT cross the unsigned limit.
    # However, the trunc function itself has this check for its own purposes.
    # In shl_const, we call trunc(ci, T-k) where ci does NOT cross UL.
    # So the trunc path goes to the "otherwise" branch.
    # But we need to model trunc correctly:
    ci_overflows = UGT(ci_size, UT_MAX - ci_base)

    # C (modified): return from_urange(0, (1ULL << bits_to_keep) - 1)
    # Previously was: (1ULL << bits_to_keep) - 1 was UT_MAX << bits_to_keep
    trunc_cul_base = BitVecVal(0, T)
    trunc_cul_size = (BitVecVal(1, T) << bits_to_keep) - BitVecVal(1, T)

    # C: start_high = cnum.base >> bits_to_keep
    start_high = LShR(ci_base, bits_to_keep)
    # C: end_high = (cnum.base + cnum.size) >> bits_to_keep
    end_high   = LShR(ci_upper, bits_to_keep)

    # C: if start_high == end_high:
    #     mask = (1ULL << bits_to_keep) - 1
    #     lower_start = cnum.base & mask
    #     lower_end = (cnum.base + cnum.size) & mask
    #     return from_urange(lower_start, lower_end)
    mask = (BitVecVal(1, T) << bits_to_keep) - BitVecVal(1, T)
    lower_start = ci_base & mask
    lower_end   = ci_upper & mask
    # from_urange: if lower_end < lower_start -> EMPTY
    trunc_s1_base = If(UGT(lower_start, lower_end), EMPTY_base, lower_start)
    trunc_s1_size = If(UGT(lower_start, lower_end), EMPTY_size, lower_end - lower_start)

    # C: else if start_high + 1 == end_high:
    #     return from_urange(0, (1ULL << bits_to_keep) - 1)
    trunc_s2_base = BitVecVal(0, T)
    trunc_s2_size = (BitVecVal(1, T) << bits_to_keep) - BitVecVal(1, T)

    # C: else: return UNBOUNDED
    trunc_unbounded_base = TOP_base
    trunc_unbounded_size = TOP_size

    # Combine trunc cases:
    # if cnum.size > UT_MAX - cnum.base -> {0, UT_MAX << bits_to_keep}
    # else if start_high == end_high -> {lower_start, lower_end}
    # else if start_high + 1 == end_high -> {0, (1<<bits_to_keep)-1}
    # else -> UNBOUNDED
    trunc_base = If(ci_overflows,
                    trunc_cul_base,
                    If(start_high == end_high,
                       trunc_s1_base,
                       If(start_high + 1 == end_high,
                          trunc_s2_base,
                          trunc_unbounded_base)))

    trunc_size = If(ci_overflows,
                    trunc_cul_size,
                    If(start_high == end_high,
                       trunc_s1_size,
                       If(start_high + 1 == end_high,
                          trunc_s2_size,
                          trunc_unbounded_size)))

    # ---- Step 3: if top(truncated_cnum) -> return UNBOUNDED ----
    trunc_top = is_top(trunc_base, trunc_size)

    # ---- Step 4: return from_urange(truncated_cnum.base << k, (truncated_cnum.base + truncated_cnum.size) << k) ----
    # Note: truncated_cnum.base + truncated_cnum.size uses C uint32_t arithmetic
    # but since truncated_cnum was produced by from_urange, it should not overflow
    # (from_urange returns EMPTY if lo > hi, and the range is within UT_MAX).
    # However, we use & UT_MAX to be safe.
    trunc_upper = (trunc_base + trunc_size) & UT_MAX
    shl_const_base = trunc_base << k_norm
    shl_const_upper = trunc_upper << k_norm

    # from_urange: if shl_const_base > shl_const_upper -> EMPTY
    shl_const_res_base = If(UGT(shl_const_base, shl_const_upper), EMPTY_base, shl_const_base)
    shl_const_res_size = If(UGT(shl_const_base, shl_const_upper), EMPTY_size, shl_const_upper - shl_const_base)

    # ---- Full shl_const result ----
    # C: shl_const(ci, k):
    #   1. if empty(ci)       -> EMPTY
    #   2. if cross_unsigned_limit(ci) -> {0, UT_MAX << k}
    #   3. truncated = trunc(ci, T - k)
    #   4. if top(truncated)  -> UNBOUNDED
    #   5. return from_urange(truncated.base << k, (truncated.base + truncated.size) << k)
    res_base = If(ci_empty, EMPTY_base,
                  If(ci_cul, cul_res_base,
                     If(trunc_top, trunc_unbounded_base,
                        shl_const_res_base)))

    res_size = If(ci_empty, EMPTY_size,
                  If(ci_cul, cul_res_size,
                     If(trunc_top, trunc_unbounded_size,
                        shl_const_res_size)))

    # ---- Theorem ----
    # x_shl = x << (k & (T-1))  -- actual C left-shift of x with shift amount k & 31
    # Note: C left shift of a value that overflows the bit width is undefined behavior.
    # However, since x is constrained to be in ci (a valid cnum range), and the shift
    # amount k is normalized to [0, T-1], we only need to verify the case where
    # the shift result is well-defined.
    # In practice, we verify the theorem: x in ci, k in [0,T-1] => x<<k in shl_const(ci,k)
    # This includes the case where x<<k may overflow, but that's part of the cnum semantics.
    x_shl = x << k_norm

    # Theorem: ci non-empty, x in ci
    #          => (x << (k & 31)) in shl_const(ci, k)
    theorem = Implies(
        And(Not(ci_empty),
            contains(ci_base, ci_size, x),
            ULE(k, BitVecVal(T - 1, T))),
        contains(res_base, res_size, x_shl))

    # ---- Solver: try to find a counterexample ----
    s = Solver()
    s.set("timeout", 3600000)
    s.set("threads", 16)
    s.add(Not(theorem))  # Negate: find case where theorem is violated

    print("Verifying cnum32_shl_const (1hr timeout, 16 threads)...")
    print("Theorem: ci non-empty, x in ci, k in [0,31]")
    print("         implies (x << (k & 31)) in shl_const(ci, k)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        m = s.model()
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        def u(name):    return m[name].as_long()
        def ev(expr):   return m.eval(expr).as_long()
        def evb(expr):  return is_true(m.eval(expr))
        print(f"\n  ci       = {{base={u(ci_base)}, size={u(ci_size)}}}")
        print(f"  k        = {u(k)}  (k & 31) = {u(k) & 31}")
        print(f"  x        = {u(x)}  x<<(k&31) = {(u(x) << (u(k) & 31)) & UT_MAX_VAL}")
        print(f"  ci_empty = {evb(ci_empty)}")
        print(f"  ci_cul   = {evb(ci_cul)}")
        print(f"  ci_overflows = {evb(ci_overflows)}")
        print(f"  bits_to_keep = {ev(bits_to_keep)}")
        print(f"  start_high = {ev(start_high)}  end_high = {ev(end_high)}")
        print(f"  mask = {ev(mask)}")
        print(f"  lower_start = {ev(lower_start)}  lower_end = {ev(lower_end)}")
        print(f"  trunc_base = {ev(trunc_base)}  trunc_size = {ev(trunc_size)}")
        print(f"  trunc_top  = {evb(trunc_top)}")
        print(f"  shl_const_base   = {ev(shl_const_base)}  shl_const_upper = {ev(shl_const_upper)}")
        print(f"  res        = {{base={ev(res_base)}, size={ev(res_size)}}}")
        print(f"  contains(ci, x)      = {evb(contains(ci_base, ci_size, x))}")
        print(f"  contains(res, x_shl) = {evb(contains(res_base, res_size, x_shl))}")
        return 1
    elif result == unsat:
        print("PASS: cnum32_shl_const verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2

if __name__ == "__main__":
    exit(main())
