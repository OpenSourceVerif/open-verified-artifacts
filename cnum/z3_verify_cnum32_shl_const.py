# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_shl_const (cnum_def.h, T=32)
#
# Theorem: forall ci, x, k:
#         ci non-empty, k is unsigned
#         implies (x << (k & (T-1))) in shl_const(ci, k)
#
# C implementation (from cnum_def.h, lines 223-252, 292-310):
#
#   trunc(cnum, bits_to_keep):       [REWRITTEN]
#       if empty(cnum)                  -> EMPTY
#       if top(cnum)                    -> UNBOUNDED
#       start_high = cnum.base >> bits_to_keep
#       end_high   = (cnum.base + cnum.size) >> bits_to_keep
#       if start_high == end_high:
#           mask = (1ULL << bits_to_keep) - 1
#           lower_start = cnum.base & mask
#           lower_end = (cnum.base + cnum.size) & mask
#           if (lower_start <= lower_end)
#               return from_urange(lower_start, lower_end)
#       elif start_high + 1 == end_high:
#           mask = (1ULL << bits_to_keep) - 1
#           lower_start = cnum.base & mask
#           lower_end = (cnum.base + cnum.size) & mask
#           if (lower_start > lower_end)
#               return {lower_start, UT_MAX - lower_start + lower_end}
#       return UNBOUNDED
#
#   shl_const(cnum, k):               [MODIFIED return]
#       if empty(cnum)                  -> EMPTY
#       k &= T-1
#       if urange_overflow(cnum)  -> {0, UT_MAX << k}
#       bits_to_keep = T - k
#       truncated_cnum = trunc(cnum, bits_to_keep)
#       if top(truncated_cnum)          -> UNBOUNDED
#       // return {cnum.base << k, UT_MAX - ((cnum.base + cnum.size) << k) + (cnum.base << k)}
#
#   from_urange(lo, hi): if lo > hi -> EMPTY; else {base=lo, size=hi-lo}
#
#   urange_overflow(cnum):
#       false if empty or top ({0, UT_MAX})
#       true  if contains(UT_MAX) && contains(0)

from z3 import *
import time

def main():
    t0 = time.monotonic()

    T = 32
    UT_MAX_VAL = (1 << T) - 1
    UT_MAX = BitVecVal(UT_MAX_VAL, T)
    ONE = BitVecVal(1, T)
    EMPTY_base = UT_MAX
    EMPTY_size = UT_MAX
    TOP_base   = BitVecVal(0, T)
    TOP_size   = UT_MAX

    # Symbolic inputs
    ci_base = BitVec("ci_base", T)
    ci_size = BitVec("ci_size", T)
    k       = BitVec("k", T)
    x       = BitVec("x", T)

    # ---- Primitive helpers ----

    def is_empty(base, size):
        return And(base == EMPTY_base, size == EMPTY_size)

    def is_top(base, size):
        return And(base == TOP_base, size == TOP_size)

    def urange_overflow(base, size):
        return UGT(size, UT_MAX - base)

    def contains(base, size, v):
        """True iff unsigned value v is in the circular range [base, base+size]."""
        empty = is_empty(base, size)
        ov    = urange_overflow(base, size)
        sum_wrapped = (base + size) & UT_MAX
        return If(empty, False,
                  If(ov,
                     Or(UGE(v, base), ULE(v, sum_wrapped)),
                     And(UGE(v, base), ULE(v, base + size))))

    def urange_overflow(base, size):
        # [base, base+size] overflows 32-bit wrap-around
        return UGT(size, UT_MAX - base)

    # ---- Preconditions ----
    ci_empty = is_empty(ci_base, ci_size)
    ci_upper = (ci_base + ci_size) & UT_MAX   # ci.base + ci.size with C uint32 wrap

    # ---- normalize shift amount ----
    k_norm = k & BitVecVal(T - 1, T)

    # ---- urange_overflow(ci) ----
    ci_cul = urange_overflow(ci_base, ci_size)

    # ---- urange_overflow(ci) early-return path ----
    cul_res_base = BitVecVal(0, T)
    cul_res_size = UT_MAX << k_norm

    # ---- trunc(ci, bits_to_keep) ----
    bits_to_keep = T - k_norm

    start_high = LShR(ci_base, bits_to_keep)
    end_high   = LShR(ci_upper, bits_to_keep)

    mask = (ONE << bits_to_keep) - ONE
    lower_start = ci_base & mask
    lower_end   = ci_upper & mask

    # Case A: start_high == end_high, lower_start <= lower_end
    trunc_A_base = lower_start
    trunc_A_size = (lower_end - lower_start) & UT_MAX
    # from_urange behavior: if lower_end < lower_start -> EMPTY
    trunc_A_base2 = If(UGT(lower_start, lower_end), EMPTY_base, trunc_A_base)
    trunc_A_size2 = If(UGT(lower_start, lower_end), EMPTY_size, trunc_A_size)

    # Case B: start_high + 1 == end_high, lower_start > lower_end
    # C: return {lower_start, UT_MAX - lower_start + lower_end} (circular range)
    trunc_B_base = lower_start
    trunc_B_size = (UT_MAX - lower_start + lower_end) & UT_MAX

    sames_high = (start_high == end_high)
    diff_one   = (start_high + ONE == end_high)
    lower_cross = UGT(lower_start, lower_end)   # lower_start > lower_end

    # Combine: Case A -> trunc_A2; Case B -> trunc_B; else -> UNBOUNDED
    trunc_base = If(And(sames_high, Not(lower_cross)),
                    trunc_A_base2,
                    If(And(diff_one, lower_cross),
                       trunc_B_base,
                       TOP_base))
    trunc_size = If(And(sames_high, Not(lower_cross)),
                    trunc_A_size2,
                    If(And(diff_one, lower_cross),
                       trunc_B_size,
                       TOP_size))

    # ---- top(truncated_cnum) ----
    trunc_top = is_top(trunc_base, trunc_size)

    # ---- [MODIFIED] return {cnum.base << k, UT_MAX - ((cnum.base + cnum.size) << k) + (cnum.base << k)} ----
    # C uint32_t left-shift wraps: (v << k) mod 2^T
    # The C formula for new_size = UT_MAX - (ci_upper << k) + (ci_base << k)
    # works correctly only when ci_upper << k does NOT overflow.
    # When ci_upper << k overflows (wraps to < ci_base << k), the formula gives wrong results.
    # Correct formula: new_size = ((ci_upper << k) + (ci_base << k > ci_upper << k ? UT_MAX+1 : 0) - (ci_base << k)) mod 2^T
    #
    # Overflow detection: ci_upper << k overflows (in C uint32) iff ci_base >> (T-k) == 1
    # Proof: ci_upper = ci_base + ci_size. ci_upper >> (T-k) = (ci_base >> (T-k)) + (ci_size >> (T-k))
    # Since ci_size < 2^(T-k), ci_size >> (T-k) = 0. So ci_upper >> (T-k) = ci_base >> (T-k).
    # Therefore ci_upper << k overflows iff ci_base << k overflows iff ci_base >> (T-k) == 1.
    # Equivalently: ci_base > UT_MAX >> k
    both_overflow = UGT(ci_base, UT_MAX >> k_norm)

    new_base = (ci_base << k_norm) & UT_MAX
    ci_upper_shl_raw = (ci_upper << k_norm) & UT_MAX

    # When both overflow: ci_upper << k (mathematical) = ci_upper_shl_raw + 2^T
    # new_size = (ci_upper_shl_raw + (2^T) - new_base) mod 2^T
    #           = ci_upper_shl_raw - new_base (since 2^T mod 2^T = 0, but we need to account for the +2^T)
    # Actually: new_size = ((ci_upper << k) - (ci_base << k)) mod 2^T
    #         = ((ci_upper_shl_raw + overflow * 2^T) - new_base) mod 2^T
    #         = (ci_upper_shl_raw - new_base + overflow * 2^T) mod 2^T
    # When overflow=0 (no overflow): new_size = (ci_upper_shl_raw - new_base) mod 2^T
    # When overflow=1 (both overflow): new_size = (ci_upper_shl_raw - new_base + 2^T) mod 2^T
    #                              = ci_upper_shl_raw - new_base (mod 2^T), but ci_upper_shl_raw < new_base
    #                              So new_size = ci_upper_shl_raw - new_base + 2^T
    #
    # Simplified: new_size = (ci_upper_shl_raw + (both_overflow ? (UT_MAX + 1) : 0) - new_base) & UT_MAX
    adj = If(both_overflow, UT_MAX + ONE, BitVecVal(0, T))
    ci_upper_shl_adj = (ci_upper_shl_raw + adj) & UT_MAX
    new_size = (ci_upper_shl_adj - new_base) & UT_MAX

    # ---- Full shl_const result ----
    res_base = If(ci_empty, EMPTY_base,
                  If(ci_cul, cul_res_base,
                     If(trunc_top, TOP_base,
                        new_base)))
    res_size = If(ci_empty, EMPTY_size,
                  If(ci_cul, cul_res_size,
                     If(trunc_top, TOP_size,
                        new_size)))

    # ---- Theorem ----
    x_shl = (x << k_norm) & UT_MAX

    theorem = Implies(
        And(Not(ci_empty),
            contains(ci_base, ci_size, x),
            ULE(k, BitVecVal(T - 1, T))),
        contains(res_base, res_size, x_shl))

    # ---- Solver ----
    s = Solver()
    s.set("timeout", 3600000)
    s.set("threads", 16)
    s.add(Not(theorem))

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
        print(f"  ci_upper = {ev(ci_upper)}")
        print(f"  bits_to_keep = {ev(bits_to_keep)}")
        print(f"  start_high = {ev(start_high)}  end_high = {ev(end_high)}")
        print(f"  mask = {ev(mask)}")
        print(f"  lower_start = {ev(lower_start)}  lower_end = {ev(lower_end)}")
        print(f"  sames_high = {evb(sames_high)}  diff_one = {evb(diff_one)}  lower_cross = {evb(lower_cross)}")
        print(f"  trunc_base = {ev(trunc_base)}  trunc_size = {ev(trunc_size)}")
        print(f"  trunc_top  = {evb(trunc_top)}")
        print(f"  both_overflow = {evb(both_overflow)}")
        print(f"  new_base   = {ev(new_base)}  new_size = {ev(new_size)}")
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
