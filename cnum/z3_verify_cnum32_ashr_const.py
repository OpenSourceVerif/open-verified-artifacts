"""
Z3 proof for cnum32_ashr_const:
    Theorem: ci non-empty, x in ci  implies  signed(x) >>(k&31) in ashr_const(ci, k)

C source (ashr_const, cnum_def.h lines 335-350):
    struct cnum_t ashr_const(cnum, k):
        if is_empty(cnum) return EMPTY
        k &= T-1
        if srange_overflow(cnum) return from_srange(ST_MIN>>k, ST_MAX>>k)
        st min = (st)cnum.base >> k
        st max = (st)(cnum.base + cnum.size) >> k
        return from_srange(min, max)
"""

from z3 import *
import time


def main():
    t0 = time.monotonic()

    T = 32
    UT_MAX_VAL = (1 << T) - 1
    UT_MAX = BitVecVal(UT_MAX_VAL, T)
    ST_MAX_VAL = (1 << (T - 1)) - 1
    ST_MIN_VAL = -(1 << (T - 1))
    EMPTY_base_val = UT_MAX_VAL
    EMPTY_size_val = UT_MAX_VAL

    ci_base = BitVec('ci_base', T)
    ci_size = BitVec('ci_size', T)
    k       = BitVec('k', T)
    x       = BitVec('x', T)

    # ------------------------------------------------------------------
    # 1. Signed comparison: interpret a BitVec as a signed T-bit integer
    # ------------------------------------------------------------------
    def to_signed(bv):
        return SignExt(T, bv)

    def s_lt(a, b):
        return to_signed(a) < to_signed(b)

    def s_le(a, b):
        return to_signed(a) <= to_signed(b)

    def s_gt(a, b):
        return to_signed(a) > to_signed(b)

    def s_ge(a, b):
        return to_signed(a) >= to_signed(b)

    # ------------------------------------------------------------------
    # 2. Signed arithmetic right shift (T-bit values, shift < T)
    #    Use SignExt(T, value) -> 2T bits, then LShR with ZeroExt'd shift
    # ------------------------------------------------------------------
    def s_shr(value, shift):
        ext    = SignExt(T, value)
        ext_sh = ZeroExt(T, shift)
        return Extract(T - 1, 0, LShR(ext, ext_sh))

    # ------------------------------------------------------------------
    # 3. C helper predicates
    # ------------------------------------------------------------------
    def is_empty(b, s):
        return And(b == EMPTY_base_val, s == EMPTY_size_val)

    def contains(b, s, v):
        ov = UGT(s, UT_MAX - b)
        return If(ov,
                  Or(UGE(v, b), ULE(v, b + s)),
                  And(UGE(v, b), ULE(v, b + s)))

    def srange_overflow(base, size):
        return And(contains(base, size, ST_MAX_VAL), contains(base, size, ST_MIN_VAL))

    def from_srange(min_s, max_s):
        # Signed comparison: wrapped if min_s > max_s (as signed T-bit values)
        wrapped = s_gt(min_s, max_s)
        # size = max_s - min_s (unsigned 32-bit subtraction, matching C semantics)
        size = (max_s - min_s) & UT_MAX
        # Full range: size == UT_MAX -> TOP (base=0, size=UT_MAX)
        is_full = size == UT_MAX - BitVecVal(1, T)
        # For normal ranges: base = min_s & UT_MAX, size = computed size
        # For wrapped ranges (min_s > max_s): same formula applies
        # (unsigned subtraction gives the total span across the wrap boundary)
        base = min_s & UT_MAX
        sz   = If(is_full, UT_MAX, size)
        return base, sz

    # ------------------------------------------------------------------
    # 4. Model the C ashr_const
    # ------------------------------------------------------------------
    ci_empty = is_empty(ci_base, ci_size)
    ci_csl   = srange_overflow(ci_base, ci_size)

    k_norm = k & BitVecVal(T - 1, T)

    # Branch 1: srange_overflow -> from_srange(ST_MIN>>k, ST_MAX>>k)
    st_min = BitVecVal(ST_MIN_VAL, T)
    st_max = BitVecVal(ST_MAX_VAL, T)
    csl_min = s_shr(st_min, k_norm)
    csl_max = s_shr(st_max, k_norm)
    csl_res_b, csl_res_s = from_srange(csl_min, csl_max)

    # Branch 2: otherwise -> from_srange((st)base>>k, (st)(base+size)>>k)
    base_signed_shr = s_shr(ci_base, k_norm)
    upper = (ci_base + ci_size) & UT_MAX
    upper_signed_shr = s_shr(upper, k_norm)
    norm_res_b, norm_res_s = from_srange(base_signed_shr, upper_signed_shr)

    res_b = If(ci_empty, EMPTY_base_val,
               If(ci_csl, csl_res_b, norm_res_b))
    res_s = If(ci_empty, EMPTY_size_val,
               If(ci_csl, csl_res_s, norm_res_s))

    # ------------------------------------------------------------------
    # 5. Theorem: ci non-empty, x in ci  =>  signed(x)>>(k&31) in ashr_const(ci,k)
    # ------------------------------------------------------------------
    x_shr = s_shr(x, k_norm)

    theorem = Implies(
        And(contains(ci_base, ci_size, x)),
        contains(res_b, res_s, x_shr))

    s = Solver()
    s.set("timeout", 3600000)
    s.set("threads", 16)
    s.add(Not(theorem))

    print("Verifying cnum32_ashr_const (1hr timeout, 16 threads)...")
    print("Theorem: ci non-empty, x in ci")
    print("         implies signed(x) >>(k&31) in ashr_const(ci, k)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        m = s.model()
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        return 1
    elif result == unsat:
        print("PASS: cnum32_ashr_const verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2


if __name__ == "__main__":
    exit(main())
