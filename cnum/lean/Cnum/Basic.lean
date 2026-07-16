import Cnum.BitVec
import Std.Tactic.BVDecide
import Lean.LibrarySuggestions.Default

structure Cnum (w : Nat) [NeZero w] where
    base : BitVec w
    size : BitVec w
    deriving DecidableEq, Repr

namespace Cnum

variable {w : Nat} [NeZero w]

abbrev ST_MIN := BitVec.intMin w
abbrev ST_MAX := BitVec.intMax w
abbrev UT_MIN := BitVec.zero w
abbrev UT_MAX := BitVec.allOnes w

def unbounded : Cnum w := ⟨0, UT_MAX⟩
def empty : Cnum w := ⟨UT_MAX, UT_MAX⟩

abbrev is_empty (cnum : Cnum w) : Prop :=
    cnum = empty

abbrev urange_overflow (cnum : Cnum w) : Prop :=
    cnum.size > UT_MAX - cnum.base

abbrev contains (cnum : Cnum w) (v : BitVec w) : Prop := 
    if is_empty cnum then
        false
    else if urange_overflow cnum then
        v ≥ cnum.base || v ≤ cnum.base + cnum.size
    else
        v ≥ cnum.base && v ≤ cnum.base + cnum.size

abbrev contains_new (cnum : Cnum w) (v : BitVec w) : Prop := 
    cnum != empty && v - cnum.base ≤ cnum.size

theorem contains_eq (cnum : Cnum 64) :
    cnum.contains = cnum.contains_new := by
    ext v
    dsimp [contains, contains_new]
    split
    · case isTrue hempty =>
      simp
      intro hc
      contradiction
    · case isFalse hnempty =>
      split
      · case isTrue hoverflow =>
        simp
        constructor
        · intro h
          cases h <;> grind
        · intro h; grind
      · case isFalse hnoverflow =>
        simp
        constructor <;> grind

abbrev srange_overflow (cnum : Cnum w) : Prop :=
    cnum.contains ST_MAX && cnum.contains ST_MIN

def smin (cnum : Cnum w) : BitVec w :=
    if cnum.srange_overflow then
        ST_MIN
    else
        cnum.base.smin (cnum.base + cnum.size)

def smin_new (cnum : Cnum w) : BitVec w :=
    if cnum.srange_overflow then ST_MIN else cnum.base

theorem smin_eq (cnum : Cnum 64) :
    cnum.smin = cnum.smin_new := by
    dsimp [smin, smin_new]
    split
    · rfl
    · case isFalse hnoverflow =>
      dsimp [BitVec.smin]
      split
      · rfl
      · case isFalse h_base_le_base_plus_size =>
        simp
        cases cnum
        sorry


def smax (cnum : Cnum w) : BitVec w :=
    if cnum.srange_overflow then
        ST_MAX
    else
        cnum.base.smax (cnum.base + cnum.size)

def smax_new (cnum : Cnum w) : BitVec w :=
    if cnum.srange_overflow then ST_MAX else cnum.base + cnum.size

theorem smax_eq (cnum : Cnum 64) :
    cnum.smax = cnum.smax_new := by
    dsimp [smax, smax_new]
    split
    · rfl
    · case isFalse hnoverflow =>
      dsimp [BitVec.smax]
      split
      · rfl
      · case isFalse h_base_lt_base_plus_size =>
        simp
        cases cnum
        sorry

def normalize (cnum : Cnum w) : Cnum w :=
    if cnum.size == UT_MAX && cnum.base != 0 && cnum.base != ST_MAX then
        ⟨0, cnum.size⟩
    else
        cnum

def normalize_new (cnum : Cnum w) : Cnum w :=
    if cnum.size == UT_MAX && cnum.base != 0 then
        ⟨0, cnum.size⟩
    else
        cnum

theorem normalize_equiv (cnum : Cnum 64) (v : BitVec 64) :
    cnum.normalize.contains v = cnum.normalize_new.contains v := by
    rw [contains_eq (cnum.normalize), contains_eq (cnum.normalize_new)]
    dsimp [normalize, normalize_new, contains_new]
    split
    · case isTrue hnorm =>
      split
      · rfl
      · case isFalse hnew =>
        simp at hnorm hnew
        grind
    · case isFalse hnnorm =>
      split
      · case isTrue hnew =>
        simp at hnnorm hnew
        have hbase : cnum.base = ST_MAX := by grind
        have hsize : cnum.size = UT_MAX := by grind
        rw [hbase, hsize]
        cases cnum
        simp at *
        dsimp [UT_MAX, ST_MAX, empty] at *
        bv_decide
      · rfl

end Cnum
