namespace BitVec

instance : Min (BitVec w) where
    min a b := if a < b then a else b

instance : Max (BitVec w) where
    max a b := if a < b then a else b

def smax (a b : BitVec w) := if a.slt b then b else a
def smin (a b : BitVec w) := if a.sle b then a else b

end BitVec
