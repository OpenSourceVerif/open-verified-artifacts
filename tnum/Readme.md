# TNum (Tristate Numbers)

## Structure

Basic files:

* `Zmore.v`: Custom Lemmas about Rocq's ZArith.
* `tnumZ.v`: TNum definition on Rocq's ZArith.
* `tnumZ_inv`: Some lemmas based on 'TNum >= 0'.
* `tnum.v`: TNum definition (64-bits) on CompCert Interger.
* `tnum32.v`: TNum definition (32-bits) on CompCert Interger.

Unsigned division:

* `tnumZ_udiv`: Unsigned division definition and proof on Rocq's ZArith.
* `tnum_udiv64`: Unsigned division definition and proof on CompCert Interger 64.
* `tnum_udiv32`: Unsigned division definition and proof on CompCert Interger 32.