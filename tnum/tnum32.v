From compcert Require Import Coqlib Integers Values.
Require Import Zmore tnumZ.

Definition tnum: Type := int * int.

Definition mem_tnum (x: int) (a: tnum): bool :=
  Int.eq (Int.and x (Int.not (snd a))) (fst a).

Definition wf_tnum (a: tnum): Prop :=
  (Int.and (fst a) (snd a) = Int.zero).

Lemma int_eq_if_same:
  forall x y : int, x = y <-> Int.eq x y = true.
Proof.
  intros.
  generalize (Int.eq_spec x y).
  destruct (Int.eq x y); intuition congruence.
Qed.

Lemma mem_imply_wf: forall va ma i,
  mem_tnum i (va, ma) = true ->
  wf_tnum (va, ma).
Proof.
  unfold mem_tnum, wf_tnum; simpl.
  intros va ma i Hg.
  apply int_eq_if_same in Hg.
  subst.
  rewrite Int.and_assoc.
  rewrite Int.and_commut with (y := ma).
  rewrite Int.and_not_self.
  apply Int.and_zero.
Qed.

Definition to_tnumZ (x: tnum) :=
  (Int.unsigned (fst x), Int.unsigned (snd x)).

Definition of_tnumZ (x: tnumZ.tnum) :=
  (Int.repr (fst x), Int.repr (snd x)).

Lemma Zland_and : forall x y,
    Z.land (Int.unsigned x) (Int.unsigned y) = Int.unsigned (Int.and x y).
Proof.
  intros.
  unfold Int.and.
  rewrite Int.unsigned_repr_eq.
  rewrite Z.mod_small.
  split.
  rewrite Z.land_nonneg.
  assert (Rx := Int.unsigned_range x).
  assert (Ry := Int.unsigned_range y).
  split.
  - lia.
  - eapply Z.le_lt_trans.
    apply Zland_ub. lia.
    lia. lia.
Qed.

Lemma Zlnot_not : forall x,
    forall n , 0 <= n < Int.zwordsize ->
    Z.testbit (Z.lnot (Int.unsigned x)) n = Z.testbit (Int.unsigned (Int.not x)) n.
Proof.
  intros.
  change (Z.testbit (Int.unsigned (Int.not x)))
    with  (Int.testbit (Int.not x)).
  rewrite Int.bits_not by lia.
  rewrite Z.lnot_spec by lia.
  reflexivity.
Qed.

Lemma mem_tnum_gamma : forall i a,
    mem_tnum i a = true ->
    gamma (to_tnumZ a) (Int.unsigned i).
Proof.
  unfold mem_tnum,gamma.
  intros.
  rewrite <- int_eq_if_same in H.
  unfold to_tnumZ.
  rewrite <- H.
  simpl.
  rewrite <- Zland_and.
  apply Z.bits_inj.
  unfold Z.eqf. intros.
  rewrite! Z.land_spec.
  change (Z.testbit (Int.unsigned i) n) with (Int.testbit i n).
  assert (n < 0 \/ n >= Int.zwordsize \/ 0 <= n < Int.zwordsize) by lia.
  destruct H0 as [N | [N | N]].
  - rewrite Int.bits_below by lia.
    reflexivity.
  - rewrite Int.bits_above by lia.
    reflexivity.
  - f_equal.
    apply Zlnot_not;auto.
Qed.

Lemma Int_unsigned_add_nonneg : forall (x y : int),
  0 <= Int.unsigned x + Int.unsigned y.
Proof.
  intros. apply Z.add_nonneg_nonneg; apply Int.unsigned_range.
Qed.

Lemma Int_unsigned_add : forall (x y : int),
  Int.unsigned x + Int.unsigned y <= Int.max_unsigned ->
  Int.unsigned (Int.add x y) = Int.unsigned x + Int.unsigned y.
Proof.
  intros. unfold Int.add.
  rewrite Int.unsigned_repr. reflexivity.
  pose proof (Int_unsigned_add_nonneg x y).
  lia.
Qed.

Lemma Int_eq_unsigned : forall x y,
  Int.eq x y = Z.eqb (Int.unsigned x) (Int.unsigned y).
Proof.
  intros. unfold Int.eq.
  destruct (Z.eqb_spec (Int.unsigned x) (Int.unsigned y)) as [E|E].
  - rewrite E. rewrite Coqlib.zeq_true. reflexivity.
  - rewrite Coqlib.zeq_false; lia.
Qed.

Lemma mem_tnum_range: forall x a, mem_tnum x a = true ->
  Int.unsigned (fst a) + Int.unsigned (snd a) <= Int.max_unsigned.
Proof.
  intros. apply mem_imply_wf in H. clear x.
  unfold wf_tnum in H; simpl in H.
  assert (Int.unsigned (Int.and (fst a) (snd a)) = Int.unsigned (Int.zero)).
  { f_equal. apply H. }
  rewrite <- Zland_and in H0.
  rewrite Int.unsigned_zero in H0.
  apply (Z.add_nocarry_lt_pow2 _ _ 32) in H0.
  - unfold Int.max_unsigned; simpl. lia.
  - apply Int.unsigned_range.
  - apply Int.unsigned_range.
Qed.
