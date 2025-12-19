From compcert Require Import Coqlib Integers Values.
Require Import Zmore tnumZ.

Definition tnum: Type := int64 * int64.

Definition mem_tnum (x: int64) (a: tnum): bool :=
  Int64.eq (Int64.and x (Int64.not (snd a))) (fst a).

Definition wf_tnum (a: tnum): Prop :=
  (Int64.and (fst a) (snd a) = Int64.zero).

Lemma int64_eq_if_same:
  forall x y : int64, x = y <-> Int64.eq x y = true.
Proof.
  intros.
  generalize (Int64.eq_spec x y).
  destruct (Int64.eq x y); intuition congruence.
Qed.

Lemma mem_imply_wf: forall va ma i,
  mem_tnum i (va, ma) = true ->
  wf_tnum (va, ma).
Proof.
  unfold mem_tnum, wf_tnum; simpl.
  intros va ma i Hg.
  apply int64_eq_if_same in Hg.
  subst.
  rewrite Int64.and_assoc.
  rewrite Int64.and_commut with (y := ma).
  rewrite Int64.and_not_self.
  apply Int64.and_zero.
Qed.

Definition to_tnumZ (x: tnum) :=
  (Int64.unsigned (fst x), Int64.unsigned (snd x)).

Definition of_tnumZ (x: tnumZ.tnum) :=
  (Int64.repr (fst x), Int64.repr (snd x)).

Lemma Zland_and : forall x y,
    Z.land (Int64.unsigned x) (Int64.unsigned y) = Int64.unsigned (Int64.and x y).
Proof.
  intros.
  unfold Int64.and.
  rewrite Int64.unsigned_repr_eq.
  rewrite Z.mod_small.
  split.
  rewrite Z.land_nonneg.
  assert (Rx := Int64.unsigned_range x).
  assert (Ry := Int64.unsigned_range y).
  split.
  - lia.
  - eapply Z.le_lt_trans.
    apply Zland_ub. lia.
    lia. lia.
Qed.

Lemma Zlnot_not : forall x,
    forall n , 0 <= n < Int64.zwordsize ->
    Z.testbit (Z.lnot (Int64.unsigned x)) n = Z.testbit (Int64.unsigned (Int64.not x)) n.
Proof.
  intros.
  change (Z.testbit (Int64.unsigned (Int64.not x)))
    with  (Int64.testbit (Int64.not x)).
  rewrite Int64.bits_not by lia.
  rewrite Z.lnot_spec by lia.
  reflexivity.
Qed.

Lemma mem_tnum_gamma : forall i a,
    mem_tnum i a = true ->
    gamma (to_tnumZ a) (Int64.unsigned i).
Proof.
  unfold mem_tnum,gamma.
  intros.
  rewrite <- int64_eq_if_same in H.
  unfold to_tnumZ.
  rewrite <- H.
  simpl.
  rewrite <- Zland_and.
  apply Z.bits_inj.
  unfold Z.eqf. intros.
  rewrite! Z.land_spec.
  change (Z.testbit (Int64.unsigned i) n) with (Int64.testbit i n).
  assert (n < 0 \/ n >= Int64.zwordsize \/ 0 <= n < Int64.zwordsize) by lia.
  destruct H0 as [N | [N | N]].
  - rewrite Int64.bits_below by lia.
    reflexivity.
  - rewrite Int64.bits_above by lia.
    reflexivity.
  - f_equal.
    apply Zlnot_not;auto.
Qed.

Lemma Int64_unsigned_add_nonneg : forall (x y : int64),
  0 <= Int64.unsigned x + Int64.unsigned y.
Proof.
  intros. apply Z.add_nonneg_nonneg; apply Int64.unsigned_range.
Qed.

Lemma Int64_unsigned_add : forall (x y : int64),
  Int64.unsigned x + Int64.unsigned y <= Int64.max_unsigned ->
  Int64.unsigned (Int64.add x y) = Int64.unsigned x + Int64.unsigned y.
Proof.
  intros. unfold Int64.add.
  rewrite Int64.unsigned_repr. reflexivity.
  pose proof (Int64_unsigned_add_nonneg x y).
  lia.
Qed.

Lemma Int64_eq_unsigned : forall x y,
  Int64.eq x y = Z.eqb (Int64.unsigned x) (Int64.unsigned y).
Proof.
  intros. unfold Int64.eq.
  destruct (Z.eqb_spec (Int64.unsigned x) (Int64.unsigned y)) as [E|E].
  - rewrite E. rewrite Coqlib.zeq_true. reflexivity.
  - rewrite Coqlib.zeq_false; lia.
Qed.

Lemma mem_tnum_range: forall x a, mem_tnum x a = true ->
  Int64.unsigned (fst a) + Int64.unsigned (snd a) <= Int64.max_unsigned.
Proof.
  intros. apply mem_imply_wf in H. clear x.
  unfold wf_tnum in H; simpl in H.
  assert (Int64.unsigned (Int64.and (fst a) (snd a)) = Int64.unsigned (Int64.zero)).
  { f_equal. apply H. }
  rewrite <- Zland_and in H0.
  rewrite Int64.unsigned_zero in H0.
  apply (Z.add_nocarry_lt_pow2 _ _ 64) in H0.
  - unfold Int64.max_unsigned; simpl. lia.
  - apply Int64.unsigned_range.
  - apply Int64.unsigned_range.
Qed.
