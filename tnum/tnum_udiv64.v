From compcert Require Import Coqlib Integers Values.
From bpf.tnum Require Import tnumZ tnumZ_inv tnumZ_udiv tnum.

(** https://www.kernel.org/doc/Documentation/bpf/standardization/instruction-set.rst
  BPF Instruction Set Architecture (ISA) - Arithmetic instructions
    - DIV: dst = (src != 0) ? (dst / src) : 0
  *)
Definition bpf_div_u64 (n1 n2:int64) : int64 :=
  if (Int64.eq n2 Int64.zero)
  then Int64.zero
  else Int64.divu n1 n2.

Definition Int64_size (x: int64) : Z :=
  Z_size_Z (Int64.unsigned x).

Definition Int64_ones (n: Z) : int64 :=
  Int64.repr (Z.ones n).

Definition tnum_udiv_64 (a b: tnum) : tnum :=
  if (Int64.eq (fst b) Int64.zero) && (Int64.eq (snd b) Int64.zero) then
    (Int64.zero, Int64.zero) (* BPF div specification: x / 0 = 0 *)
  else if (Int64.eq (snd a) Int64.zero) && (Int64.eq (snd b) Int64.zero) then
    (Int64.divu (fst a) (fst b), Int64.zero) (* concrete udiv *)
  else if (Int64.eq (fst b) Int64.zero) then
    (Int64.zero, Int64.mone) (* -1 represents unsigned_max *)
  else let max_res := Int64.divu (Int64.add (fst a) (snd a)) (fst b) in
    (Int64.zero, Int64_ones (Int64_size max_res)).

Lemma testbit_divu : forall i x y,
    0 <= i < Int64.zwordsize ->
    Int64.testbit (Int64.divu x y) i =
      Z.testbit (Z.div (Int64.unsigned x) (Int64.unsigned y)) i.
Proof.
  intros. unfold Int64.divu.
  rewrite Int64.testbit_repr by auto.
  reflexivity.
Qed.

Lemma tnum_udiv_eq : forall (a b : tnum),
    Int64.unsigned (fst a) + Int64.unsigned (snd a) <= Int64.max_unsigned ->
    tnum_udiv_64 a b =
      of_tnumZ (tnumZ_udiv.tnum_udiv (to_tnumZ a) (to_tnumZ b)).
Proof.
  intros. unfold tnum_udiv_64, tnumZ_udiv.tnum_udiv. simpl.
  rewrite !Int64_eq_unsigned. rewrite Int64.unsigned_zero.
  destruct ((Int64.unsigned (fst b) =? 0) && (Int64.unsigned (snd b) =? 0)).
  { reflexivity. }
  destruct ((Int64.unsigned (snd a) =? 0) && (Int64.unsigned (snd b) =? 0)).
  { reflexivity. }
  destruct (Int64.unsigned (fst b) =? 0) eqn:Hb_v0.
  { reflexivity. }
  unfold of_tnumZ. f_equal. simpl.
  unfold Int64_ones, Int64_size, Int64.divu.
  rewrite Int64_unsigned_add; try lia.
  rewrite Int64.unsigned_repr. reflexivity.
  pose proof (Int64.unsigned_range (fst b)).
  pose proof (Int64_unsigned_add_nonneg (fst a) (snd a)).
  split.
  - apply Z_div_nonneg_nonneg; lia.
  - apply Z.le_trans with (m := Int64.unsigned (fst a) + Int64.unsigned (snd a)).
    2:{ apply H. }
    rewrite <- Z.div_1_r.
    apply Z.div_le_compat_l; lia.
Qed.

Theorem tnum_binary_sound_ge_0 :
  forall a b i j f fz tnum_f tnum_fz
         (TNUM_FZ_SOUND : forall a i b j,
            tnum_ge_inv a -> tnum_ge_inv b ->
              gamma a i -> gamma b j -> gamma (tnum_fz a b) (fz i j))
         (FFZ : forall n, 0 <= n < Int64.zwordsize ->
            forall i j, (Int64.testbit (f i j) n =
              Z.testbit (fz (Int64.unsigned i) (Int64.unsigned j)) n))
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true)
         (EQ : tnum_f a b = of_tnumZ (tnum_fz (to_tnumZ a) (to_tnumZ b)))
  ,
    mem_tnum (f i j) (tnum_f a b) = true.
Proof.
  intros.
  apply mem_tnum_gamma in MEMA.
  apply mem_tnum_gamma in MEMB.
  rewrite EQ.
  specialize (TNUM_FZ_SOUND _ _ _ _ GEA GEB MEMA MEMB).
  revert TNUM_FZ_SOUND.
  unfold to_tnumZ.
  generalize (Int64.unsigned (fst a), Int64.unsigned (snd a)) as az.
  generalize (Int64.unsigned (fst b), Int64.unsigned (snd b)) as bz.
  intros bz az.
  generalize (tnum_fz az bz) as r.
  destruct r.
  unfold gamma. simpl in *. intros. subst.
  unfold mem_tnum.
  simpl.
  apply int64_eq_if_same.
  apply Int64.same_bits_eq.
  intros.
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_and by auto.
  rewrite Z.land_spec.
  rewrite Z.lnot_spec by lia.
  rewrite Int64.bits_not by auto.
  rewrite! Int64.testbit_repr by auto.
  rewrite FFZ. reflexivity.
  auto.
Qed.

Theorem tnum_udiv_sound :
  forall a b i j
         (GEA : tnum_ge_inv (to_tnumZ a))
         (GEB : tnum_ge_inv (to_tnumZ b))
         (MEMA : mem_tnum i a = true)
         (MEMB : mem_tnum j b = true),
    mem_tnum (bpf_div_u64 i j) (tnum_udiv_64 a b) = true.
Proof.
  intros.
  unfold bpf_div_u64.
  destruct (Int64.eq j Int64.zero) eqn:EQ.
  - assert (Int64.eq (fst b) Int64.zero = true).
    { unfold mem_tnum in MEMB.
      apply Int64.same_if_eq in EQ.
      rewrite EQ in MEMB.
      rewrite Int64.and_zero_l in MEMB.
      rewrite Int64.eq_sym. apply MEMB. }
    unfold tnum_udiv_64. rewrite H. rewrite andb_true_l.
    destruct (Int64.eq (snd b) Int64.zero).
    { reflexivity. }
    rewrite andb_false_r. reflexivity.
  - apply tnum_binary_sound_ge_0
      with (tnum_fz := tnumZ_udiv.tnum_udiv) (fz:= Z.div); auto.
    + intros. apply tnumZ_udiv.tnum_udiv_sound; auto.
    + intros. apply testbit_divu ; auto.
    + apply tnum_udiv_eq; auto. apply (mem_tnum_range _ _ MEMA).
Qed.