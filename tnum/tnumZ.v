Require Import ZArith Bool Lia.
From bpf.tnum Require Import Zmore.

Open Scope Z_scope.

Definition tnum := (Z * Z)%type.

Definition gamma (a: tnum) (x: Z) : Prop :=
   (Z.land x (Z.lnot (snd a))) = (fst a).

Definition wf_tnum (a: tnum): Prop := (Z.land (fst a) (snd a)) = 0.

Definition Z_size_Z (x: Z) : Z :=
  match x with
  | Z0 => 0
  | _ => Z.log2 (Z.abs x) + 1
  end.

Lemma gamma_0 : forall i,
  gamma (0, 0) i -> i = 0.
Proof.
  intros. unfold gamma in H; simpl in H.
  rewrite <- Z.ldiff_land in H.
  rewrite Z.ldiff_0_r in H.
  apply H.
Qed.