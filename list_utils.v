Require Import List Omega Wellfounded Extraction.

Definition app_split { X : Type } (l1 l2 r1 r2 : list X) : 
   l1++r1 = l2++r2 -> (exists m, l2 = l1++m /\ r1 = m++r2) 
                   \/ (exists m, l1 = l2++m /\ r2 = m++r1).
Proof.
  revert l2 r1 r2.
  induction l1 as [ | x l1 Hl1 ].
  left; exists l2; auto.
  intros [ | y l2 ] r1 r2 H.
  right; exists (x::l1); auto.
  simpl in H; injection H; clear H; intros H ?; subst.
  apply Hl1 in H.
  destruct H as [ (m & H1 & H2) | (m & H1 & H2) ].
  left; exists m; subst; auto.
  right; exists m; subst; auto.
Qed.

Section measure_ind.

  Variable (X : Type) (m : X -> nat) (P : X -> Type)
           (HP : forall x, (forall y, m y < m x -> P y) -> P x).

  Let R x y := m x < m y.

  Theorem measure_rect x : P x.
  Proof.
    cut (Acc R x).
    + revert x.
      exact (fix loop x Hx { struct Hx } := HP x (fun y Hy => loop y (Acc_inv Hx Hy))).
    + unfold R; apply wf_inverse_image, lt_wf.
  Qed.

End measure_ind.

Section measure_double_ind.

  Variable (X Y : Type) (m : X -> Y -> nat) (P : X -> Y -> Type)
           (HP : forall x y, (forall x' y', m x' y' < m x y -> P x' y') -> P x y).

  Let R c d := m (fst c) (snd c) < m (fst d) (snd d).

  Theorem measure_double_rect x y : P x y.
  Proof.
    cut (Acc R (x,y)).
    + revert x y.
      refine (fix loop x y H { struct H } := HP x y (fun x' y' H' => loop x' y' (Acc_inv H _))).
      apply H'.
    + unfold R; apply wf_inverse_image, lt_wf.
  Qed.

End measure_double_ind.

Extraction Inline measure_double_rect.
Extraction Inline measure_rect.