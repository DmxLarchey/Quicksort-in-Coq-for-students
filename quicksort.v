Require Import Arith List Bool Omega Extraction.

Require Import list_utils perm sorted.

Section quicksort.

  Fixpoint pivot x m :=
    match m with 
      | nil   => (nil,nil)
      | y::m' => let (l,r) := pivot x m'
                 in if y <b x then (y::l,r) else (l,y::r)
    end.

  Proposition pivot_spec x m : let (l,r) := pivot x m 
                               in m ~p l++r 
                               /\ ub l x = true
                               /\ lb r (S x) = true.
  Proof.
    induction m as [ | y m IHm ]; simpl; auto.
    destruct (pivot x m) as (l,r).
    destruct IHm as (H1 & H2 & H3).
    case_eq (y <b x); intros H.
    + split; simpl; auto.
      split; auto.
      apply andb_true_iff; split; auto.
    + split; auto.
      split; auto.
      destruct y as [ | y ]; simpl.
      * apply Nat.leb_nle in H; omega.
      * apply andb_true_iff; split; auto.
        apply Nat.leb_le.
        apply Nat.leb_nle in H; omega.
  Qed.

  Let pivot_type x m (piv : list nat * list nat) := let (l,r) := piv in m ~p l++r /\ ub l x = true /\ lb r x = true.
    
  Proposition pivot_prop x m : pivot_type x m (pivot x m).
  Proof.
    generalize (pivot_spec x m).
    destruct (pivot x m) as (l,r).
    intros (? & ? & ?); repeat split; auto.
    revert H1; apply lb_inc, le_bool_le; auto.
  Qed.

  Section qs.

    Inductive qs_graph : list nat -> list nat -> Prop :=
      | in_qsg_0 : qs_graph nil nil
      | in_qsg_1 : forall x m l r, qs_graph (fst (pivot x m)) l
                                -> qs_graph (snd (pivot x m)) r
                                -> qs_graph (x::m) (l++x::r).

    Let qs_rec m : sig (qs_graph m).
    Proof.
      induction m as [ m IH ] using (measure_rect _ (@length _)); revert IH.
      refine  (match m with 
        | nil  => fun IH =>       exist _ nil _
        | x::m => fun IH => 
        match pivot x m as piv return pivot x m = piv -> _ with
          | (l,r) => fun E => let (l',G1) := IH l _ in
                              let (r',G3) := IH r _ 
                              in  exist _ (l'++x::r') _
        end eq_refl
      end); try (constructor; fail); generalize (pivot_prop x m); rewrite E.
      + intros (H & _); apply perm_length in H; simpl; rewrite H, app_length; omega.
      + intros (H & _); apply perm_length in H; simpl; rewrite H, app_length; omega.
      + intros (H1 & H2 & H3); constructor; rewrite E; simpl; auto.
    Qed.

    Definition qs m := proj1_sig (qs_rec m).

    Fact qs_spec m : qs_graph m (qs m).
    Proof. apply (proj2_sig _). Qed.

    Fact qs_correct m : m ~p qs m /\ sorted (qs m).
    Proof.
      generalize (qs m) (qs_spec m).
      induction 1 as [ | x m l' r' H1 (G1 & G2) H2 (G3 & G4) ]; auto.
      generalize (pivot_prop x m); destruct (pivot x m) as (l,r); simpl in *.
      intros (H3 & H4 & H5); split.
      + apply perm_special, perm_trans with (1 := H3); auto.
      + apply quick_sorted; auto.
        * revert H4; apply ub_incl, perm_incl, perm_sym; auto.
        * revert H5; apply lb_incl, perm_incl, perm_sym; auto.
    Qed.

  End qs.

  Definition quicksort m : { k | m ~p k /\ sorted k }.
  Proof.
    induction m as [ m IH ] using (measure_rect _ (@length _)); revert IH.
    refine (match m with 
      | nil  => fun IH =>       exist _ nil _
      | x::m => fun IH => 
      match pivot x m as piv return pivot_type x m piv -> _ with
        | (l,r) => fun H => let (l',G1) := IH l _ in
                            let (r',G3) := IH r _ 
                            in  exist _ (l'++x::r') _

      end (pivot_prop x m)
    end).
    1,2,3 : cycle 1.

    (* Termination certificates *)

    + apply proj1, perm_length in H; simpl; rewrite H, app_length; omega.
    + apply proj1, perm_length in H; simpl; rewrite H, app_length; omega.

    (* Post-conditions *)

    + split; auto; constructor.
    + destruct H as (H1 & H2 & H3).
      destruct G1 as (G1 & G2).
      destruct G3 as (G3 & G4). 
      split.
      - apply perm_special, perm_trans with (1 := H1); auto.
      - apply quick_sorted; auto.
        * revert H2; apply ub_incl, perm_incl, perm_sym; auto.
        * revert H3; apply lb_incl, perm_incl, perm_sym; auto.
  Defined.

  (* quick_sort_rec : by induction on the length n of the list m *)

  Definition quick_sort_rec : nat -> list nat -> list nat := fix loop n m := 
    match n, m with 
      | O  , _    => nil
      | S n, nil  => nil
      | S n, x::m => let (l,r) := pivot x m
                     in  (loop n l)++x::(loop n r)
    end.

  (* assuming m has length lower than n, then it is correctly sorted by quick_sort_rec 
     ie quick_sort_rec n m is a permutation of m which is sorted 
  *)

  Proposition quick_sort_rec_prop n m : length m <= n -> m ~p quick_sort_rec n m /\ sorted (quick_sort_rec n m).
  Proof.
    revert n; induction m as [ [ | x m ] IHm ] using (measure_rect _ (@length _)). 
    + destruct n; simpl; split; auto.
    + intros [ | n ] Hn; simpl in Hn |- *; try omega.
      generalize (pivot_prop x m).
      destruct (pivot x m) as (l,r).
      intros (H1 & H2 & H3).
      generalize (perm_length H1); rewrite app_length; intros H4.
      destruct (IHm l) with (n := n) as (H5 & H6); try (simpl; omega).
      destruct (IHm r) with (n := n) as (H7 & H8); try (simpl; omega).
      split; auto.
      * apply perm_special, perm_trans with (1 := H1), perm_app; auto.
      * apply quick_sorted; auto; 
          [ revert H2; apply ub_incl | revert H3; apply lb_incl ]; 
          apply perm_incl, perm_sym; auto.
  Qed.

  (* compute the length of m before calling quick_sort_rec *)
 
  Definition quick_sort m := quick_sort_rec (S (length m)) m.

  Proposition quick_sort_prop m : m ~p quick_sort m /\ sorted (quick_sort m).
  Proof. apply quick_sort_rec_prop; auto. Qed.

End quicksort.

Extraction Inline quick_sort_rec.

Recursive Extraction quicksort quick_sort qs.

Check qs_correct.
Check quicksort.

Eval compute in quick_sort (2::3::1::8::1::10::3::5::2::nil).


    
    