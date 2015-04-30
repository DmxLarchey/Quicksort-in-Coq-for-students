Require Import Arith.
Require Import List.
Require Import Bool.

Require Import list_utils.
Require Import perm.
Require Import sorted.

Section quicksort.

  Fixpoint pivot x m :=
    match m with 
      | nil  => (nil,nil)
      | y::m => let (l,r) := pivot x m
                in if y <b x then (y::l,r) else (l,y::r)
    end.

  Proposition pivot_spec x m : let (l,r) := pivot x m 
                               in m ~p l++r 
                               /\ ub l x = true
                               /\ lb r (S x) = true.
  Proof.
    induction m as [ | y m IHm ]; simpl.

    repeat split; auto.
    apply perm_nil.

    destruct (pivot x m) as (l,r).
    destruct IHm as (H1 & H2 & H3).
    case_eq (y <b x); intros H.
  Admitted.
    
  Proposition pivot_prop x m : let (l,r) := pivot x m 
                               in m ~p l++r 
                               /\ ub l x = true
                               /\ lb r x = true.
  Proof.
    generalize (pivot_spec x m).
    destruct (pivot x m) as (l,r).
    intros ( ? & ? & ? ); repeat split; auto.
    revert H1; apply lb_inc.
    apply le_bool_le.
    auto.
  Qed.

  (* quick_sort_rec : by induction on the length n of the list m *)

  Fixpoint quick_sort_rec n m := 
    match n, m with 
      | O  , _    => nil
      | S n, nil  => nil
      | S n, x::m => let (l,r) := pivot x m
                     in  (quick_sort_rec n l)++x::(quick_sort_rec n r)
    end.

  (* assuming m has length lower than n, then it is correctly sorted by quick_sort_rec 
     ie quick_sort_rec n m is a permutation of m which is sorted 
  *)

  Proposition quick_sort_rec_prop n : forall m, length m < n -> m ~p quick_sort_rec n m 
                                                             /\ sorted (quick_sort_rec n m).
  Proof.
    induction n as [ | n IHn ]; intros [ | x m ] Hm; simpl; auto; simpl in Hm;
    try (apply lt_n_O in Hm; elim Hm).

    split; auto.
    apply perm_nil.

    generalize (pivot_prop x m).
    destruct (pivot x m) as (l,r).
    intros ( H1 & H2 & H3 ).
    apply lt_S_n in Hm.

    destruct (IHn l) as (H4 & H5).
 
  Admitted.

  (* compute the length of m before calling quick_sort_rec *)
 
  Definition quick_sort m := quick_sort_rec (S (length m)) m.

  Proposition quick_sort_prop m : m ~p quick_sort m /\ sorted (quick_sort m).
  Proof.
    apply quick_sort_rec_prop.
    auto.
  Qed.

End quicksort.

Eval compute in quick_sort (2::3::1::8::1::10::3::5::2::nil).


    
    