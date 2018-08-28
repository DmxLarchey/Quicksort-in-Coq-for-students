Require Import Arith List Omega.

Require Import list_utils perm sorted.

Section mergesort.

  Section merge.

    Let merge_perm_1 (x y : nat) l m k : k ~p l++y::m -> x::k ~p x::l++y::m.
    Proof. intro; auto. Qed.

    Let merge_perm_2 (x y : nat) l m k : k ~p x::l++m -> y::k ~p x::l++y::m.
    Proof.
      intros H. 
      apply perm_special with (l := x::l),
            perm_trans with (1 := H), perm_refl. 
    Qed.

    Let merge_le_bool x y : x <b y = false -> y <b x = true.
    Proof. intros H; apply Nat.leb_le; apply Nat.leb_nle in H; omega. Qed.

    Let merge_sorted x y l m k : x <b y = true 
                              -> sorted (x::l) 
                              -> sorted (y::m) 
                              -> sorted k 
                              -> k ~p l++y::m 
                              -> sorted (x::k).
    Proof.
      intros H1 H2 H3 H4 H5.
      apply sorted_cons; split; auto.
      apply lb_incl with (l++y::m).
      * apply perm_incl; auto.
      * rewrite lb_app.
        apply sorted_inv_lb in H2.
        apply sorted_inv_lb in H3.
        apply andb_true_intro; split; auto.
        simpl; apply andb_true_intro; split; auto.
        revert H3; apply lb_inc; auto.
    Qed.

    Definition merge l m : sorted l -> sorted m -> { k | k ~p l++m /\ sorted k }.
    Proof.
      pattern l, m; revert l m; apply measure_double_rect with (m := fun x y => length x+length y).
      intros l m IH Hl Hm.
      case_eq l.
      + exists m; subst; split; auto; apply perm_refl.
      + intros x l' H1.
        case_eq m.
        * intros H2; exists l; split; auto.
          rewrite <- H1, <- app_nil_end; apply perm_refl.
        * intros y m' H2.
          case_eq (x <b y); intros H3; [ | apply merge_le_bool in H3 ].
          - refine (let (k,G) := IH l' m _ _ _ in _); auto; try destruct G as (G1 & G2).
            ++ subst; simpl; omega.
            ++ revert Hl; subst; apply sorted_inv_sorted.
            ++ exists (x::k); subst; split; simpl; auto.
               apply merge_sorted with (1 := H3) (5 := G1); auto.
          - refine (let (k,G) := IH l m' _ _ _ in _); auto; try destruct G as (G1 & G2).
            ++ subst; simpl; omega.
            ++ revert Hm; subst; apply sorted_inv_sorted.
            ++ exists (y::k); subst; split; auto.
               apply merge_sorted with (1 := H3) (2 := Hm) (3 := Hl); auto.
               apply perm_trans with (1 := G1), 
                     perm_trans with (2 := perm_middle _ _ _ _),
                     perm_cons, perm_app_comm.
    Defined.

  End merge.

  Fixpoint halve m : list nat * list nat :=
    match m with
      | nil      => (nil,nil)
      | x::nil   => (m,nil)
      | x::y::m' => let (l',r') := halve m' in (x::l',y::r')
    end. 

  Fact halve_spec m : let (l,r) := halve m 
                      in m ~p l++r 
                      /\ length r <= length l <= 1 + length r. 
  Proof.
    induction m as [ [ | x [ | y m ] ] IH ] using (measure_rect _ (@length _)); simpl.
    + split; auto; constructor.
    + split; auto; repeat constructor.
    + specialize (IH m).
      destruct (halve m).
      destruct IH; simpl; auto; split; auto; omega.
  Qed.

  Definition merge_sort m : { k | m ~p k /\ sorted k }.
  Proof.
    induction m as [ m IH ] using (measure_rect _ (@length _)).
    generalize (halve_spec m).
    refine (match halve m with (l,r) => _ end); intros (H1 & H2).
    case_eq r.
    + intros H3; exists l; split.
      * subst; rewrite <- app_nil_end in H1; auto.
      * destruct l as [ | x [ | y l ] ]; auto.
        subst; simpl in H2; omega.
    + intros y r' Hr.
      refine (let (l',G1) := IH l _ in
              let (r',G3) := IH r _ in _).
      * apply perm_length in H1; simpl; subst.
        rewrite H1, app_length; simpl; omega.
      * apply perm_length in H1; simpl; subst.
        rewrite H1, app_length; simpl in H2; omega.
      * destruct G1 as (G1 & G2).
        destruct G3 as (G3 & G4).
        refine (let (k,G) := merge l' r' G2 G4 in _).
        destruct G as (G5 & G6).
        exists k; split; auto.
        apply perm_trans with (1 := H1), perm_sym,
              perm_trans with (1 := G5), perm_sym; auto.
  Defined.

End mergesort.

Recursive Extraction merge_sort.
