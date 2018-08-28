Require Import Arith Omega.
Require Import List. 

Set Implicit Arguments.

Reserved Notation "x '~p' y" (at level 70, no associativity).

Section In.

  Variable (X : Type) (x : X) (eqX_dec : forall y : X, y = x \/ y <> x).

  Theorem In_w_dec l : In x l \/ ~ In x l.
  Proof.
    induction l as [ | y l IHl ].
    + right; red; trivial.
    + destruct (eqX_dec y); simpl; tauto.
  Qed.

End In.  

Section add.

    Variable (X : Type) (x : X).

    Implicit Type l : list X.

    Definition add l m := exists l1 l2, m = l1++x::l2 /\ l = l1++l2.

    Fact in_add_0 l : add l (x::l).
    Proof. exists nil, l; auto. Qed.
 
    Fact in_add_1 y l m : add l m -> add (y::l) (y::m).
    Proof.
      intros (l1 & l2 & ? & ?); subst; red.
      exists (y::l1), l2; auto.
    Qed.

    Section add_ind.

      Variable P : list X -> list X -> Prop.

      Hypothesis HP0 : forall l, P l (x::l).
      Hypothesis HP1 : forall y l m, P l m -> P (y::l) (y::m).

      Theorem add_ind : forall l m, add l m -> P l m.
      Proof.
        intros l m (l1 & l2 & ? & ?); subst.
        induction l1 as [ | y l1 IH ].
        + apply HP0.
        + simpl; apply HP1, IH.
      Qed.
  
    End add_ind.

    Fact add_nil_inv l : add l nil -> False.
    Proof.
      intros ([|] & ? & ? & _); discriminate.
    Qed.

    Fact add_cons_inv l y m : add l (y::m) -> x = y /\ l = m 
                                           \/ exists l', l = y::l' /\ add l' m.
    Proof.
      intros ([ | u l1 ] & l2 & H1 & H2); simpl in *; inversion H1; subst; auto.
      right; exists (l1++l2); split; auto.
      exists l1, l2; auto.
    Qed.

End add.

Hint Resolve in_add_0 in_add_1.

Section split.

  Variable (X : Type) (x y : X).

  Fact split_inv l1 r1 l2 r2 : l1++x::r1 = l2++y::r2 
                            -> (exists m, l1 = l2++y::m /\ r2 = m++x::r1)  
                            \/ l1 = l2 /\ x = y /\ r1 = r2
                            \/ (exists m, l2 = l1++x::m /\ r1 = m++y::r2).
  Proof.
    revert l2.
    induction l1 as [ | u l1 IH ]; intros [ | v l2 ]; simpl; inversion 1; auto.
    + do 2 right; exists l2; auto.
    + left; exists l1; auto.
    + destruct (IH _ H2) as [ (m & ? & ?) | [ (? & ? & ?) | (m & ? & ?) ] ]; subst.
      - left; exists m; auto.
      - right; left; auto.
      - do 2 right; exists m; auto.
  Qed.

End split.

Section perm.

  Variable X : Type.

  Inductive perm : list X -> list X -> Prop :=

    | perm_nil   :                    nil ~p nil

    | perm_cons  : forall x l1 l2,     l1 ~p l2 
                               ->   x::l1 ~p x::l2

    | perm_swap  : forall x y l,  x::y::l ~p y::x::l

    | perm_trans : forall l1 l2 l3,    l1 ~p l2 
                               ->      l2 ~p l3 
                               ->      l1 ~p l3

  where "x '~p' y " := (perm x y).
  
  Hint Constructors perm.

  Fact perm_refl l : l ~p l.
  Proof.
    induction l as [ | x l IH ].
    + apply perm_nil.
    + apply perm_cons, IH.
  Qed.

  Fact perm_sym l1 l2 : l1 ~p l2 -> l2 ~p l1.
  Proof.
    intros H.
    induction H as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ]; auto.
    apply perm_trans with (1 := IH2); trivial.
  Qed.

  Fact perm_length l1 l2 : l1 ~p l2 -> length l1 = length l2.
  Proof.
    intros H.
    induction H as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ]; simpl; trivial.
    f_equal; trivial.
    rewrite IH1; trivial.
  Qed.

  Fact perm_middle x l r : x::l++r ~p l++x::r.
  Proof.
    induction l as [ | y l IHl ]; simpl.
    + apply perm_refl.
    + apply perm_trans with (1 := perm_swap _ _ _); auto.
  Qed.

  Fact perm_special x k l r : k ~p l++r -> x::k ~p l++x::r.
  Proof.
    intros H; apply perm_trans with (2 := perm_middle _ _ _), perm_cons, H.
  Qed.

  Fact perm_app_comm l m : l ++ m ~p m ++ l.
  Proof.
    induction l; simpl.
    * rewrite <- app_nil_end; apply perm_refl.
    * apply perm_special; trivial.
  Qed.

  Fact perm_app_l l r1 r2 : r1 ~p r2 -> l++r1 ~p l++r2.
  Proof.
    intros; induction l; simpl; auto.
  Qed.

  Fact perm_app l1 l2 r1 r2 : l1 ~p l2 -> r1 ~p r2 -> l1++r1 ~p l2++r2.
  Proof.
    intros H; revert H r1 r2.
    induction 1 as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ]; intros r1 r2 H12; simpl; auto.
     apply perm_trans with (1 := perm_swap _ _ _), perm_app_l with (l := _::_::_); auto.
     apply perm_trans with (1 := IH1 _ _ H12), IH2, perm_refl.
  Qed.

  (* incl is defined in the List module of the Standard library *)

  Print incl.

  Fact perm_incl l m : l ~p m -> incl l m.
  Proof.
    intros H.
    induction H as [ | x l1 l2 H1 IH1 | x y l | l1 l2 l3 H1 IH1 H2 IH2 ]; red; simpl; auto.
    + intros a [ ? | H ]; subst; auto.
    + intros a [ ? | [ ? | H ] ]; subst; auto.
  Qed.

  Fact perm_equal x y : x::nil ~p y::nil -> x = y.
  Proof.
    intros H.
    apply perm_incl in H.
    specialize (H x); simpl in H.
    destruct H as [ ? | [] ]; subst; auto.
  Qed.

  Hint Resolve perm_refl.

  Fact add_perm x l m : add x l m -> x::l ~p m.
  Proof. intros (? & ? & ? & ?); subst; apply perm_middle. Qed.

  Fact add_perm_rev x l m : add x l m -> m ~p x::l.
  Proof. intro; apply perm_sym, add_perm; trivial. Qed.

  Fact add_perm' x l m : add x l (x::m) -> l ~p m.
  Proof.
    intros ([|] & ? & H1 & H2); subst; inversion H1; subst; auto; apply perm_middle. 
  Qed.

  Fact add_perm_rev' x l m : add x l (x::m) -> m ~p l.
  Proof. intro; apply perm_sym, add_perm' with x; trivial. Qed.

  Hint Resolve add_perm add_perm_rev add_perm' add_perm_rev'.
  
  Fact add_perm_inv x l1 m1 m2 : m1 ~p m2 -> add x l1 m1 -> exists l2, l1 ~p l2 /\ add x l2 m2.
  Proof.
    intros H; revert H x l1. 
    induction 1 as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ]; intros u l' H.
    + apply add_nil_inv in H; tauto.
    + apply add_cons_inv in H.
      destruct H as [ (? & ?) | (l3 & ? & H3) ]; subst.
      * exists l2; auto.
      * apply IH1 in H3.
        destruct H3 as (l4 & H3 & H4).
        exists (x::l4); auto.
    + apply add_cons_inv in H.
      destruct H as  [ (? & ?) | (l1 & ? & H) ]; subst.
      * exists (y::l); auto.
      * apply add_cons_inv in H.
        destruct H as  [ (? & ?) | (l2 & ? & H) ]; subst.
        - exists (x::l); auto.
        - exists (y::x::l2); auto.
    + apply IH1 in H.
      destruct H as (l4 & G1 & H).
      apply IH2 in H.
      destruct H as (l5 & G2 & H).
      exists l5; split; auto.
      apply perm_trans with (1 := G1); auto.
  Qed.

  Fact perm_add_inv ll mm : ll ~p mm -> forall x l m, add x l ll -> add x m mm -> l ~p m.  
  Proof.
    induction 1 as [ 
                   | x l1 l2 H1 IH1 
                   | x y l 
                   | l1 l2 l3 H1 IH1 H2 IH2 
                   ]; intros z u v H3 H4.
    + apply add_nil_inv in H3; tauto.
    + apply add_cons_inv in H3;
      apply add_cons_inv in H4.
      destruct H3 as [ (? & ?) | (l' & ? & H3) ]; 
      destruct H4 as [ (? & ?) | (m' & ? & H4) ]; subst; auto.
      * apply perm_trans with (1 := H1); auto.
      * apply perm_trans with (2 := H1); auto.
      * apply perm_cons, IH1 with z; auto.
    + apply add_cons_inv in H3;
      apply add_cons_inv in H4.
      destruct H3 as [ (? & ?) | (l' & ? & H3) ]; 
      destruct H4 as [ (? & ?) | (m' & ? & H4) ]; subst; auto.
      * apply perm_cons, add_perm_rev' with x; auto.
      * apply perm_cons, add_perm' with y; auto.
      * apply add_cons_inv in H3;
        apply add_cons_inv in H4.
        destruct H3 as [ (? & ?) | (l'' & ? & H3) ]; 
        destruct H4 as [ (? & ?) | (m'' & ? & H4) ]; subst; auto.
        - apply perm_trans with (1 := perm_swap _ _ _).
          do 2 apply perm_cons.
          destruct H3 as (l1 & l2 & ? & ?);
          destruct H4 as (m1 & m2 & ? & ?); subst.
          apply split_inv in H1.
          destruct H1 as [ (m & ? & ?) | [ (? & ? & ?) | (m & ? & ?) ] ]; subst; auto.
          ** rewrite app_ass; simpl; apply perm_app; auto; apply perm_middle.
          ** rewrite app_ass; simpl; apply perm_app; auto; apply perm_sym, perm_middle.
    + apply add_perm_inv with (1 := H1) in H3.
      destruct H3 as (w & H3 & H5).
      apply perm_trans with (1 := H3).
      apply IH2 with z; auto.
  Qed.

  Fact perm_cons_inv x l m : x::l ~p x::m -> l ~p m.
  Proof. intro; apply perm_add_inv with (x::l) (x::m) x; auto. Qed.

  Hint Resolve perm_cons_inv.

  Fact perm_app_inv l m k : l++m ~p l++k -> m ~p k.
  Proof.
    intro H; induction l; simpl; auto.
    apply perm_cons_inv in H; auto.
  Qed.
  
  Fact perm_app_perm_inv l1 l2 r1 r2 : l1 ~p l2 -> l1++r1 ~p l2++r2 -> r1 ~p r2.
  Proof.
    intros H1 H2.  
    apply perm_app_inv with l2, perm_trans with (2 := H2), perm_sym.
    do 2 apply perm_sym, perm_trans with (1 := perm_app_comm _ _).
    apply perm_app_l; auto.
  Qed.

  Section perm_dec.
 
    Let perm_dec_1 : (forall l m, l ~p m \/ ~ l ~p m) -> (forall x y : X, x = y \/ x <> y).
    Proof.
      intros H x y.
      destruct (H (x::nil) (y::nil)) as [ H1 | H1 ].
      + left; revert H1; apply perm_equal.
      + right; contradict H1; subst; auto.
    Qed.

    Let perm_dec_2 : (forall x y : X, x = y \/ x <> y) -> (forall l m, l ~p m \/ ~ l ~p m).
    Proof.
      intros H.
      induction l as [ | x l IH ]; intros [ | y m ].
      + left; auto.
      + right; intros C; apply perm_length in C; discriminate.
      + right; intros C; apply perm_length in C; discriminate.
      + destruct (@In_w_dec _ x) with (l := m) as [ G1 | G1 ].
        - intro; auto.
        - apply in_split in G1.
          destruct G1 as (m1 & m2 & ?); subst.
          destruct (IH (y::m1++m2)) as [ G1 | G1 ].
          * left; apply perm_special with (l := _::_); auto.
          * right; contradict G1.
            apply perm_cons_inv with x, 
                  perm_trans with (1 := G1),
                  perm_trans with (2 := perm_swap _ _ _),
                  perm_cons, perm_sym, perm_middle.
        - destruct (H x y) as [ E | D ].
          * subst.
            destruct (IH m) as [ H1 | H1 ].
            ++ left; auto.
            ++ right; contradict H1.
               revert H1; apply perm_cons_inv.
          * right; contradict G1.
            apply perm_incl in G1.
            destruct (G1 x) as [ G2 | G2 ]; simpl; subst; tauto.
    Qed.

    Theorem perm_dec : (forall x y : X, x = y \/ x <> y) 
                   <-> (forall l m, l ~p m \/ ~ l ~p m).
    Proof. split; auto. Qed.

  End perm_dec.

End perm.

Infix "~p" := (@perm _).

Hint Constructors perm.
Hint Resolve perm_special perm_refl perm_app.

Check perm_dec.

    

  