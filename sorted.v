Require Import Arith.
Require Import List.
Require Import Bool.

Require Import list_utils.

Notation le_bool := (NPeano.leb).
Infix "<b" := le_bool (at level 30, no associativity).

Definition le_bool_le := NPeano.leb_le.

(* don't forget to use these two propositions *)

Check le_bool_le.
Check andb_true_iff.

(* ub is upper bound *) 

Fixpoint ub l x := 
  match l with 
    | nil  => true
    | y::l => y <b x && ub l x
  end.

(* ub l x means that every element in l is lower than x *)

Fact ub_spec l x : ub l x = true <-> forall y, In y l -> y <b x = true.
Proof.
  induction l as [ | z l IHl ]; simpl; split; auto.

  intros H1 y H2.
  apply andb_true_iff in H1.
  destruct H2 as [ H2 | H2 ].
  rewrite H2 in H1.
  apply H1.
  apply IHl; auto.
  apply H1.
  
  intros H.
  apply andb_true_iff; split.
  apply (H z); auto.
  apply IHl.
  intros; apply H; auto.
Qed.

Fact ub_inc l x y : x <b y = true -> ub l x = true -> ub l y = true.
Proof.
  do 2 rewrite ub_spec.
Admitted.

Fact ub_incl l l' x : incl l l' -> ub l' x = true -> ub l x = true.
Proof.
Admitted.

Fact ub_app l1 l2 x : ub (l1++l2) x = ub l1 x && ub l2 x.
Proof.
  induction l1 as [ | y l1 IHl1 ]; simpl; auto.
  rewrite IHl1.
  destruct (y <b x); simpl; auto.
Qed.

(* lower bound : every element in l is greater than x *)

Fixpoint lb m x := 
  match m with 
    | nil  => true
    | y::m => x <b y && lb m x
  end.

Fact lb_spec l x : lb l x = true <-> forall y, In y l -> x <b y = true.
Proof.
Admitted.

Fact lb_inc m x y : x <b y = true -> lb m y = true -> lb m x = true.
Proof.
Admitted.

Fact lb_incl m m' x : incl m m' -> lb m' x = true -> lb m x = true.
Proof.
Admitted.

Fact lb_app m1 m2 x : lb (m1++m2) x = lb m1 x && lb m2 x.
Proof.
Admitted.

(* lower upper : every element in l is lower that every element in m *)

Fixpoint lu l m := 
  match m with 
    | nil  => true
    | x::m => ub l x && lu l m
  end.

Fact lu_spec l m : lu l m = true <-> forall x y, In x l -> In y m -> x <b y = true.
Proof.
  induction m as [ | z m IHm ]; simpl; split; auto.
Admitted.

Fact lu_middle l x m : ub l x = true -> lb m x = true -> lu l m = true.
Proof.
Admitted.
  
Fact lu_In l l' x m : In x m -> incl l l' -> lu l' m = true -> ub l x = true.
Proof.
Admitted.

(* incl is defined in the List module of the Standard library *)

Print incl.
SearchAbout [ incl ].

Fact lu_incl l l' m m' : incl l l'
                      -> incl m m' 
                      -> lu l' m' = true 
                      -> lu l m = true.
Proof.
Admitted.

Fact lu_nil_l l : lu nil l = true.
Proof.
  apply lu_spec.
  intros ? ? [].
Qed.

Fact lu_nil_r l : lu l nil = true.
Proof.
  simpl; auto.
Qed.

Hint Immediate lu_nil_l lu_nil_r.

Fact lu_app_l l1 l2 r : lu (l1++l2) r = lu l1 r && lu l2 r.
Proof.
  induction r as [ | x r IHr ]; simpl; auto.
Admitted.

Fact lu_app_r l r1 r2 : lu l (r1++r2) = lu l r1 && lu l r2.
Proof.
Admitted.

Fact lu_cons_r l x r : lu l r = true -> ub l x = true -> lu l (x::r) = true.
Proof.
  simpl.
  intros H1 H2.
  rewrite H1, H2.
  auto.
Qed.

Fact lu_cons r : forall l x, lu (x::l) r = lb r x && lu l r.
Proof.
  induction r as [ | y r IHr ]; intros l x; simpl; auto.
  rewrite IHr.
Admitted.

Fact lu_cons_l x l r : lu l r = true -> lb r x = true -> lu (x::l) r = true.
Proof.
  rewrite lu_cons.
  intros H1 H2; rewrite H1, H2.
  auto.
Qed.

Fact lu_cons_lr x y : x <b y = true -> lu (x::nil) (y::nil) = true.
Proof.
  simpl.
  intros H; rewrite H; auto.
Qed.

Hint Resolve lu_cons_l lu_cons_r lu_cons_lr. 

Fact lu_xchg l1 l2 m : lu (l1++m) l2 = true -> lu l1 m = true -> lu l1 (m++l2) = true.
Proof.
Admitted.

Fact lu_insert x m l1 l2 : lu (m++x::nil) (l1++l2) = true -> ub m x = true -> lu m (l1++x::l2) = true.
Proof.
  intros H1 H2.
  apply lu_incl with (l' := m) (m' := (x::nil)++l1++l2).
Admitted.

(* ll is sorted iff whenever it is split into l++r, the elements of l are lower than those of r *)

Definition sorted ll := forall l r, ll = l++r -> lu l r = true.

Proposition sorted_nil : sorted nil.
Proof.
  intros [ | ] [ | ]; try discriminate 1.
  intros _; simpl; auto.
Qed.

Proposition sorted_one x : sorted (x::nil).
Proof.
  intros [ | ? []] [] H; try discriminate H; auto.
Qed.

Hint Resolve sorted_nil sorted_one.

Section sorted_app.

  Let sorted_app_1 l r : sorted (l++r) -> sorted l /\ sorted r /\ lu l r = true. 
  Proof.
  Admitted.

  Let sorted_app_2 l r : sorted l /\ sorted r /\ lu l r = true -> sorted (l++r). 
  Proof.
    intros (H1 & H2 & H3) l1 r1 H.

    (* app_split is proved in list_utils.v *)

    apply app_split in H;
    destruct H as [ (m & M1 & M2) 
                  | (m & M1 & M2) ].
  Admitted.

  Fact sorted_app l r : sorted (l++r) <-> sorted l /\ sorted r /\ lu l r = true. 
  Proof.
    split.
    apply sorted_app_1.
    apply sorted_app_2.
  Qed.

End sorted_app.

Proposition sorted_cons x l : sorted (x::l) <-> sorted l /\ lb l x = true.
Proof.
  cutrewrite (x::l = (x::nil)++l); auto.
  split.
Admitted.

Hint Resolve sorted_nil sorted_one sorted_cons.

Proposition sorted_inv_lb x l : sorted (x::l) -> lb l x = true.
Proof.
  rewrite sorted_cons; tauto.
Qed.

Proposition sorted_inv_sorted x l : sorted (x::l) -> sorted l.
Proof.
  rewrite sorted_cons; tauto.
Qed.

Hint Resolve sorted_inv_sorted sorted_inv_lb.

Theorem quick_sorted l x m : sorted l
                          -> ub l x = true
                          -> lb m x = true 
                          -> sorted m
                          -> sorted (l++x::m).
Proof.
  intros.
  apply sorted_app; repeat split; auto.
  apply sorted_cons; split; auto.
  simpl.
  apply andb_true_iff; split; auto.
  apply lu_middle with (x := x); auto.
Qed.
