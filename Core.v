Set Implicit Arguments.
Require Import Coq.Lists.List.
Require Import Notations.
Require Import Datatypes.
Require Import Logic.
Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetDecide.
Require Import DecidableType.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Relations.Relations.

Module Solver.

(* Start with assumptions about flavors. Flavor equality is just Coq 
   equality, but it is decidable.  We can also decide whether one 
   flavor can rewrite another.  I'm using "sumbool" for the result of 
   these two decision procedures. *)

Parameter flavor : Set.
Parameter eq_flavor_dec : forall (f1 f2 : flavor), 
  { f1 = f2 } + { ~ f1 = f2 }.

(* There are only a finite number of flavors, and we can list 
   them all out. *)
Parameter flavors : exists (l : list flavor), forall f : flavor, In f l.


Parameter canRewrite : relation flavor.
Notation "f1 >= f2" := (canRewrite f1 f2).
Parameter canRewrite_dec : forall f1 f2, { f1 >= f2 } + { ~ f1 >= f2 }.

Axiom R1 : transitive flavor canRewrite.
Axiom R2 : forall f f1 f2, 
    f1 >= f -> f2 >= f -> f1 >= f2 \/ f2 >= f1.
(* An extra axiom about flavors: We don't have any useless flavors. 
   Everything can be used for rewriting something.... *)
(* NOTE: Wanteds is a counter-example!!! *)
Axiom R3 : forall f, exists f', f >= f'.

(* If f rewrites anything, then it rewrites itself. *)
Lemma SelfRewrite : forall f,  (exists f1, f >= f1) -> f >= f.
intros. destruct H as [f1 H].
pose (K := @R2 f1 f f H H). clearbody K. tauto.
Qed.

Definition var := nat.

Inductive ty : Set :=
  | tycon : ty
  | tyvar : var -> ty
  | tyapp : ty -> ty -> ty.

Definition eq_ty_dec : forall t1 t2 : ty, {t1 = t2} + {t1 <> t2}.
  intros; decide equality. apply eq_nat_dec.
Qed.

Module VarSet       := MSetWeakList.Make Nat_as_OT.
Module VarSetDecide := WDecideOn Nat_as_OT VarSet.

Fixpoint vars (t : ty) : VarSet.t :=
  match t with 
  | tycon => VarSet.empty
  | tyvar x => VarSet.singleton x
  | tyapp t1 t2 => VarSet.union (vars t1) (vars t2)
  end.

Definition elt : Set := (var * flavor * ty).
Definition Subst : Set := list elt.
(* Working from the picture of the whiteboard. *)

(* This allows (a,f,t1) (a,f,t2) when not f >= f. 
    (i.e. 2 wanteds that don't.) *)
Definition WF1 (s : Subst) := forall a f1 t1 f2 t2,  
     In (a, f1, t1) s -> In (a, f2, t2) s -> 
     t1 <> t2 -> not (f1 >= f2).

Definition WF2 (s : Subst) := forall a f, 
  not (In (a, f, tyvar a) s).

Definition noids (s : Subst) := WF2 s.

(* This was on the board, but I don't think it is true. 
   What if f can't rewrite itself? *)
Lemma L1 : forall s (f : flavor) a t1 t2, 
  WF1 s -> f >= f -> In (a, f, t1) s -> In (a, f, t2) s -> t1 = t2.
Proof.  intros. 
  destruct (eq_ty_dec t1 t2) as [Y | N]. exact Y. 
  pose (J := H _ _ _ _ _ H1 H2 N). clearbody J.
  contradiction.
Qed.


(* A very concrete definition of applying the substition. 
   We just lookup the first tuple in the list that works.
   (Is this what GHC does?) *)
Fixpoint apply (s : Subst) (f : flavor) (a : var) : option ty := 
  match s with 
  | nil => None
  | (a1,f1,t1) :: s' => 
     if sumbool_and _ _ _ _ 
        (eq_nat_dec a a1) 
        (canRewrite_dec f1 f)
     then Some t1 else apply s' f a 
  end.

Lemma WF1_tail : forall a f t s, WF1 ((a,f,t)::s) -> WF1 s.
  intros. unfold WF1 in *. intros. apply (H a0 f1 t1 f2 t2).
  right. auto. right. auto. auto.
Qed.

(* Here's an alternative to L1.  
   It doesn't necessarily have to be the first tuple. *)
Lemma apply_in : forall s f f1 a t, 
  WF1 s -> In (a, f1, t) s -> f1 >= f -> apply s f a = Some t.
 intros. 
 induction s. inversion H0.
 destruct a0 as [[a2 f2] t2]. simpl.
 destruct (eq_nat_dec a a2); destruct (canRewrite_dec f2 f); simpl.
 - subst. 
   destruct (eq_ty_dec t2 t). f_equal. auto.
   inversion H0. inversion H2. rewrite H5 in n. tauto. (* n <> n *)
   assert (I : In (a2, f2, t2) ((a2,f2,t2) :: s)). simpl. left. auto.
   destruct (R2 H1 c).
   assert (n2 : t <> t2). auto.
   pose (K := H _ _ _ _ _ H0 I n2). contradiction. 
   pose (K := H _ _ _ _ _ I H0 n). contradiction.
 - destruct (eq_flavor_dec f1 f2). subst. contradiction.
   simpl in H0. inversion H0. inversion H2. subst f2. tauto. 
   apply IHs. eapply WF1_tail. eauto. auto.
 - simpl in H0. inversion H0. inversion H2. subst a2. tauto.
   apply IHs. eapply WF1_tail. eauto. auto.
 - simpl in H0. inversion H0. inversion H2. subst a2. tauto.
   apply IHs. eapply WF1_tail. eauto. auto.
Qed.  

(* We can also invert the function. *)
Lemma in_apply : forall s f a t, 
  apply s f a = Some t -> exists f1, f1 >= f /\ In (a, f1, t) s.
  induction s; intros; simpl in H. inversion H.
  destruct a as [p0 t1]. destruct p0 as [a1 f1].
  destruct (eq_nat_dec a0 a1); destruct (canRewrite_dec f1 f); simpl in H.
  - inversion H. exists f1. split. auto. subst. simpl. left. auto.
  - subst. destruct (IHs f a1 t H) as [f2 [J K]].
    exists f2. split. auto. simpl. right. auto.
  - subst. destruct (IHs f a0 t H) as [f2 [J K]].
    exists f2. split. auto. simpl. right. auto.
  - subst. destruct (IHs f a0 t H) as [f2 [J K]].
    exists f2. split. auto. simpl. right. auto.
Qed.
   

(* Extend the substitution to types *)

Fixpoint apply_ty (s : Subst) (f : flavor) (t : ty) : ty :=
  match t with 
  | tycon => tycon
  | tyvar x => match apply s f x with
                  | Some t => t
                  | None   => tyvar x
               end
  | tyapp t1 t2 => tyapp (apply_ty s f t1) (apply_ty s f t2)
  end.

(* This is from the triangular substitutions paper. 
   Define a substituion to be well formed if there are 
   no cycles. 
 *)

(* is y connected to x through some rewrite. *)
Definition tri s y x := 
  exists f, match apply s f x with 
    | Some t => VarSet.In y (vars t)
    | None => False
    end.

Definition wfs (s : Subst) := 
  forall (a : var), not ((clos_trans var (tri s)) a a). 

Lemma wfs_noids : forall s, WF1 s -> wfs s -> noids s.
  intros s H1 H. unfold noids. unfold WF2. unfold not. intros.
  unfold wfs in H. unfold not in H.
  destruct (R3 f) as [f' Hf']. apply (H a).
  apply t_step. assert (apply s f' a = Some (tyvar a)).
  eapply apply_in. eauto. eauto. eauto. 
  unfold tri. exists f'. rewrite H2. simpl. 
  (* This is a general purpose tactic from the MSets library
  for proving facts about finite sets. *)
  VarSetDecide.fsetdec.
Qed.

Lemma var_in_union : forall a s1 s2, VarSet.In a (VarSet.union s1 s2) -> 
  VarSet.In a s1 \/ VarSet.In a s2.
intros. VarSetDecide.fsetdec.
Qed. 

Lemma vars_in_apply_ty : forall s a f t, 
  VarSet.In a (vars (apply_ty s f t)) -> 
  VarSet.In a (vars t) \/ exists b t0,  
    VarSet.In a (vars t0) /\ apply s f b = Some t0 /\ VarSet.In b (vars t).
induction t; intros; simpl in H. 
  - inversion H.
  - destruct (eq_nat_dec a v). subst. left. simpl. VarSetDecide.fsetdec.
    right. exists v. destruct (apply s f v). exists t. simpl. split; auto.
       split. auto. VarSetDecide.fsetdec.
    simpl in H. VarSetDecide.fsetdec.
  - destruct (var_in_union H) as [L | R].
     destruct (IHt1 L) as [M | [b [t0 [In [Ap Inb]]]]]. left. simpl. VarSetDecide.fsetdec.
       right. exists b. exists t0. simpl. split. auto. split. auto. VarSetDecide.fsetdec.
     destruct (IHt2 R) as [M | [b [t0 [In [Ap Inb]]]]]. left. simpl. VarSetDecide.fsetdec.
       right. exists b. exists t0. simpl. split. auto. split. auto. VarSetDecide.fsetdec.
Qed.

(* ?????   
  Do we need to check the interaction between f and f1 in 
  the self application?   *)
Definition apply_e s f (e : elt) : elt := 
  match e with
  | (a, f1, t) => 
    if canRewrite_dec f f1 then 
      (a, f1, apply_ty s f t)
    else
      (a, f1, t)
  end.

(* The first result of the triangular substitutions paper. *)
Definition selfapp (s : Subst) (f : flavor) : Subst := 
  map (apply_e s f) s.

Definition map_option A B (f: A -> B) o := 
  match o with 
  | Some t => Some (f t)
  | None   => None
  end.

Lemma map_apply : forall s1 f1 s f y o,
   apply s f y = o -> 
   apply (map (apply_e s1 f1) s) f y = map_option (apply_ty s1 f1) o.
destruct o.
induction s. intros. inversion H. 
intros. destruct a as [[a0 f0] t0].
simpl. simpl in H. 
destruct (eq_nat_dec y a0);
destruct (canRewrite_dec f0 f). 
- simpl. subst. simpl in H. inversion H. auto.
- simpl. subst. simpl in H. apply IHs. auto.
- simpl. subst. simpl in H. apply IHs. auto.
- simpl. subst. simpl in H. apply IHs. auto.
- intros. simpl.
Admitted.


(* If a var is free in S_f (t) then either it was in t, or it is in 
   some b that was substituted in t.*)
Lemma in_apply_ty : forall a s f t,
VarSet.In a (vars  (apply_ty s f t)) -> VarSet.In a (vars t) \/ 
  exists b t0, VarSet.In b (vars t) /\ apply s f b = Some t0 /\ VarSet.In a (vars t0).
induction t; intros.
- simpl in H. VarSetDecide.fsetdec.
- simpl in *. 
  case_eq (apply s f v); intros. rewrite H0 in H.
    right. exists v. exists t. split. VarSetDecide.fsetdec. tauto.
    rewrite H0 in H. simpl in H. inversion H. subst. left. auto.
       subst. inversion H2.
- simpl in *.
  destruct (var_in_union H) as [L | R].
    destruct (IHt1 L) as [ In | [b [t0 [M [N P]]]]].
    VarSetDecide.fsetdec.
    right. exists b. exists t0. split. VarSetDecide.fsetdec. tauto.
    destruct (IHt2 R) as [ In | [b [t0 [M [N P]]]]].
    VarSetDecide.fsetdec.
    right. exists b. exists t0. split. VarSetDecide.fsetdec. tauto.
Qed.

(* If you can get there taking two steps at a time, you 
  can get there taking one step at a time. *)
Lemma step: forall s f a y,
  clos_trans var (tri (selfapp s f)) a y -> 
  clos_trans var (tri s) a y.
intros. induction H; subst.
(* single step case *)
- unfold selfapp, tri in H.
  destruct H as [f0 M].
  case_eq (apply s f0 y); intros.
  assert (H1 : apply (map (apply_e s f) s) f0 y =
               map_option (apply_ty s f) (Some t)). eapply map_apply; eauto.
  rewrite H1 in M.
  destruct (in_apply_ty _ _ _ M).
    apply t_step. unfold tri. exists f0. rewrite H. auto.
    destruct H0 as [b [t0 [N [P Q]]]].
    apply t_trans with (y := b). 
      apply t_step. unfold tri. exists f. rewrite P. auto.
      apply t_step. unfold tri. exists f0. rewrite H. auto.
  pose (K:= map_apply s f _ _ _ H). simpl in K.
  rewrite K in M. contradiction.
- apply t_trans with (y := y). auto. auto.
Qed.

(* If you can get there taking one at a time, you 
  can get there taking two steps at a time. *)
(* Probably not true *)
(*
Lemma step_two_one : forall s f a y,
  clos_trans var (tri s) a y -> 
  clos_trans var (tri (selfapp s f)) a y.
intros. induction H; unfold tri in H.
- destruct H as [f0 M].
case_eq (apply s f0 y); intros; rewrite H in M.
apply t_step. unfold tri. exists f0. unfold selfapp.
apply map_apply with (s := s) (f := f0)(s1:= s)(f1:=f) in H.
rewrite H. simpl. admit. 
contradiction.
- apply t_trans with (y := y). auto. auto.
Qed.
*)

Lemma wfs_selfapp : forall s f, WF1 s -> wfs s <-> wfs (selfapp s f).
intros. split.
(* left to right*)
- unfold wfs. unfold not. intros H1 a CT. apply (H1 a).
  inversion CT. subst. unfold tri in H0. destruct H0 as [f0 H0].
  assert (EQ : exists t, apply (selfapp s f) f0 a = Some t).
  destruct (apply (selfapp s f) f0 a). exists t. auto. inversion H0.
  destruct EQ as [t EQ].
  rewrite EQ in H0.
  destruct (in_apply _ _ _ EQ) as [f1 [J K]].
  unfold selfapp in K.
  rewrite in_map_iff in K. destruct K as [[[a0 f3] t0] [L M]].
  inversion L. subst. clear L.
  assert (apply s f0 a = Some t0). eapply apply_in; eauto.
  destruct (vars_in_apply_ty _ _ _ H0) as [N | [b [t1 [In [Ap Inb]]]]].
  eapply t_step. unfold tri. exists f0. rewrite H2. auto. 
  apply t_trans with (y := b). apply t_step. unfold tri.
  exists f. rewrite Ap. auto. apply t_step. unfold tri.
  exists f0. rewrite H2. auto. 
  subst. apply (step _ _ CT).
(* right to left *)
- unfold wfs, not. intros H1 a CT. apply (H1 a).
inversion CT. subst. unfold tri in H0. destruct H0 as [f0 H0].
  (* Kinda stuck *)
Admitted.


(* It's not clear to me which version of the iterated substitution is 
   easier to work with. *)

(* Apply a substitution to itself n times. *)
Definition selfapp_n (n : nat) (s : Subst) (f : flavor) : Subst :=
  nat_rec (fun _ => Subst) s (fun _ =>  map (apply_e s f)) n.

Lemma selfapp_once : forall s f,
  selfapp_n (S 0) f s = selfapp f s.
intros. simpl. unfold selfapp. auto.
Qed.

Lemma selfapp_many : forall s f n,
  selfapp_n (S n) s f = map (apply_e s f) (selfapp_n n s f).
intros. simpl. unfold selfapp. auto.
Qed.

(* Apply a substitution to a ty n times *)
Fixpoint apply_n (n : nat) (s : Subst) (f : flavor) (t : ty) : ty := 
  match n with 
  | 0 => t
  | S m => apply_ty s f (apply_n m s f t)
  end.

Lemma apply_n_tycon : forall n s f, apply_n n s f tycon = tycon.
induction n. intros. simpl. auto.
intros. simpl. rewrite IHn. simpl. auto.
Qed.

Lemma apply_n_app : forall n s f t1 t2, 
  apply_n n s f (tyapp t1 t2) = 
  tyapp (apply_n n s f t1) (apply_n n s f t2).
induction n; intros; simpl; auto.
rewrite IHn. simpl. auto.
Qed.


Lemma iterate : forall n s f t, 
  apply_ty (selfapp_n n s f) f t = apply_n (S n) s f t.
induction n; intros.
  - simpl. auto.
  - simpl in IHn. simpl. rewrite <- IHn.
(* STUCK *)
Admitted.

Definition IG1 s := 
  forall f t, 
    exists n, apply_n n s f t = apply_n (S n) s f t.

Definition IG1C s := exists n, 
  forall f t, 
    apply_n n s f t = apply_n (S n) s f t.


Lemma one_n : forall s, IG1 s -> IG1C s.
(* I don't believe this. The n *could* depend on t, 
    and there are an infinite number of these. *)
Admitted.

Definition IG1A s := forall f, 
      exists n, selfapp_n n s f = selfapp_n (S n) s f.
Definition IG1AC s := exists n, forall f, 
      selfapp_n n s f = selfapp_n (S n) s f.
Lemma one_nA : forall s, IG1A s -> IG1AC s.
intros.
unfold IG1A,IG1AC in *.  destruct flavors as [l F].
Admitted.



Lemma L2 : forall s s', IG1 s -> incl s' s ->  IG1 s'.
unfold incl, IG1. intros.
destruct (H f t) as [n K].
exists n.
induction t. simpl. rewrite apply_n_tycon. simpl. auto.
simpl. 
Admitted.

Lemma fixpoint : forall s, WF1 s -> wfs s <-> IG1 s.

