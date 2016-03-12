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
Require Import Setoid.


Module Solver.

Parameter flavor : Type.
Parameter eq_flavor_dec : forall (f1 f2 : flavor), { f1 = f2 } + { ~ f1 = f2 }.

Parameter canRewrite : relation flavor.
Notation "f1 >= f2" := (canRewrite f1 f2).
Parameter canRewrite_dec : forall f1 f2, { f1 >= f2 } + { ~ f1 >= f2 }.

Axiom R1 : transitive flavor canRewrite.
Axiom R2 : forall f f1 f2, f1 >= f -> f2 >= f -> 
    { f1 >= f2 } + { f2 >= f1 }.
(* We don't have any useless flavors. 
   Everything can be used for rewriting something. *)
Axiom R3 : forall f, exists f', f >= f'.


Definition var := nat.
Module VarSet := MSetWeakList.Make Nat_as_OT.
Module VarSetDecide := WDecideOn Nat_as_OT VarSet.

Inductive ty : Set :=
  | tycon : ty
  | tyvar : var -> ty
  | tyapp : ty -> ty -> ty.

Definition eq_ty_dec : forall t1 t2 : ty, {t1 = t2} + {t1 <> t2}.
  intros; decide equality. apply eq_nat_dec.
Qed.

Fixpoint vars (t : ty) : VarSet.t :=
  match t with 
  | tycon => VarSet.empty
  | tyvar x => VarSet.singleton x
  | tyapp t1 t2 => VarSet.union (vars t1) (vars t2)
  end.

Definition elt := (var * flavor * ty).
Definition Subst := list elt.
Definition WF1 (s : Subst) := forall a f1 t1 f2 t2,  
     In (a, f1, t1) s -> In (a, f2, t2) s -> 
     t1 <> t2 -> not (f1 >= f2).

Definition WF2 (s : Subst) := forall a f, 
  not (In (a, f, tyvar a) s).
Definition noids (s : Subst) := WF2 s.

Lemma L1 : forall s (f : flavor) a t1 t2, 
  WF1 s -> In (a, f, t1) s -> In (a, f, t2) s -> t1 = t2.
Proof.  intros. 
  destruct (eq_ty_dec t1 t2) as [Y | N]. exact Y. 
  pose (J := H _ _ _ _ _ H0 H1 N).
Admitted.
(* I don't think this is true. what if f can't rewrite itself? *)

(* Lookup the first tuple in the list that works. *)
Fixpoint apply (s : Subst) (f : flavor) (a : var) : option ty := 
  match s with 
  | nil => None
  | (a1,f1,t1) :: s' => 
     if sumbool_and _ _ _ _ (eq_nat_dec a a1) (canRewrite_dec f1 f)
     then Some t1 else apply s' f a 
  end.

Lemma WF1_tail : forall a f t s, WF1 ((a,f,t)::s) -> WF1 s.
  intros. unfold WF1 in *. intros. apply (H a0 f1 t1 f2 t2).
  right. auto. right. auto. auto.
Qed.

(* It doesn't necessarily have to be the first tuple. *)
Lemma apply_in : forall s f f1 a t, 
  WF1 s -> In (a, f1, t) s -> f1 >= f -> apply s f a = Some t.
 intros. 
 induction s. inversion H0.
 destruct a0 as [[a2 f2] t2]. simpl.
 destruct (eq_nat_dec a a2); destruct (canRewrite_dec f2 f); simpl.
 - subst. destruct (eq_ty_dec t2 t). f_equal. auto.
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

Fixpoint apply_ty (s : Subst) (f : flavor) (t : ty) : ty :=
  match t with 
  | tycon => tycon
  | tyvar x => match apply s f x with
                  | Some t => t
                  | None   => tyvar x
               end
  | tyapp t1 t2 => tyapp (apply_ty s f t1) (apply_ty s f t2)
  end.

Definition selfapp (s : Subst) (f : flavor) : Subst := 
  map (fun e => 
   match e with 
    | (a,f1, t) => (a, f1, apply_ty s f t)
   end) s.

Definition tri s f y x := 
    match apply s f x with 
    | Some t => VarSet.In y (vars t)
    | None => False
    end.

(* From Triangular substitutions paper. *)

Definition wfs (s : Subst) := 
  forall a f, not ((clos_trans _ (tri s f)) a a). 

Lemma wfs_noids : forall s, WF1 s -> wfs s -> noids s.
  intros s H1 H. unfold noids. unfold WF2. unfold not. intros.
  unfold wfs in H. unfold not in H.
  destruct (R3 f) as [f' Hf']. apply (H a f').
  apply t_step. assert (apply s f' a = Some (tyvar a)).
  eapply apply_in. eauto. eauto. eauto. 
  unfold tri. rewrite H2. simpl. 
  VarSetDecide.fsetdec.
Qed.

Lemma wfs_selfapp : forall s f, WF1 s -> wfs s <-> wfs (selfapp s f).
Admitted.

Fixpoint apply_n (n : nat) (s : Subst) (f : flavor) (t : ty) : ty := 
  match n with 
  | 0 => t
  | S m => apply_ty s f (apply_n m s f t)
  end.


Definition IG1 s := forall f t, 
      exists n, apply_n n s f t = apply_n (S n) s f t.

(* I don't believe this. The n could depend on t, and there are an infinite number of these. 
Axiom IG1C : exists n, forall s f t, apply_n n s f t = apply_n (S n) s f t. *)

Lemma L2 : forall s s', IG1 s -> incl s' s ->  IG1 s'.
Admitted.



