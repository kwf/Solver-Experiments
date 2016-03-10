
Set Implicit Arguments.
Require Import Coq.Lists.List.
Require Import Notations.
Require Import Datatypes.
Require Import Logic.

Notation " [ ] " := nil (format "[ ]") : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

Definition commutative {X} (P : X -> X -> Prop) :=
  forall x y, P x y <-> P y x.

Lemma and_comm : commutative and.
Proof.
  unfold commutative. split; apply and_comm.
Qed.

Inductive with_each {X} (P : X -> X -> Prop) : X -> list X -> Prop :=
| WE_nil :
    forall x, with_each P x []
| WE_cons :
    forall x y ys, P x y -> with_each P x ys -> with_each P x (y :: ys).

Inductive all_diff_pairs
  {X} (P : X -> X -> Prop) : list X -> Prop :=
| ADP_nil :
    all_diff_pairs P []
| ADP_cons :
    forall x xs,
      with_each P x xs ->
      all_diff_pairs P xs ->
      all_diff_pairs P (x :: xs).

Lemma test_adp : all_diff_pairs eq [1; 1; 1].
Proof.
  repeat
    (apply ADP_cons;
     repeat (apply WE_cons;
             try (split; reflexivity));
     try (apply WE_nil; split; reflexivity)).
  apply ADP_nil.
Qed.

Inductive elem {X} : X -> list X -> Prop :=
| here : forall x ys, elem x (x :: ys)
| there : forall x y ys, elem x ys -> elem x (y :: ys).

Inductive filtered {X} (P: X -> Prop) : list X -> Prop :=
| filtered_nil : filtered P []
| filtered_yes : forall x xs, P x -> filtered P xs -> filtered P (x :: xs).

Lemma filtered_extract :
  forall X (x : X) (xs : list X) (P : X -> Prop),
    elem x xs -> filtered P xs -> P x.
Proof.
  intros X x xs P elem_x filtered_P.
  induction xs.
  - inversion elem_x.
  - inversion filtered_P; subst.
    inversion elem_x; subst.
    + apply H1.
    + apply (IHxs H3 H2).
Qed.

Definition neq {X} (a : X) (b : X) := a <> b.

Definition distinct {X} (xs : list X) := all_diff_pairs neq xs.

Lemma next_elem :
  forall X (a b : X) (xs : list X),
    a <> b -> elem a (b :: xs) -> elem a xs.
Proof.
  intros X a b xs a_neq_b elem_a_b_xs.
  inversion elem_a_b_xs; subst.
  exfalso; apply a_neq_b; reflexivity.
  apply H1.
Qed.

Lemma app_cons_not_nil :
  forall A (y : A) (xs zs : list A),
    [] <> xs ++ [y] ++ zs.
Proof.
  intros A y xs zs.
  destruct xs.
  - simpl. intros contra. inversion contra.
  - intros contra. inversion contra.
Qed.

Theorem elem_in_list :
  forall X (xs : list X) (a : X),
    elem a xs <->
    (exists ys zs,
       xs = ys ++ [a] ++ zs).
Proof.
  intros X xs a.
  split.
  - intros elem_a.
    induction elem_a as [| ? ? ? ? [ys' [zs' w]] ].
    + exists []. exists ys. reflexivity.
    + rewrite w. exists (y :: ys'). exists zs'. reflexivity.
  - intros [ys [zs w]].
    rewrite w. clear w.
    induction ys; simpl.
    + apply here.
    + apply there. apply IHys.
Qed.

Lemma iff_right :
  forall A B, (A <-> B) -> A -> B.
Proof.
  intros A B [R ?]; apply R.
Qed.

Lemma iff_left :
  forall A B, (A <-> B) -> B -> A.
Proof.
  intros A B [? L]; apply L.
Qed.

Lemma neq_sym :
  forall X (A B : X), (A <> B) -> (B <> A).
Proof.
  intros X A B H G.
  apply H. apply eq_sym. apply G.
Qed.

Theorem distinct_elem :
  forall X (ws : list X) (a b : X),
    distinct ws ->
    a <> b ->
    elem a ws ->
    elem b ws ->
    (exists xs ys zs,
       ws = xs ++ [a] ++ ys ++ [b] ++ zs \/
       ws = xs ++ [b] ++ ys ++ [a] ++ zs).
Proof.
  intros X ws a b distinct_ws a_neq_b elem_a.
  induction elem_a.
  - intros elem_b.
    inversion elem_b; subst.
    + exfalso. apply a_neq_b; reflexivity.
    + exists []; simpl.
      assert (split_b := iff_right (elem_in_list _ _) H1).
      destruct split_b as [ys' [zs' w]].
      rewrite w. exists ys'. exists zs'.
      left. reflexivity.
  - intros elem_b.
    inversion elem_b; subst.
    + exists []; simpl.
      assert (split_a := iff_right (elem_in_list _ _) elem_a).
      destruct split_a as [ys' [zs' w]].
      rewrite w. exists ys'. exists zs'.
      right. reflexivity.
    + inversion distinct_ws; subst.
      unfold distinct in IHelem_a.
      assert (apply_IH := IHelem_a H3 a_neq_b H1).
      destruct apply_IH as [xs' [ys' [zs' w]]].
      exists (y :: xs'). exists ys'. exists zs'.
      simpl. destruct w; [left | right];
             simpl in H; rewrite H; reflexivity.
Qed.

Lemma with_each_extract :
  forall X (P : X -> X -> Prop) (xs : list X) (a x : X),
    elem a xs ->
    with_each P x xs ->
    P x a.
Proof.
  intros X P xs a x elem_a we_x.
  induction we_x.
  - inversion elem_a; subst;
    inversion elem_b; subst;
    exfalso;
    try (apply a_neq_b; reflexivity);
    try (inversion H1).
  - inversion elem_a; subst.
    + apply H.
    + apply (IHwe_x H2).
Qed.

Theorem all_diff_pairs_extract :
  forall X (P : X -> X -> Prop) (xs : list X) (a b : X),
    commutative P ->
    distinct xs ->
    all_diff_pairs P xs ->
    a <> b ->
    elem a xs ->
    elem b xs ->
    P a b.
Proof.
  intros X P xs a b P_comm distinct_xs ADP_P_xs a_neq_b elem_a elem_b.
  - induction ADP_P_xs; subst.
    + exfalso.
      inversion elem_a.
    + inversion distinct_xs; subst.
      inversion elem_a; subst; inversion elem_b; subst.
      * exfalso; apply a_neq_b; reflexivity.
      * assert (elem_b' := next_elem (neq_sym a_neq_b) elem_b).
        apply (with_each_extract elem_b' H).
      * assert (elem_a' := next_elem a_neq_b elem_a).
        apply P_comm.
        apply (with_each_extract elem_a' H).
      * unfold distinct in IHADP_P_xs.
        apply (IHADP_P_xs H3 H4 H5).
Qed.

Inductive flavour :=
| G : flavour
| W : flavour.

Definition var := nat.
Definition const := nat.

Inductive ty :=
| ty_var   : var -> ty
| ty_const : const -> ty
| ty_app   : ty -> ty -> ty.

Inductive canon_eq :=
| canon : var -> flavour -> ty -> canon_eq.

Definition given_rewrites_all (f1 f2 : flavour) : Prop :=
  match f1 with
    | G => True
    | W => False
  end.

Definition R1 {X} (R : X -> X -> Prop) :=
  forall x y z, R x y -> R y z -> R x z.

Definition R2 {X} (R : X -> X -> Prop) :=
  forall f f1 f2, R f1 f /\ R f2 f -> R f1 f2 \/ R f2 f1.

Definition can_rewrite_rel {X} :=
  { R : X -> X -> Prop | R1 R /\ R2 R}.

Definition distinct_list X := {l : list X | distinct l}.

Definition substitution := distinct_list canon_eq.

Definition WF1 (can_rewrite : can_rewrite_rel) (S : substitution) :=
  match can_rewrite with exist R _ =>
    match S with exist l _ =>
      all_diff_pairs
        (fun x y =>
          match x, y with
            | canon a1 f1 t1, canon a2 f2 t2 =>
              a1 = a2 ->
              not (R f1 f2) /\
              not (R f2 f1)
          end) l
    end
  end.

Definition reflexive_eq (e : canon_eq) : Prop :=
  match e with
    | canon a _ (ty_var b) => a = b
    | _ => False
  end.

Definition WF2 (S : substitution) :=
  match S with exist l _ =>
    filtered (fun x => ~ reflexive_eq x) l
  end.

Definition get_subst (S : substitution) : list canon_eq :=
  match S with exist l _ => l end.

Definition use_rewrite_rel {X} (R : @can_rewrite_rel X) : (X -> X -> Prop) :=
  match R with exist r _ => r end.

Inductive all {X} (P : X -> Prop) : list X -> Prop :=
| all_nil : all P []
| all_cons : forall x xs, P x -> all P xs -> all P (x :: xs).

Definition none {X} (P : X -> Prop) := all (fun x => ~ P x).

Inductive unique {X} (P : X -> Prop) : list X -> Prop :=
| unique_here :
    forall x xs,
      P x -> none P xs -> unique P (x :: xs)
| unique_there :
    forall x xs,
      ~ P x -> unique P xs -> unique P (x :: xs).

Inductive some {X} (P : X -> Prop) : list X -> Prop :=
| some_here :
    forall x xs,
      P x -> some P (x :: xs)
| some_there :
    forall x xs,
      some P xs -> some P (x :: xs).

Inductive apply_subst_var
  (R : can_rewrite_rel)
  (S : substitution)
  (f : flavour)
  (a : var) : ty -> Prop :=
| apply_subst_var_no_match :
    none (fun x =>
            match x with
              | canon a' f' _ =>
                  a' = a /\
                  use_rewrite_rel R f' f
            end)
         (get_subst S) ->
    apply_subst_var R S f a (ty_var a).
| apply_subst_var_match :
    forall x,
      elem x (get_subst S) ->






