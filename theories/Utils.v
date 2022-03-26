(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** * Utility functions and results *)

From Coq Require Import Arith NArith List.
From Coq Require Import FMapPositive FMapFacts RelationClasses Equality.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** ** Utilities for positive numbers

 We use positive numbers as:
 - indices for morphisms and symbols
 - multiplicity of terms in sums
*)

Notation idx := positive.

Fixpoint eq_idx_bool i j :=
  match i,j with
    | xH, xH => true
    | xO i, xO j => eq_idx_bool i j
    | xI i, xI j => eq_idx_bool i j
    | _, _ => false
  end.

Fixpoint idx_compare i j :=
  match i,j with
    | xH, xH => Eq
    | xH, _ => Lt
    | _, xH => Gt
    | xO i, xO j => idx_compare i j
    | xI i, xI j => idx_compare i j
    | xI _, xO _ => Gt
    | xO _, xI _ => Lt
  end.

Notation pos_compare := idx_compare (only parsing).

(** specification predicate for boolean binary functions *)
Inductive decide_spec {A} {B} (R : A -> B -> Prop) (x : A) (y : B) : bool -> Prop :=
| decide_true : R x y -> decide_spec R x y true
| decide_false : ~(R x y) -> decide_spec R x y false.

Lemma eq_idx_spec : forall i j, decide_spec (@eq _) i j (eq_idx_bool i j).
Proof.
  induction i; destruct j; simpl; try (constructor; congruence).
   case (IHi j); constructor; congruence.
   case (IHi j); constructor; congruence.
Qed.

(** weak specification predicate for comparison functions: only the [Eq] case is specified *)
Inductive compare_weak_spec A: A -> A -> comparison -> Prop :=
| pcws_eq: forall i, compare_weak_spec i i Eq
| pcws_lt: forall i j, compare_weak_spec i j Lt
| pcws_gt: forall i j, compare_weak_spec i j Gt.

Lemma pos_compare_weak_spec: forall i j, compare_weak_spec i j (pos_compare i j).
Proof.
  induction i; destruct j; simpl; try constructor;
    case (IHi j); intros; constructor.
Qed.

Lemma idx_compare_reflect_eq: forall i j, idx_compare i j = Eq -> i=j.
Proof. intros i j. case (pos_compare_weak_spec i j); intros; congruence. Qed.

(** ** Dependent types utilities *)

Notation cast T H u := (eq_rect _ T u _ H).

Section dep.
  Variable U: Type.
  Variable T: U -> Type.

  Lemma cast_eq: (forall u v: U, {u=v}+{u<>v}) -> forall A (H: A=A) (u: T A), cast T H u = u.
  Proof. intros. rewrite <- Eqdep_dec.eq_rect_eq_dec; trivial. Qed.

  Variable f: forall A B, T A -> T B -> comparison.
  Definition reflect_eqdep := forall A u B v (H: A=B), @f A B u v = Eq -> cast T H u = v.

  (** these lemmas have to remain transparent to get structural recursion
    in the lemma [tcompare_weak_spec] below *)
  Lemma reflect_eqdep_eq: reflect_eqdep ->
    forall A u v, @f A A u v = Eq -> u = v.
  Proof. intros H A u v He. apply (H _ _ _ _ eq_refl He). Defined.

  Lemma reflect_eqdep_weak_spec: reflect_eqdep ->
    forall A u v, compare_weak_spec u v (@f A A u v).
  Proof.
    intros. case_eq (f u v); try constructor.
    intro H'. apply reflect_eqdep_eq in H'. subst. constructor. assumption.
  Defined.
End dep.

(** ** Utilities about (non-empty) lists and multisets  *)

#[universes(template)]
Inductive nelist (A : Type) : Type :=
| nil : A -> nelist A
| cons : A -> nelist A -> nelist A.

Register nil as aac_tactics.nelist.nil.
Register cons as aac_tactics.nelist.cons.

Notation "x :: y" := (cons x y).

Fixpoint nelist_map (A B: Type) (f: A -> B) l :=
  match l with
    | nil x => nil ( f x)
    | cons x l => cons ( f x) (nelist_map  f l)
  end.

Fixpoint appne  A l l' : nelist A :=
  match l with
    nil x => cons x l'
    | cons t q => cons t (appne A q l')
  end.

Notation "x ++ y" := (appne x y).

(** finite multisets are represented with ordered lists with multiplicities *)
Definition mset A := nelist (A*positive).

(** lexicographic composition of comparisons (this is a notation to keep it lazy) *)
Notation lex e f := (match e with Eq => f | _ => e end).  

Section lists.

  (** comparison functions *)
  Section c.
    Variables A B: Type.
    Variable compare: A -> B -> comparison.
    Fixpoint list_compare h k :=
      match h,k with
        | nil x, nil y => compare x y
        | nil x, _   => Lt
        | _,   nil x => Gt
        | u::h, v::k => lex (compare u v) (list_compare h k)
      end. 
  End c.

  Definition mset_compare A B compare: mset A -> mset B -> comparison :=
    list_compare (fun un vm =>
      let '(u,n) := un in
        let '(v,m) := vm in
        lex (compare u v) (pos_compare n m)).

  Section list_compare_weak_spec.
    Variable A: Type.
    Variable compare: A -> A -> comparison.
    Hypothesis Hcompare: forall u v, compare_weak_spec u v (compare u v).
    (** this lemma has to remain transparent to get structural recursion
       in the lemma [tcompare_weak_spec] below **)
    Lemma list_compare_weak_spec: forall h k,
      compare_weak_spec h k (list_compare compare h k).
    Proof.
      induction h as [|u h IHh]; destruct k as [|v k]; simpl; try constructor.

      case (Hcompare a a0 ); try constructor.
      case (Hcompare u v ); try constructor.
      case (IHh k); intros; constructor.
    Defined.
  End list_compare_weak_spec.

  Section mset_compare_weak_spec.
    Variable A: Type.
    Variable compare: A -> A -> comparison.
    Hypothesis Hcompare: forall u v, compare_weak_spec u v (compare u v).
    (** this lemma has to remain transparent to get structural recursion
      in the lemma [tcompare_weak_spec] below *)
    Lemma mset_compare_weak_spec: forall h k,
      compare_weak_spec h k (mset_compare compare h k).
    Proof.
      apply list_compare_weak_spec.
      intros [u n] [v m].
       case (Hcompare u v); try constructor.
       case (pos_compare_weak_spec n m); try constructor.
    Defined.
  End mset_compare_weak_spec.

  (** (sorted) merging functions *)
  Section m.
    Variable A: Type.
    Variable compare: A -> A -> comparison.
    Definition insert n1 h1 :=
      let fix insert_aux l2 :=
      match l2 with
        | nil (h2,n2) =>
          match compare h1 h2 with
            | Eq => nil (h1,Pplus n1 n2)
            | Lt => (h1,n1):: nil (h2,n2)
            | Gt => (h2,n2):: nil (h1,n1)
          end
        | (h2,n2)::t2 =>
          match compare h1 h2 with
            | Eq => (h1,Pplus n1 n2):: t2
            | Lt => (h1,n1)::l2
            | Gt => (h2,n2)::insert_aux t2
          end
      end
      in insert_aux.
   
    Fixpoint merge_msets l1 :=
      match l1 with
        | nil (h1,n1) => fun l2 => insert n1 h1 l2
        | (h1,n1)::t1 =>
          let fix merge_aux l2 :=
            match l2 with
               | nil (h2,n2) =>
                match compare h1 h2 with
                  | Eq => (h1,Pplus n1 n2) :: t1
                  | Lt => (h1,n1):: merge_msets t1 l2
                  | Gt => (h2,n2)::  l1
                end
              | (h2,n2)::t2 =>
                match compare h1 h2 with
                  | Eq => (h1,Pplus n1 n2)::merge_msets t1 t2
                  | Lt => (h1,n1)::merge_msets t1 l2
                  | Gt => (h2,n2)::merge_aux t2
                end
            end
            in merge_aux
      end.

    (** setting all multiplicities to one, in order to implement idempotency *)
    Definition reduce_mset: mset A -> mset A := nelist_map (fun x => (fst x,xH)).

    (** interpretation of a list with a constant and a binary operation *)
    Variable B: Type.
    Variable map: A -> B.
    Variable b2: B -> B -> B.
    Fixpoint fold_map l :=
      match l with
        | nil x => map x
        | u::l => b2 (map u) (fold_map l)
      end.

    (** mapping and merging *)

    Variable merge: A -> nelist B -> nelist B.
    Fixpoint merge_map (l: nelist A): nelist B :=
      match l with
        | nil x => nil (map x)
        | u::l => merge u (merge_map l)
      end.

    Variable ret : A -> B.
    Variable bind : A -> B -> B.
    Fixpoint fold_map' (l : nelist A) : B :=
      match l with
        | nil x => ret x
        | u::l => bind u (fold_map' l)
      end.

  End m.
End lists.
