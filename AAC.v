(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** * Theory file for the aac_rewrite tactic

   We define several base classes to package associative and possibly
   commutative operators, and define a data-type for reified (or
   quoted) expressions (with morphisms).

   We then define a reflexive decision procedure to decide the
   equality of reified terms: first normalize reified terms, then
   compare them. This allows us to close transitivity steps
   automatically, in the [aac_rewrite] tactic.
   
   We restrict ourselves to the case where all symbols operate on a
   single fixed type. In particular, this means that we cannot handle
   situations like   

   [H: forall x y, nat_of_pos (pos_of_nat (x) + y) + x = ....]

   where one occurence of [+] operates on nat while the other one
   operates on positive. *)

Require Import Arith NArith. 
Require Import List.
Require Import FMapPositive FMapFacts.
Require Import RelationClasses Equality.
Require Export Morphisms.

Set Implicit Arguments.
Unset Automatic Introduction.
Open Scope signature_scope.

(** * Environments for the reification process: we use positive maps to index elements *)

Section sigma.
  Definition sigma := PositiveMap.t.
  Definition sigma_get A (null : A) (map : sigma A) (n : positive) : A :=
    match PositiveMap.find n map with 
      | None => null
      | Some x => x
    end.
  Definition sigma_add := @PositiveMap.add.
  Definition sigma_empty := @PositiveMap.empty.
End sigma.

(** * Packaging structures *)

(** ** Free symbols  *)
Module Sym.
  Section t.
  Context {X} {R : relation X} .
  
  (** type of an arity  *)
  Fixpoint type_of  (n: nat) :=
  match n with
    | O => X
    | S n => X -> type_of  n
  end.

  (** relation to be preserved at an arity  *)
  Fixpoint rel_of n : relation (type_of n) := 
    match n with
      | O => R
      | S n => respectful R (rel_of n)
    end.
  
  (** a symbol package contains an arity, 
     a value of the corresponding type, 
     and a proof that the value is a proper morphism *)
  Record pack  : Type := mkPack {
    ar : nat;
    value : type_of  ar;
    morph : Proper (rel_of ar) value
  }.

  (** helper to build default values, when filling reification environments *)
  Program Definition null (H: Equivalence R) (x : X)  := mkPack 0 x _.
    
  End t.

End Sym.

(** ** Associative commutative operations (commutative monoids) 
   
   See #<a href="Instances.html">Instances.v</a># for concrete instances of these classes.

*)

Class Op_AC (X:Type) (R: relation X) (plus: X -> X -> X) (zero:X) := {
  plus_compat:> Proper (R ==> R ==> R) plus;
  plus_neutral_left: forall x, R (plus zero x) x;
  plus_assoc: forall x y z, R (plus x (plus y z)) (plus (plus x y) z);
  plus_com: forall x y, R (plus x y) (plus y x)
}.

Module Sum.
  Section t.
  Context {X : Type} {R: relation X}.
  Class pack : Type := mkPack {
    plus : X -> X -> X;
    zero : X;
    opac :> @Op_AC X R plus zero
  }.
  End t.
End Sum.
  
    

(** ** Associative operations (monoids) *)
Class Op_A (X:Type) (R:relation X) (dot: X -> X -> X) (one: X) := {
  dot_compat:> Proper (R ==> R ==> R) dot;
  dot_neutral_left: forall x, R (dot one x) x;
  dot_neutral_right: forall x, R (dot x one) x;
  dot_assoc: forall x y z, R (dot x (dot y z)) (dot (dot x y) z)
}.


Module Prd.
  Section t.
  Context {X : Type} {R: relation X}.
  Class pack : Type := mkPack {
    dot : X -> X -> X;
    one : X;
    opa :> @Op_A X R dot one
  }.
  End t.
End Prd.


(** an helper lemma to derive an A class out of an AC one (not
   declared as an instance to avoid useless branches in typeclass
   resolution) *)
Lemma AC_A {X} {R:relation X} {EQ: Equivalence R} {plus} {zero} (op: Op_AC R plus zero): Op_A R plus zero.
Proof.
  split; try apply op.
   intros. rewrite plus_com. apply op.
Qed.



(** * Utilities for the evaluation function *)
Section copy.

  Context  {X} {R: relation X} {HR : @Equivalence X R} {plus} {zero} {op: @Op_AC X R plus zero}.

  (* copy n x = x+...+x (n times) *)
  Definition copy n x := Prect (fun _ => X) x (fun _ xn => plus x xn) n.
  
  Lemma copy_plus : forall n m x, R (copy (n+m) x) (plus (copy n x) (copy m x)).
  Proof.
    unfold copy.
    induction n using Pind; intros m x.
     rewrite Prect_base. rewrite <- Pplus_one_succ_l. rewrite Prect_succ. reflexivity.
     rewrite Pplus_succ_permute_l. rewrite 2Prect_succ. rewrite IHn. apply plus_assoc. 
  Qed.

  Global Instance copy_compat n: Proper (R ==> R) (copy n).
  Proof.
    unfold copy.
    induction n using Pind; intros x y H.
     rewrite 2Prect_base. assumption. 
     rewrite 2Prect_succ. apply plus_compat; auto. 
  Qed.

End copy.

(** * Utilities for positive numbers
   which we use as:
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

(** weak specification predicate for comparison functions: only the 'Eq' case is specified *)
Inductive compare_weak_spec A: A -> A -> comparison -> Prop :=
| pcws_eq: forall i, compare_weak_spec i i Eq
| pcws_lt: forall i j, compare_weak_spec i j Lt
| pcws_gt: forall i j, compare_weak_spec i j Gt.

Lemma pos_compare_weak_spec: forall i j, compare_weak_spec i j (pos_compare i j).
Proof. induction i; destruct j; simpl; try constructor; case (IHi j); intros; constructor. Qed.

Lemma idx_compare_reflect_eq: forall i j, idx_compare i j = Eq -> i=j.
Proof. intros i j. case (pos_compare_weak_spec i j); intros; congruence. Qed.


(** * Dependent types utilities *)
Notation cast T H u := (eq_rect _ T u _ H).

Section dep.
  Variable U: Type.
  Variable T: U -> Type.

  Lemma cast_eq: (forall u v: U, {u=v}+{u<>v}) -> 
    forall A (H: A=A) (u: T A), cast T H u = u.
  Proof. intros. rewrite <- Eqdep_dec.eq_rect_eq_dec; trivial. Qed. 

  Variable f: forall A B, T A -> T B -> comparison.
  Definition reflect_eqdep := forall A u B v (H: A=B), @f A B u v = Eq -> cast T H u = v.

  (* these lemmas have to remain transparent to get structural recursion
     in the lemma [tcompare_weak_spec] below *)
  Lemma reflect_eqdep_eq: reflect_eqdep -> forall A u v, @f A A u v = Eq -> u = v.
  Proof. intros H A u v He. apply (H _ _ _ _ eq_refl He). Defined. 

  Lemma reflect_eqdep_weak_spec: reflect_eqdep -> forall A u v, compare_weak_spec u v (@f A A u v).
  Proof.
    intros. case_eq (f u v); try constructor.
    intro H'. apply reflect_eqdep_eq in H'. subst. constructor. assumption.
  Defined.
End dep.


(** * Utilities about lists and multisets  *)

(** finite multisets are represented with ordered lists with multiplicities *)
Definition mset A := list (A*positive).

(** lexicographic composition of comparisons (this is a notation to keep it lazy) *)
Notation lex e f := (match e with Eq => f | _ => e end).   


Section lists.

  (** comparison function  *)
  Section c.
    Variables A B: Type.
    Variable compare: A -> B -> comparison.
    Fixpoint list_compare h k := 
      match h,k with
        | nil, nil => Eq
        | nil, _   => Lt
        | _,   nil => Gt
      | u::h, v::k => lex (compare u v) (list_compare h k)
      end.  
  End c.
  Definition mset_compare A B compare: mset A -> mset B -> comparison :=
    list_compare (fun un vm => let '(u,n) := un in let '(v,m) := vm in lex (compare u v) (pos_compare n m)).

  Section list_compare_weak_spec.
    Variable A: Type.
    Variable compare: A -> A -> comparison.
    Hypothesis Hcompare: forall u v, compare_weak_spec u v (compare u v).
    (* this lemma has to remain transparent to get structural recursion 
       in the lemma [tcompare_weak_spec] below *)
    Lemma list_compare_weak_spec: forall h k, compare_weak_spec h k (list_compare compare h k).
    Proof.
      induction h as [|u h IHh]; destruct k as [|v k]; simpl; try constructor.
      case (Hcompare u v); try constructor.
      case (IHh k); intros; constructor.
    Defined.
  End list_compare_weak_spec.

  Section mset_compare_weak_spec.
    Variable A: Type.
    Variable compare: A -> A -> comparison.
    Hypothesis Hcompare: forall u v, compare_weak_spec u v (compare u v).
    (* this lemma has to remain transparent to get structural recursion 
       in the lemma [tcompare_weak_spec] below *)
    Lemma mset_compare_weak_spec: forall h k, compare_weak_spec h k (mset_compare compare h k).
    Proof.
      apply list_compare_weak_spec.
      intros [u n] [v m].
       case (Hcompare u v); try constructor.
       case (pos_compare_weak_spec n m); try constructor.
    Defined.
  End mset_compare_weak_spec.

  (** (sorted) merging functions  *)
  Section m.
    Variable A: Type.
    Variable compare: A -> A -> comparison.

    Fixpoint merge_msets l1 :=
      match l1 with
        | nil => fun l2 => l2
        | (h1,n1)::t1 =>
          let fix merge_aux l2 :=
            match l2 with
              | nil => l1
              | (h2,n2)::t2 =>
                match compare h1 h2 with
                  | Eq => (h1,Pplus n1 n2)::merge_msets t1 t2
                  | Lt => (h1,n1)::merge_msets t1 l2
                  | Gt => (h2,n2)::merge_aux t2
                end
            end
            in merge_aux
      end.

    (** interpretation of a list with a constant and a binary operation *)
    Variable B: Type.
    Variable map: A -> B.
    Variable b2: B -> B -> B.
    Variable b0: B.
    Fixpoint fold_map l :=
      match l with
        | nil => b0
        | u::nil => map u
        | u::l => b2 (map u) (fold_map l)
      end.

    (** mapping and merging *)
    Variable merge: A -> list B -> list B.
    Fixpoint merge_map (l: list A): list B :=
      match l with
        | nil => nil
        | u::l => merge u (merge_map l)
      end.

  End m.

End lists.



(** * Reification, normalisation, and decision  *)
Section s.
  Context {X} {R: relation X} {E: @Equivalence X R}.
  Infix "==" := R (at level 80).

  (* We use environments to store the various operators and the
     morphisms.*)

  Variable e_sym: idx -> @Sym.pack X R.
  Variable e_prd: idx -> @Prd.pack X R.
  Variable e_sum: idx -> @Sum.pack X R.
  Hint Resolve e_sum e_prd: typeclass_instances.


  (** ** Almost normalised syntax
     a term in [T] is in normal form if:
     - sums do not contain sums
     - products do not contain products
     - there are no unary sums or products
     - lists and msets are lexicographically sorted according to the order we define below
     
     [vT n] denotes the set of term vectors of size [n] (the mutual dependency could be removed), 

     Note that [T] and [vT] depend on the [e_sym] environment (which
     contains, among other things, the arity of symbols)
     *)
  Inductive T: Type := 
  | sum: idx -> mset T -> T
  | prd: idx -> list T -> T
  | sym: forall i, vT (Sym.ar (e_sym i)) -> T
  with vT: nat -> Type :=
  | vnil: vT O
  | vcons: forall n, T -> vT n -> vT (S n).


  (** lexicographic rpo over the normalised syntax *)
  Fixpoint compare (u v: T) :=
    match u,v with 
      | sum i l, sum j vs => lex (idx_compare i j) (mset_compare compare l vs)
      | prd i l, prd j vs => lex (idx_compare i j) (list_compare compare l vs)
      | sym i l, sym j vs => lex (idx_compare i j) (vcompare l vs)
      | sum _ _, _        => Lt
      | _      , sum _ _  => Gt
      | prd _ _, _        => Lt
      | _      , prd _ _  => Gt
    end
  with vcompare i j (us: vT i) (vs: vT j) :=
    match us,vs with
      | vnil, vnil => Eq
      | vnil, _    => Lt
      | _,    vnil => Gt
      | vcons _ u us, vcons _ v vs => lex (compare u v) (vcompare us vs)
    end.


  (** we need to show that compare reflects equality
     (this is because we work with msets rather than lists with arities) 
    *)

  Lemma tcompare_weak_spec: forall (u v : T), compare_weak_spec u v (compare u v)
  with vcompare_reflect_eqdep: forall i us j vs (H: i=j), vcompare us vs = Eq -> cast vT H us = vs.
  Proof.
    induction u.
     destruct v; simpl; try constructor.
      case (pos_compare_weak_spec p p0); intros; try constructor.
      case (mset_compare_weak_spec compare tcompare_weak_spec m m0); intros; try constructor.
     destruct v; simpl; try constructor.
      case (pos_compare_weak_spec p p0); intros; try constructor.
      case (list_compare_weak_spec compare tcompare_weak_spec l l0); intros; try constructor.
     destruct v0; simpl; try constructor.
      case_eq (idx_compare i i0); intro Hi; try constructor.
      apply idx_compare_reflect_eq in Hi. symmetry in Hi. subst. (* the [symmetry] is required ! *)
      case_eq (vcompare v v0); intro Hv; try constructor.
      rewrite <- (vcompare_reflect_eqdep _ _ _ _ eq_refl Hv). constructor. 

    induction us; destruct vs; simpl; intros H Huv; try discriminate.
     apply cast_eq, eq_nat_dec. 
     injection H; intro Hn.
     revert Huv; case (tcompare_weak_spec t t0); intros; try discriminate. 
     symmetry in Hn. subst.   (* symmetry required *)
     rewrite <- (IHus _ _ eq_refl Huv). 
     apply cast_eq, eq_nat_dec.
  Qed.

  (** ** Evaluation from syntax to the abstract domain *)
  Fixpoint eval u: X :=
    match u with 
      | sum i l => fold_map (fun un => let '(u,n):=un in @copy _ (@Sum.plus _ _ (e_sum i)) n (eval u))
                            (@Sum.plus _ _ (e_sum i)) (@Sum.zero _ _ (e_sum i)) l 
      | prd i l => fold_map eval 
                            (@Prd.dot _ _ (e_prd i)) (@Prd.one _ _ (e_prd i)) l 
      | sym i v => @eval_aux _ v (Sym.value (e_sym i))
    end
  with eval_aux i (v: vT i): Sym.type_of  i -> X :=
    match v with
      | vnil => fun f => f
      | vcons _ u v => fun f => eval_aux v (f (eval u))
    end.


  Instance eval_aux_compat i (l: vT i): Proper (@Sym.rel_of X R i ==> R) (eval_aux l).
  Proof.
    induction l; simpl; repeat intro.
     assumption.
     apply IHl, H. reflexivity. 
  Qed.


  (** ** Normalisation *)

  (** auxiliary functions, to clean up sums and products  *)
  Definition sum' i (u: mset T): T :=
    match u with 
      | (u,xH)::nil => u
      | _ => sum i u
    end.
  Definition is_sum i (u: T): option (mset T) :=
    match u with 
      | sum j l => if eq_idx_bool j i then Some l else None
      | u => None
    end.
  Definition copy_mset n (l: mset T): mset T :=
    match n with 
      | xH => l
      | _ => List.map (fun vm => let '(v,m):=vm in (v,Pmult n m)) l
    end.
  Definition sum_to_mset i (u: T) n := 
    match is_sum i u with 
      | Some l' => copy_mset n l' 
      | None => (u,n)::nil 
    end.

  Definition prd' i (u: list T): T :=
    match u with 
      | u::nil => u
      | _ => prd i u
    end.
  Definition is_prd i (u: T): option (list T) :=
    match u with 
      | prd j l => if eq_idx_bool j i then Some l else None
      | u => None
    end.
  Definition prd_to_list i (u: T) := 
    match is_prd i u with
      | Some l' => l' 
      | None => u::nil 
    end.


  (** we deduce the normalisation function *)
  Fixpoint norm u :=
    match u with 
      | sum i l => sum' i (merge_map (fun un l => let '(u,n):=un in 
                                      merge_msets compare (sum_to_mset i (norm u) n) l) l)
      | prd i l => prd' i (merge_map (fun u l => prd_to_list i (norm u) ++ l) l)
      | sym i l => sym i (vnorm l)
    end
  with vnorm i (l: vT i): vT i := 
    match l with
      | vnil => vnil
      | vcons _ u l => vcons (norm u) (vnorm l)
    end.


  (** ** Correctness *)

  (** auxiliary lemmas about sums  *)
  Lemma sum'_sum i (l: mset T): eval (sum' i l) ==eval (sum i l) .
  Proof. 
    intros i [|? [|? ?]].
     reflexivity.
     destruct p; destruct p; simpl; reflexivity.
     destruct p; destruct p; simpl; reflexivity.
  Qed.

  Lemma eval_sum_cons i n a (l: mset T): 
    (eval (sum i ((a,n)::l))) == (@Sum.plus _ _ (e_sum i) (@copy _ (@Sum.plus _ _ (e_sum i)) n (eval a)) (eval (sum i l))).
  Proof.
    intros i n a [|[b m] l]; simpl. 
     rewrite plus_com, plus_neutral_left. reflexivity.
     reflexivity.
  Qed.        

  Lemma eval_sum_app i (h k: mset T):  eval (sum i (h++k)) == @Sum.plus _ _ (e_sum i) (eval (sum i h)) (eval (sum i k)).
  Proof.
    induction h; intro k. 
     simpl. rewrite plus_neutral_left. reflexivity.
     simpl app. destruct a. rewrite 2 eval_sum_cons, IHh, plus_assoc. reflexivity.
  Qed.        

  Lemma eval_merge_sum i (h k: mset T): 
    eval (sum i (merge_msets compare h k)) == @Sum.plus _ _ (e_sum i) (eval (sum i h)) (eval (sum i k)).
  Proof.
    induction h as [|[a n] h IHh]; intro k. 
     simpl. rewrite plus_neutral_left. reflexivity.
     induction k as [|[b m] k IHk].
      simpl. setoid_rewrite plus_com. rewrite plus_neutral_left. reflexivity.
      simpl merge_msets. rewrite eval_sum_cons. destruct (tcompare_weak_spec a b) as [a|a b|a b]. 
       rewrite 2eval_sum_cons. rewrite IHh. rewrite <- plus_assoc. setoid_rewrite plus_assoc at 3.
       setoid_rewrite plus_com at 5. rewrite !plus_assoc. rewrite copy_plus. reflexivity.

       rewrite eval_sum_cons. rewrite IHh. apply plus_assoc.

       rewrite <- eval_sum_cons. setoid_rewrite eval_sum_cons at 3. 
       rewrite plus_com, <- plus_assoc. rewrite plus_com in IHk. rewrite <- IHk.
       rewrite eval_sum_cons. apply plus_compat; reflexivity. 
  Qed.

  Inductive sum_spec: T -> option (mset T) -> Prop :=
  | ss_sum1: forall i l, sum_spec (sum i l) (Some l)
  | ss_sum2: forall j i l, i<>j -> sum_spec (sum i l) None
  | ss_prd: forall i l, sum_spec (prd i l) None
  | ss_sym: forall i l, sum_spec (@sym i l) None.
  Lemma is_sum_spec: forall i (a: T), sum_spec a (is_sum i a).
  Proof.
    intros i [j l|j l|j l]; simpl; try constructor.
    case eq_idx_spec; intro.
     subst. constructor.
     econstructor. eassumption.
  Qed.

  Lemma eval_is_sum: forall i (a: T) k, is_sum i a = Some k -> eval (sum i k) = eval a.
  Proof.
    intros i [j l|j l|j l] k; simpl is_sum; try (intro; discriminate).
    case eq_idx_spec; intros ? H. 
     injection H. clear H. intros <-. congruence. 
     discriminate.
  Qed.

  Lemma copy_mset' n (l: mset T): 
    copy_mset n l = List.map (fun vm => let '(v,m):=vm in (v,Pmult n m)) l.
  Proof.
    intros. destruct n; try reflexivity.
    simpl. induction l as [|[a l] IHl]; simpl; congruence. 
  Qed.

  
  Lemma copy_mset_succ i n (l: mset T): 
    eval (sum i (copy_mset (Psucc n) l)) == @Sum.plus _ _ (e_sum i) (eval (sum i l)) (eval (sum i (copy_mset n l))).
  Proof.
    intros. rewrite 2copy_mset'.
    induction l as [|[a m] l IHl].
     simpl eval at 2. rewrite plus_neutral_left. destruct n; reflexivity.
     simpl map. rewrite ! eval_sum_cons. rewrite IHl. 
     rewrite Pmult_Sn_m. rewrite copy_plus. rewrite <- !plus_assoc. apply plus_compat; try reflexivity.
     setoid_rewrite plus_com at 3. rewrite <- !plus_assoc. apply plus_compat; try reflexivity. apply plus_com. 
  Qed.

  Lemma eval_sum_to_mset: forall i n a, eval (sum i (sum_to_mset i a n)) == @copy _  (@Sum.plus _ _ (e_sum i)) n (eval a).
  Proof.
    intros. unfold sum_to_mset.
    case_eq (is_sum i a).
     intros k Hk. induction n using Pind. 
       simpl copy_mset. rewrite (eval_is_sum _ _ Hk). reflexivity.
       rewrite copy_mset_succ. rewrite IHn. rewrite (eval_is_sum _ _ Hk).
       unfold copy at 2. rewrite Prect_succ. reflexivity.
     reflexivity.
  Qed.


  (** auxiliary lemmas about products  *)
  Lemma prd'_prd i (l: list T): eval (prd' i l) == eval (prd i l).
  Proof. intros i [|? [|? ?]]; reflexivity. Qed.

  Lemma eval_prd_cons i a (l: list T): eval (prd i (a::l)) == @Prd.dot _ _ (e_prd i) (eval a) (eval (prd i l)).
  Proof.
    intros i a [|b l]; simpl. 
     rewrite dot_neutral_right. reflexivity.
     reflexivity.
  Qed.        

  Lemma eval_prd_app i (h k: list T): eval (prd i (h++k)) == @Prd.dot _ _ (e_prd i) (eval (prd i h)) (eval (prd i k)).
  Proof.
    induction h; intro k. 
     simpl. rewrite dot_neutral_left. reflexivity.
     simpl app. rewrite 2 eval_prd_cons, IHh, dot_assoc. reflexivity.
  Qed.        

  Lemma eval_is_prd: forall i (a: T) k, is_prd i a = Some k -> eval (prd i k) = eval a.
  Proof.
    intros i [j l|j l|j l] k; simpl is_prd; try (intro; discriminate).
    case eq_idx_spec; intros ? H. 
     injection H. clear H. intros <-. subst. congruence.
     discriminate.
  Qed.

  Lemma eval_prd_to_list: forall i a, eval (prd i (prd_to_list i a)) = eval a.
  Proof.
    intros. unfold prd_to_list.
    case_eq (is_prd i a).
     intros k Hk. apply eval_is_prd. assumption.
     reflexivity.
  Qed.


  (** correctness of the normalisation function *)
  Theorem eval_norm: forall u, eval (norm u) == eval u
    with eval_norm_aux: forall i (l: vT i) (f: Sym.type_of i), 
      Proper (@Sym.rel_of X R i) f -> eval_aux (vnorm l) f == eval_aux l f.
  Proof.
    induction u.
     simpl norm. rewrite sum'_sum. induction m as [|[u n] m IHm]. 
      reflexivity.
      simpl merge_map. rewrite eval_merge_sum.
      rewrite eval_sum_to_mset, IHm, eval_norm.
      rewrite eval_sum_cons. reflexivity.

     simpl norm. rewrite prd'_prd. induction l. 
      reflexivity.
      simpl merge_map.
      rewrite eval_prd_app.
      rewrite eval_prd_to_list, IHl, eval_norm.
      rewrite eval_prd_cons. reflexivity.

     simpl. apply eval_norm_aux, Sym.morph. 


    induction l; simpl; intros f Hf.
     reflexivity.
     rewrite eval_norm. apply IHl, Hf. reflexivity.
  Qed.

  (** corollaries, for goal normalisation or decision *)
  Lemma normalise: forall (u v: T), eval (norm u) == eval (norm v) -> eval u == eval v.
  Proof. intros u v. rewrite 2 eval_norm. trivial. Qed.
    
  Lemma compare_reflect_eq: forall u v, compare u v = Eq -> eval u == eval v.
  Proof. intros u v. case (tcompare_weak_spec u v); intros; try congruence. reflexivity. Qed.

  Lemma decide: forall (u v: T), compare (norm u) (norm v) = Eq -> eval u == eval v.
  Proof. intros u v H. apply normalise. apply compare_reflect_eq. apply H. Qed.

End s.
Declare ML Module "aac_tactics".
