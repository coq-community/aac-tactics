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
   equality of reified terms: first normalise reified terms, then
   compare them. This allows us to close transitivity steps
   automatically, in the [aac_rewrite] tactic.
  
   We restrict ourselves to the case where all symbols operate on a
   single fixed type. In particular, this means that we cannot handle
   situations like  

   [H: forall x y, nat_of_pos (pos_of_nat (x) + y) + x = ....]

   where one occurrence of [+] operates on nat while the other one
   operates on positive. *)

Require Import Arith NArith.
Require Import List.
Require Import FMapPositive FMapFacts.
Require Import RelationClasses Equality.
Require Export Morphisms.

Set Implicit Arguments.

Local Open Scope signature_scope.

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


(** * Classes for properties of operators *)

Class Associative (X:Type) (R:relation X) (dot: X -> X -> X) :=
  law_assoc : forall x y z, R (dot x (dot y z)) (dot (dot x y) z).
Class Commutative (X:Type) (R: relation X) (plus: X -> X -> X) :=
  law_comm: forall x y, R (plus x y) (plus y x).
Class Unit (X:Type) (R:relation X) (op : X -> X -> X) (unit:X) := {
  law_neutral_left: forall x, R (op unit x) x;
  law_neutral_right: forall x, R (op x unit) x
}.


(** Class used to find the equivalence relation on which operations
   are A or AC, starting from the relation appearing in the goal *)

Class AAC_lift X (R: relation X) (E : relation X) := {
  aac_lift_equivalence : Equivalence E;
  aac_list_proper : Proper (E ==> E ==> iff) R
}.

(** simple instances, when we have a subrelation, or an equivalence *)

Instance aac_lift_subrelation {X} {R} {E} {HE: Equivalence E}
  {HR: @Transitive X R} {HER: subrelation E R}: AAC_lift  R E | 3.
Proof.
  constructor; trivial.
  intros ? ? H ? ? H'. split; intro G.
   rewrite <- H, G. apply HER, H'.
   rewrite H, G. apply HER. symmetry. apply H'.
Qed.

Instance aac_lift_proper {X} {R : relation X} {E} {HE: Equivalence E}
  {HR: Proper (E==>E==>iff) R}: AAC_lift  R E | 4 := {}.



Module Internal.

(** * Utilities for the evaluation function *)

Section copy.

  Context {X} {R} {HR: @Equivalence X R} {plus}
   (op: Associative R plus) (op': Commutative R plus) (po: Proper (R ==> R ==> R) plus).

  (* copy n x = x+...+x (n times) *)
  Fixpoint copy' n x := match n with
                         | xH => x
                         | xI n => let xn := copy' n x in plus (plus xn xn) x
                         | xO n => let xn := copy' n x in (plus xn xn)
                       end.
  Definition copy n x :=  Prect (fun _ => X) x (fun _ xn => plus x xn) n.
     
  Lemma copy_plus : forall n m x, R (copy (n+m) x) (plus (copy n x) (copy m x)).
  Proof.
    unfold copy.
    induction n using Pind; intros m x.
     rewrite Prect_base. rewrite <- Pplus_one_succ_l. rewrite Prect_succ. reflexivity. 
     rewrite Pplus_succ_permute_l. rewrite 2Prect_succ. rewrite IHn. apply op.
  Qed.
  Lemma copy_xH : forall x, R (copy 1 x) x.
  Proof. intros; unfold copy; rewrite Prect_base. reflexivity. Qed.
  Lemma copy_Psucc : forall n x, R (copy (Psucc n) x) (plus x (copy n x)).
  Proof. intros; unfold copy; rewrite Prect_succ. reflexivity. Qed.

  Global Instance copy_compat n: Proper (R ==> R) (copy n).
  Proof.
    unfold copy.
    induction n using Pind; intros x y H.
     rewrite 2Prect_base. assumption.
     rewrite 2Prect_succ. apply po; auto.
  Qed.

End copy.

(** * Utilities for positive numbers
   which we use as:
     - indices for morphisms and symbols
     - multiplicity of terms in sums *)

Local Notation idx := positive.

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

Local Notation pos_compare := idx_compare (only parsing).

(** Specification predicate for boolean binary functions *)
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

Local Notation cast T H u := (eq_rect _ T u _ H).

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



(** * Utilities about (non-empty) lists and multisets  *)

Inductive nelist (A : Type) : Type :=
| nil : A -> nelist A
| cons : A -> nelist A -> nelist A.

Local Notation "x :: y" := (cons x y).

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

Local Notation "x ++ y" := (appne x y).

(** finite multisets are represented with ordered lists with multiplicities *)
Definition mset A := nelist (A*positive).

(** lexicographic composition of comparisons (this is a notation to keep it lazy) *)
Local Notation lex e f := (match e with Eq => f | _ => e end).  


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
    (* this lemma has to remain transparent to get structural recursion
       in the lemma [tcompare_weak_spec] below *)
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
    (* this lemma has to remain transparent to get structural recursion
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

  (** (sorted) merging functions  *)

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

(** * Packaging structures *)

(** ** free symbols  *)

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
    value :> type_of  ar;
    morph : Proper (rel_of ar) value
  }.

  (** helper to build default values, when filling reification environments *)
  Definition null: pack := mkPack 1 (fun x => x) (fun _ _ H => H).
   
  End t.

End Sym.
  
(** ** binary operations *)

Module Bin.
  Section t.
    Context {X} {R: relation X}.

    Record pack := mk_pack {
      value:> X -> X -> X;
      compat: Proper (R ==> R ==> R) value;
      assoc: Associative R value;
      comm: option (Commutative R value)
    }.
  End t.
  (*    See #<a href="Instances.html">Instances.v</a># for concrete instances of these classes. *)

End Bin.


(** * Reification, normalisation, and decision  *)

Section s.
  Context {X} {R: relation X} {E: @Equivalence X R}.
  Infix "==" := R (at level 80).

  (* We use environments to store the various operators and the
     morphisms.*)
 
  Variable e_sym: idx -> @Sym.pack X R.
  Variable e_bin: idx -> @Bin.pack X R.

 
  (** packaging units (depends on e_bin) *)

  Record unit_of u := mk_unit_for {
    uf_idx: idx;
    uf_desc: Unit R (Bin.value (e_bin uf_idx)) u
  }.

  Record unit_pack := mk_unit_pack {
    u_value:> X;
    u_desc: list (unit_of u_value)
  }.
  Variable e_unit: positive -> unit_pack.
 
  Hint Resolve e_bin e_unit: typeclass_instances.

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
  | prd: idx -> nelist T -> T
  | sym: forall i, vT (Sym.ar (e_sym i)) -> T
  | unit : idx -> T
  with vT: nat -> Type :=
  | vnil: vT O
  | vcons: forall n, T -> vT n -> vT (S n).


  (** lexicographic rpo over the normalised syntax *)
  Fixpoint compare (u v: T) :=
    match u,v with
      | sum i l, sum j vs => lex (idx_compare i j) (mset_compare compare l vs)
      | prd i l, prd j vs => lex (idx_compare i j) (list_compare compare l vs)
      | sym i l, sym j vs => lex (idx_compare i j) (vcompare l vs)
      | unit i , unit j => idx_compare i j
      | unit _ , _        => Lt
      | _      , unit _  => Gt
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
 


  (** ** Evaluation from syntax to the abstract domain *)

  Fixpoint eval u: X :=
    match u with
      | sum i l => let o := Bin.value (e_bin i) in
        fold_map (fun un => let '(u,n):=un in @copy _ o n (eval u)) o l
      | prd i l => fold_map eval (Bin.value (e_bin i)) l
      | sym i v => eval_aux v (Sym.value (e_sym i))
      | unit i  => e_unit i
    end
  with eval_aux i (v: vT i): Sym.type_of i -> X :=
    match v with
      | vnil => fun f => f
      | vcons _ u v => fun f => eval_aux v (f (eval u))
    end.

  (** we need to show that compare reflects equality (this is because
     we work with msets rather than lists with arities) *)
  Lemma tcompare_weak_spec: forall (u v : T), compare_weak_spec u v (compare u v)
  with vcompare_reflect_eqdep: forall i us j vs (H: i=j), vcompare us vs = Eq -> cast vT H us = vs.
  Proof.
    induction u.
     destruct v; simpl; try constructor.
      case (pos_compare_weak_spec p p0); intros; try constructor.
      case (mset_compare_weak_spec compare tcompare_weak_spec m m0); intros; try constructor.
     destruct v; simpl; try constructor.
      case (pos_compare_weak_spec p p0); intros; try constructor.
      case (list_compare_weak_spec compare tcompare_weak_spec n n0); intros; try constructor.
     destruct v0; simpl; try constructor.
      case_eq (idx_compare i i0); intro Hi; try constructor.
      apply idx_compare_reflect_eq in Hi. symmetry in Hi. subst. (* the [symmetry] is required ! *)
      case_eq (vcompare v v0); intro Hv; try constructor.
      rewrite <- (vcompare_reflect_eqdep _ _ _ _ eq_refl Hv). constructor.
     destruct v; simpl; try constructor.
      case_eq (idx_compare p p0); intro Hi; try constructor.
      apply idx_compare_reflect_eq in Hi. symmetry in Hi. subst.  constructor.

    induction us; destruct vs; simpl; intros H Huv; try discriminate.
     apply cast_eq, eq_nat_dec.
     injection H; intro Hn.
     revert Huv; case (tcompare_weak_spec t t0); intros; try discriminate.
     symmetry in Hn. subst.   (* symmetry required *)
     rewrite <- (IHus _ _ eq_refl Huv).
     apply cast_eq, eq_nat_dec.
  Qed.

  Instance eval_aux_compat i (l: vT i): Proper (@Sym.rel_of X R i ==> R) (eval_aux l).
  Proof.
    induction l; simpl; repeat intro.
     assumption.
     apply IHl, H. reflexivity.
  Qed.

 
  (* is [i] a unit for [j] ? *)
  Definition is_unit_of j i :=
    List.existsb (fun p => eq_idx_bool j (uf_idx p)) (u_desc (e_unit i)).

  (* is [i] commutative ? *)
  Definition is_commutative i :=
    match Bin.comm (e_bin i) with Some _ => true | None => false end.


  (** ** Normalisation *)

  Inductive discr {A} : Type :=
  | Is_op : A -> discr
  | Is_unit : idx -> discr
  | Is_nothing : discr .
 
  (* This is called sum in the std lib *)
  Inductive m {A} {B} :=
  | left : A -> m
  | right : B -> m.

  Definition comp A B (merge : B -> B -> B) (l : B) (l' : @m A B) : @m A B :=
    match l' with
      | left _ => right l
      | right l' => right (merge l l')
    end.
 
  (** auxiliary functions, to clean up sums  *)

  Section sums.
    Variable i : idx.
    Variable is_unit : idx -> bool.

    Definition sum' (u: mset T): T :=
      match u with
        | nil (u,xH) => u
        | _ => sum i u
      end.

    Definition is_sum  (u: T) : @discr (mset T) :=
    match u with
      | sum j l => if eq_idx_bool j i then Is_op l else Is_nothing
      | unit j => if is_unit j   then Is_unit j else Is_nothing
      | u => Is_nothing
    end.

    Definition copy_mset n (l: mset T): mset T :=
      match n with
        | xH => l
        | _ => nelist_map (fun vm => let '(v,m):=vm in (v,Pmult n m)) l
      end.
   
    Definition return_sum  u n :=
      match is_sum  u with
        | Is_nothing => right (nil (u,n))
        | Is_op l' =>  right (copy_mset n l')
        | Is_unit j => left j
      end.
   
    Definition add_to_sum u n (l : @m idx (mset T))  :=
      match is_sum  u with
        | Is_nothing => comp (merge_msets compare) (nil (u,n)) l
        | Is_op l' => comp (merge_msets compare) (copy_mset n l') l
        | Is_unit _ => l
    end.


    Definition norm_msets_ norm  (l: mset T) :=
    fold_map'
    (fun un => let '(u,n) := un in  return_sum  (norm u) n)
    (fun un l => let '(u,n) := un in  add_to_sum  (norm u) n l) l.


  End sums.
 
  (** similar functions for products *)

  Section prds.

    Variable i : idx.
    Variable is_unit : idx -> bool.
    Definition prd'  (u: nelist T): T :=
    match u with
      | nil u => u
      | _ => prd i u
    end.

    Definition is_prd (u: T) : @discr (nelist T) :=
    match u with
      | prd j l => if eq_idx_bool j i then Is_op l else Is_nothing
      | unit j => if is_unit j  then Is_unit j else Is_nothing
      | u => Is_nothing
    end.
 
   
    Definition return_prd u :=
      match is_prd u with
        | Is_nothing => right (nil (u))
        | Is_op l' =>  right (l')
        | Is_unit j => left j
      end.
   
    Definition add_to_prd  u  (l : @m idx (nelist T))  :=
      match is_prd  u with
        | Is_nothing => comp (@appne T) (nil (u)) l
        | Is_op l' => comp (@appne T) (l') l
        | Is_unit _ => l
      end.

    Definition norm_lists_ norm (l : nelist T) :=
    fold_map'
    (fun u => return_prd  (norm u))
    (fun u l => add_to_prd (norm u) l) l.


  End prds.


  Definition run_list x := match x with
                        | left n => nil (unit n)
                        | right l => l
                      end.
 
  Definition norm_lists norm i l :=
    let is_unit := is_unit_of i in
      run_list (norm_lists_ i is_unit norm l).

  Definition run_msets x := match x with
                        | left n => nil (unit n, xH)
                        | right l => l
                      end.
 
  Definition norm_msets norm i l :=
    let is_unit := is_unit_of i in
      run_msets (norm_msets_ i is_unit norm l).
 
  Fixpoint norm u {struct u}:=
    match u with
      | sum i l => if is_commutative i then sum' i (norm_msets norm i l)  else u
      | prd i l => prd' i (norm_lists norm i l)
      | sym i l => sym i (vnorm l)
      | unit i => unit i
    end
  with vnorm i (l: vT i): vT i :=
    match l with
      | vnil => vnil
      | vcons _ u l => vcons (norm u) (vnorm l)
    end.

  (** ** Correctness *)

  Lemma is_unit_of_Unit  : forall i j : idx,
   is_unit_of i j = true -> Unit R (Bin.value (e_bin i)) (eval (unit j)).
  Proof.
    intros. unfold is_unit_of in H.
    rewrite existsb_exists in H.
    destruct H as [x [H H']].
    revert H' ; case (eq_idx_spec); [intros H' _ ; subst| intros _ H'; discriminate].
    simpl. destruct x. simpl. auto.
  Qed.
 
  Instance Binvalue_Commutative i (H :  is_commutative i = true) : Commutative R  (@Bin.value _ _ (e_bin i) ).
  Proof.
    unfold is_commutative in H.
    destruct (Bin.comm (e_bin i)); auto.
    discriminate.
  Qed.

  Instance Binvalue_Associative i :Associative R (@Bin.value _ _ (e_bin i) ).
  Proof.
    destruct ((e_bin i)); auto.
  Qed.
 
  Instance Binvalue_Proper i : Proper (R ==> R ==> R) (@Bin.value _ _ (e_bin i) ).
  Proof.
    destruct ((e_bin i)); auto.
  Qed.
  Hint Resolve Binvalue_Proper Binvalue_Associative Binvalue_Commutative.

  (** auxiliary lemmas about sums  *)

  Hint Resolve is_unit_of_Unit.
  Section sum_correctness.
    Variable i : idx.
    Variable is_unit : idx -> bool.
    Hypothesis is_unit_sum_Unit : forall j, is_unit j = true->  @Unit X R (Bin.value (e_bin i)) (eval (unit j)).

    Inductive is_sum_spec_ind : T ->  @discr (mset T) -> Prop :=
    | is_sum_spec_op : forall j l, j = i -> is_sum_spec_ind (sum j l) (Is_op l)
    | is_sum_spec_unit : forall j, is_unit j = true ->  is_sum_spec_ind (unit j) (Is_unit j)
    | is_sum_spec_nothing : forall u, is_sum_spec_ind  u (Is_nothing).
 
    Lemma is_sum_spec u : is_sum_spec_ind u (is_sum i is_unit u).
    Proof.
      unfold is_sum; case u; intros; try constructor.
      case_eq (eq_idx_bool p i); intros; subst;  try constructor; auto.
      revert H. case eq_idx_spec; try discriminate. auto.
      case_eq (is_unit p); intros; try constructor. auto.
    Qed.

    Instance assoc :   @Associative X R (Bin.value (e_bin i)).
    Proof.
      destruct (e_bin i). simpl. assumption.
    Qed.
    Instance proper :   Proper (R ==> R ==> R)(Bin.value (e_bin i)).
    Proof.
      destruct (e_bin i). simpl. assumption.
    Qed.
    Hypothesis comm : @Commutative X R (Bin.value (e_bin i)).

    Lemma sum'_sum : forall  (l: mset T),  eval (sum' i l) ==eval (sum i l) .
    Proof.
      intros [[a n] | [a n] l]; destruct n;  simpl; reflexivity.
    Qed.

    Lemma eval_sum_nil x:
      eval (sum i (nil (x,xH))) == (eval x).
    Proof. rewrite <- sum'_sum. reflexivity.   Qed.
     
    Lemma eval_sum_cons : forall n a (l: mset T),
      (eval (sum i ((a,n)::l))) == (@Bin.value _ _ (e_bin i) (@copy _ (@Bin.value _ _ (e_bin i)) n (eval a)) (eval (sum i l))).
    Proof.
      intros n a [[? ? ]|[b m] l]; simpl; reflexivity.
    Qed.
   
    Inductive compat_sum_unit : @m idx (mset T) -> Prop :=
    | csu_left : forall x,  is_unit x = true->  compat_sum_unit  (left x)
    | csu_right : forall m, compat_sum_unit (right m)
    .

    Lemma compat_sum_unit_return x n : compat_sum_unit  (return_sum i is_unit x n).
    Proof.
      unfold return_sum.
      case is_sum_spec; intros; try constructor; auto.
    Qed.
   
    Lemma compat_sum_unit_add : forall x n h,
      compat_sum_unit  h
      ->
     compat_sum_unit
     (add_to_sum i (is_unit_of i) x n
       h).
    Proof.
      unfold add_to_sum;intros; inversion H;
        case_eq  (is_sum i (is_unit_of i) x);
        intros; simpl; try constructor || eauto. apply H0.
    Qed.

    (* Hint Resolve copy_plus. : this lags because of  the inference of the implicit arguments *)
    Hint Extern 5 (copy (?n + ?m) (eval ?a) == Bin.value (copy ?n (eval ?a)) (copy ?m (eval ?a))) => apply copy_plus.
    Hint Extern 5 (?x == ?x) => reflexivity.
    Hint Extern 5 ( Bin.value ?x ?y == Bin.value ?y ?x) => apply Bin.comm.
   
    Lemma eval_merge_bin : forall (h k: mset T),
      eval (sum i (merge_msets compare h k)) == @Bin.value _ _ (e_bin i) (eval (sum i h)) (eval (sum i k)).
    Proof.
      induction h as [[a n]|[a n] h IHh]; intro k.
      simpl.
      induction k as [[b m]|[b m] k IHk]; simpl.
      destruct (tcompare_weak_spec a b) as [a|a b|a b]; simpl; auto. apply copy_plus; auto.
     
      destruct (tcompare_weak_spec a b) as [a|a b|a b]; simpl; auto.
      rewrite copy_plus,law_assoc; auto. 
      rewrite IHk;  clear IHk. rewrite 2 law_assoc. apply proper. apply law_comm. reflexivity.
     
      induction k as [[b m]|[b m] k IHk]; simpl;  simpl in IHh.
      destruct (tcompare_weak_spec a b) as [a|a b|a b]; simpl.
      rewrite  (law_comm _ (copy m (eval a))), law_assoc, <- copy_plus,  Pplus_comm; auto. 
      rewrite <- law_assoc, IHh.  reflexivity.
      rewrite law_comm. reflexivity.
     
      simpl in IHk.
      destruct (tcompare_weak_spec a b) as [a|a b|a b]; simpl.
      rewrite IHh; clear IHh. rewrite 2 law_assoc. rewrite (law_comm _ (copy m (eval a))). rewrite law_assoc, <- copy_plus,  Pplus_comm; auto. 
      rewrite IHh; clear IHh. simpl.  rewrite law_assoc. reflexivity. 
      rewrite 2 (law_comm  (copy m (eval b))). rewrite law_assoc.  apply proper; [ | reflexivity]. 
      rewrite <- IHk. reflexivity.
    Qed.

 
    Lemma copy_mset' n (l: mset T):  copy_mset n l = nelist_map (fun vm => let '(v,m):=vm in (v,Pmult n m)) l.
    Proof.
      unfold copy_mset.  destruct n; try reflexivity.
     
      simpl. induction l as [|[a l] IHl]; simpl; try congruence.  destruct a.  reflexivity.
    Qed.
   
   
    Lemma copy_mset_succ  n (l: mset T):  eval (sum i (copy_mset (Psucc n) l)) == @Bin.value _ _ (e_bin i) (eval (sum i l)) (eval (sum i (copy_mset n l))).
    Proof.
      rewrite 2 copy_mset'.
     
      induction l as [[a m]|[a m] l IHl].
      simpl eval.   rewrite <- copy_plus; auto. rewrite Pmult_Sn_m. reflexivity.
     
      simpl nelist_map.  rewrite ! eval_sum_cons. rewrite IHl.  clear IHl.
      rewrite Pmult_Sn_m. rewrite copy_plus; auto. rewrite <- !law_assoc.
      apply Binvalue_Proper; try reflexivity.
      rewrite law_comm . rewrite <- !law_assoc. apply proper; try reflexivity.
      apply law_comm.
    Qed.

    Lemma copy_mset_copy : forall n  (m : mset T), eval (sum i (copy_mset n m)) == @copy _ (@Bin.value _ _ (e_bin i)) n (eval (sum i m)).
    Proof.
      induction n using Pind; intros.
     
      unfold copy_mset. rewrite copy_xH. reflexivity.
      rewrite copy_mset_succ. rewrite copy_Psucc. rewrite IHn. reflexivity.
    Qed.
   
    Instance compat_sum_unit_Unit : forall p, compat_sum_unit (left p) ->
      @Unit X R (Bin.value (e_bin i)) (eval (unit p)).
    Proof.
      intros.
      inversion H. subst.  auto.
    Qed.
  
    Lemma copy_n_unit : forall j n, is_unit j = true ->
      eval (unit j) == @copy _ (Bin.value (e_bin i)) n (eval (unit j)).
    Proof.
      intros.
      induction n using Prect.
      rewrite copy_xH. reflexivity.
      rewrite copy_Psucc. rewrite <- IHn. apply is_unit_sum_Unit in H. rewrite law_neutral_left. reflexivity.
    Qed.

   
    Lemma z0  l r (H : compat_sum_unit  r):
      eval (sum i (run_msets (comp (merge_msets compare) l r))) == eval (sum i ((merge_msets compare) (l) (run_msets r))).
    Proof.
      unfold comp. unfold run_msets.
      case_eq r; intros; subst.
      rewrite eval_merge_bin; auto.
      rewrite eval_sum_nil.
      apply compat_sum_unit_Unit in H. rewrite law_neutral_right.  reflexivity.
      reflexivity.
    Qed.

    Lemma z1 : forall n x,
      eval (sum i (run_msets (return_sum i (is_unit) x n )))
      == @copy _ (@Bin.value _ _ (e_bin i)) n (eval x).
    Proof.
      intros. unfold return_sum.  unfold run_msets.
      case (is_sum_spec); intros; subst.
      rewrite copy_mset_copy.
      reflexivity.
     
      rewrite eval_sum_nil. apply copy_n_unit. auto.
      reflexivity.
    Qed.
    Lemma z2 : forall  u n x, compat_sum_unit  x ->
      eval (sum i ( run_msets
        (add_to_sum i (is_unit) u n x)))
      == 
      @Bin.value _ _ (e_bin i) (@copy _ (@Bin.value _ _ (e_bin i))  n (eval u)) (eval (sum i (run_msets x))).
    Proof.
      intros u n x Hix .
      unfold add_to_sum.
      case is_sum_spec; intros; subst.
   
      rewrite z0 by auto.  rewrite eval_merge_bin.  rewrite copy_mset_copy. reflexivity.
      rewrite <- copy_n_unit by assumption.
      apply is_unit_sum_Unit in H.
      rewrite law_neutral_left. reflexivity.
     
     
      rewrite z0 by auto.  rewrite eval_merge_bin. reflexivity.
    Qed.
  End sum_correctness.
  Lemma eval_norm_msets i norm
    (Comm : Commutative R (Bin.value (e_bin i)))
    (Hnorm: forall u, eval (norm u) == eval u) : forall h, eval (sum i (norm_msets norm i h)) == eval (sum i h).
  Proof.
    unfold norm_msets.
    assert (H :
      forall h : mset T,
        eval (sum i (run_msets (norm_msets_ i (is_unit_of i) norm h))) ==  eval (sum i h) /\ compat_sum_unit (is_unit_of i) (norm_msets_ i (is_unit_of i) norm h)).
      
    induction h as [[a n] | [a n] h [IHh IHh']]; simpl norm_msets_; split.
    rewrite z1 by auto. rewrite Hnorm . reflexivity. auto.
    apply compat_sum_unit_return.
      
    rewrite z2 by auto. rewrite IHh. 
    rewrite eval_sum_cons.  rewrite Hnorm. reflexivity. apply compat_sum_unit_add, IHh'.
   
    apply H.
  Defined.
 
  (** auxiliary lemmas about products  *)

  Section prd_correctness.
    Variable i : idx.
    Variable is_unit : idx -> bool.
    Hypothesis is_unit_prd_Unit : forall j, is_unit j = true->  @Unit X R (Bin.value (e_bin i)) (eval (unit j)).

    Inductive is_prd_spec_ind  : T ->  @discr (nelist T) -> Prop :=
    | is_prd_spec_op :
      forall j l, j = i -> is_prd_spec_ind (prd j l) (Is_op l)
    | is_prd_spec_unit :
      forall j, is_unit j = true ->  is_prd_spec_ind (unit j) (Is_unit j)
    | is_prd_spec_nothing :
      forall u, is_prd_spec_ind u (Is_nothing).
   
    Lemma is_prd_spec u : is_prd_spec_ind u (is_prd i is_unit u).
    Proof.
      unfold is_prd; case u; intros; try constructor.
      case (eq_idx_spec); intros; subst;  try constructor; auto.
      case_eq (is_unit p); intros; try constructor; auto.  
    Qed.

    Lemma prd'_prd : forall (l: nelist T), eval (prd' i l) == eval (prd i l).
    Proof.
      intros  [?|? [|? ?]]; simpl; reflexivity.
    Qed.
   
   
    Lemma eval_prd_nil x:  eval (prd i (nil x)) == eval x. 
    Proof.
      rewrite <- prd'_prd. simpl. reflexivity.
    Qed.
    Lemma eval_prd_cons a : forall (l: nelist T), eval (prd i (a::l)) == @Bin.value _ _ (e_bin i) (eval a) (eval (prd i l)).
    Proof.
      intros  [|b l]; simpl; reflexivity.
    Qed.       
    Lemma eval_prd_app : forall (h k: nelist T), eval (prd i (h++k)) == @Bin.value _ _ (e_bin i) (eval (prd i h)) (eval (prd i k)).
    Proof.
      induction h; intro k. simpl; try reflexivity.
      simpl appne.  rewrite  2 eval_prd_cons, IHh, law_assoc. reflexivity.
    Qed.       

    Inductive compat_prd_unit : @m idx (nelist T) -> Prop :=
    | cpu_left : forall x,  is_unit  x = true -> compat_prd_unit  (left x)
    | cpu_right : forall m, compat_prd_unit (right m)
    .
 
    Lemma compat_prd_unit_return  x: compat_prd_unit (return_prd i is_unit x).
    Proof.
      unfold return_prd.
      case (is_prd_spec); intros; try constructor; auto.
    Qed.

    Lemma compat_prd_unit_add  : forall x  h,
      compat_prd_unit  h
      ->
      compat_prd_unit
      (add_to_prd i is_unit x
        h).
    Proof.
      intros.
      unfold add_to_prd.
      unfold comp.
      case (is_prd_spec); intros; try constructor; auto.
      unfold comp; case h; try constructor.
      unfold comp; case h; try constructor.
    Qed.

   
    Instance compat_prd_Unit : forall p, compat_prd_unit (left p) ->
      @Unit X R (Bin.value (e_bin i)) (eval (unit p)).
    Proof.
      intros.
      inversion H; subst. apply is_unit_prd_Unit. assumption.
    Qed.

    Lemma z0' : forall l (r: @m idx (nelist T)), compat_prd_unit r ->
      eval (prd i (run_list (comp (@appne T) l r))) == eval (prd i ((appne (l) (run_list r)))).
    Proof.
      intros.
      unfold comp. unfold run_list. case_eq r; intros; auto; subst.
      rewrite eval_prd_app.
      rewrite eval_prd_nil.
      apply compat_prd_Unit in H. rewrite law_neutral_right. reflexivity.
      reflexivity.
    Qed.
 
    Lemma z1' a :  eval (prd i (run_list (return_prd i is_unit a))) ==  eval (prd i (nil a)).
    Proof.
      intros. unfold return_prd.  unfold run_list.
      case (is_prd_spec); intros; subst; reflexivity.
    Qed.
    Lemma z2' : forall  u  x, compat_prd_unit  x -> 
      eval (prd i ( run_list
        (add_to_prd i is_unit u x))) ==  @Bin.value _ _ (e_bin i) (eval u) (eval (prd i (run_list x))).
    Proof.
      intros u x Hix.
      unfold add_to_prd.
      case (is_prd_spec); intros; subst.
      rewrite z0' by auto.  rewrite eval_prd_app.  reflexivity.
      apply is_unit_prd_Unit in H. rewrite law_neutral_left. reflexivity.
      rewrite z0' by auto.  rewrite eval_prd_app. reflexivity.
    Qed.
 
  End prd_correctness.




  Lemma eval_norm_lists i (Hnorm: forall u, eval (norm u) == eval u) : forall h, eval (prd i (norm_lists norm i h)) == eval (prd i h).
  Proof.
    unfold norm_lists.
    assert (H :  forall h : nelist T,
      eval (prd i (run_list (norm_lists_ i (is_unit_of i) norm h))) ==
      eval (prd i h)
      /\ compat_prd_unit (is_unit_of i) (norm_lists_ i (is_unit_of i) norm h)).
  
   
      induction h as [a | a h [IHh IHh']]; simpl norm_lists_; split.
      rewrite z1'. simpl.  apply Hnorm.
   
      apply compat_prd_unit_return.
   
      rewrite z2'. rewrite IHh.  rewrite eval_prd_cons.  rewrite Hnorm. reflexivity. apply is_unit_of_Unit.
      auto.

      apply compat_prd_unit_add. auto.
      apply H.
    Defined.

  (** correctness of the normalisation function *)

  Theorem eval_norm: forall u, eval (norm u) == eval u
    with eval_norm_aux: forall i (l: vT i) (f: Sym.type_of i),
      Proper (@Sym.rel_of X R i) f -> eval_aux (vnorm l) f == eval_aux l f.
  Proof.
    induction u as [ p m | p l | ? | ?];  simpl norm.
    case_eq (is_commutative p); intros.
    rewrite sum'_sum.
    apply eval_norm_msets; auto.
    reflexivity.

    rewrite prd'_prd.
    apply eval_norm_lists; auto.

    apply eval_norm_aux, Sym.morph.

    reflexivity.

    induction l; simpl; intros f Hf. reflexivity.
    rewrite eval_norm. apply IHl, Hf; reflexivity.
  Qed.


  (** corollaries, for goal normalisation or decision *)

  Lemma normalise : forall (u v: T), eval (norm u) == eval (norm v) -> eval u == eval v.
  Proof. intros u v. rewrite 2 eval_norm. trivial. Qed.
   
  Lemma compare_reflect_eq: forall u v, compare u v = Eq -> eval u == eval v.
  Proof. intros u v. case (tcompare_weak_spec u v); intros; try congruence. reflexivity. Qed.

  Lemma decide: forall (u v: T), compare (norm u) (norm v) = Eq -> eval u == eval v.
  Proof. intros u v H. apply normalise. apply compare_reflect_eq. apply H. Qed.

  Lemma lift_normalise {S} {H : AAC_lift S R}:
    forall (u v: T), (let x := norm u in let y := norm v in
      S (eval x) (eval y)) -> S (eval u) (eval v).
  Proof. destruct H. intros u v; simpl; rewrite 2 eval_norm. trivial. Qed.

End s.
End Internal.


(** * Lemmas for performing transitivity steps
   given an instance of AAC_lift *)

Section t.
  Context `{AAC_lift}.

  Lemma lift_transitivity_left  (y x z : X): E x y -> R y z -> R x z.
  Proof. destruct H as [Hequiv Hproper]; intros G;rewrite G. trivial. Qed.
 
  Lemma lift_transitivity_right (y x z : X): E y z -> R x y -> R x z.
  Proof.  destruct H as [Hequiv Hproper]; intros G. rewrite G. trivial. Qed.

  Lemma lift_reflexivity {HR :Reflexive R}: forall x y, E x y -> R x y.
  Proof. destruct H. intros ? ? G. rewrite G. reflexivity. Qed.

End t.
       
Declare ML Module "aac_tactics".
