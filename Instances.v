(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)


Require Export AAC.

(** Instances for aac_rewrite.*)


(* This one is not declared as an instance: this interferes badly with setoid_rewrite *)
Lemma eq_subr {X} {R} `{@Reflexive X R}: subrelation eq R.
Proof. intros x y ->. reflexivity. Qed.

(* At the moment, all the instances are exported even if they are packaged into modules. Even using LocalInstances in fact*)

Module Peano.
  Require Import Arith NArith Max Min.
  Instance aac_plus_Assoc : Associative eq plus := plus_assoc.
  Instance aac_plus_Comm : Commutative eq plus :=  plus_comm.
 
  Instance aac_mult_Comm : Commutative eq mult :=  mult_comm.
  Instance aac_mult_Assoc : Associative eq mult :=  mult_assoc.
 
  Instance aac_min_Comm : Commutative eq min :=  min_comm.
  Instance aac_min_Assoc : Associative eq min :=  min_assoc.

  Instance aac_max_Comm : Commutative eq max :=  max_comm.
  Instance aac_max_Assoc : Associative eq max :=  max_assoc.
 
  Instance aac_one : Unit eq mult 1 :=  Build_Unit eq mult 1 mult_1_l mult_1_r. 
  Instance aac_zero_plus  : Unit eq plus O := Build_Unit eq plus (O) plus_0_l plus_0_r.
  Instance aac_zero_max  :  Unit eq max  O := Build_Unit eq max 0 max_0_l max_0_r. 


  (* We also provide liftings from le to eq *)
  Instance preorder_le : PreOrder le := Build_PreOrder _ _ le_refl le_trans.
  Instance lift_le_eq : AAC_lift le eq := Build_AAC_lift eq_equivalence _.

End Peano.


Module Z.
  Require Import ZArith Zminmax.
  Open Scope Z_scope.
  Instance aac_Zplus_Assoc : Associative eq Zplus :=  Zplus_assoc.
  Instance aac_Zplus_Comm : Commutative eq Zplus :=  Zplus_comm.
 
  Instance aac_Zmult_Comm : Commutative eq Zmult :=  Zmult_comm.
  Instance aac_Zmult_Assoc : Associative eq Zmult :=  Zmult_assoc.
 
  Instance aac_Zmin_Comm : Commutative eq Zmin :=  Zmin_comm.
  Instance aac_Zmin_Assoc : Associative eq Zmin :=  Zmin_assoc.

  Instance aac_Zmax_Comm : Commutative eq Zmax :=  Zmax_comm.
  Instance aac_Zmax_Assoc : Associative eq Zmax :=  Zmax_assoc.
 
  Instance aac_one : Unit eq Zmult 1 :=  Build_Unit eq Zmult 1 Zmult_1_l Zmult_1_r. 
  Instance aac_zero_Zplus  : Unit eq Zplus 0 := Build_Unit eq Zplus 0 Zplus_0_l Zplus_0_r.

  (* We also provide liftings from le to eq *)
  Instance preorder_Zle : PreOrder Zle := Build_PreOrder _ _ Zle_refl Zle_trans.
  Instance lift_le_eq : AAC_lift Zle eq := Build_AAC_lift eq_equivalence _.

End Z.

Module Lists.
   Require Import List.
   Instance aac_append_Assoc {A} : Associative eq (@app A) := @app_assoc A.
   Instance aac_nil_append  {A} : @Unit (list A) eq (@app A) (@nil A) := Build_Unit _ (@app A) (@nil A) (@app_nil_l A) (@app_nil_r A).
   Instance aac_append_Proper {A} : Proper (eq ==> eq ==> eq) (@app A).
   Proof.
     repeat intro.
     subst.
     reflexivity.
   Qed.
End Lists.


Module N.
  Require Import NArith.
  Open Scope N_scope.
  Instance aac_Nplus_Assoc : Associative eq Nplus :=  Nplus_assoc.
  Instance aac_Nplus_Comm : Commutative eq Nplus :=  Nplus_comm.
 
  Instance aac_Nmult_Comm : Commutative eq Nmult :=  Nmult_comm.
  Instance aac_Nmult_Assoc : Associative eq Nmult :=  Nmult_assoc.
 
  Instance aac_Nmin_Comm : Commutative eq Nmin :=  N.min_comm.
  Instance aac_Nmin_Assoc : Associative eq Nmin :=  N.min_assoc.

  Instance aac_Nmax_Comm : Commutative eq Nmax :=  N.max_comm.
  Instance aac_Nmax_Assoc : Associative eq Nmax :=  N.max_assoc.
 
  Instance aac_one  : Unit eq Nmult (1)%N := Build_Unit eq Nmult (1)%N Nmult_1_l Nmult_1_r. 
  Instance aac_zero  : Unit eq Nplus (0)%N := Build_Unit eq Nplus (0)%N Nplus_0_l Nplus_0_r.
  Instance aac_zero_max  :  Unit eq Nmax 0 := Build_Unit eq Nmax 0 N.max_0_l N.max_0_r. 
   
  (* We also provide liftings from le to eq *)
  Instance preorder_le : PreOrder Nle := Build_PreOrder _ Nle N.le_refl N.le_trans.
  Instance lift_le_eq : AAC_lift Nle eq := Build_AAC_lift eq_equivalence _.

End N.

Module P.
  Require Import NArith.
  Open Scope positive_scope.
  Instance aac_Pplus_Assoc : Associative eq Pplus :=  Pplus_assoc.
  Instance aac_Pplus_Comm : Commutative eq Pplus :=  Pplus_comm.
 
  Instance aac_Pmult_Comm : Commutative eq Pmult :=  Pmult_comm.
  Instance aac_Pmult_Assoc : Associative eq Pmult :=  Pmult_assoc.
 
  Instance aac_Pmin_Comm : Commutative eq Pmin :=  Pos.min_comm.
  Instance aac_Pmin_Assoc : Associative eq Pmin :=  Pos.min_assoc.

  Instance aac_Pmax_Comm : Commutative eq Pmax :=  Pos.max_comm.
  Instance aac_Pmax_Assoc : Associative eq Pmax :=  Pos.max_assoc.
 
  Instance aac_one  : Unit eq Pmult 1 := Build_Unit eq Pmult 1 _ Pmult_1_r. 
  intros; reflexivity. Qed.          (*  TODO : add this lemma in the stdlib *)
  Instance aac_one_max  :  Unit eq Pmax 1 := Build_Unit eq Pmax 1 Pos.max_1_l Pos.max_1_r. 

  (* We also provide liftings from le to eq *)
  Instance preorder_le : PreOrder Ple := Build_PreOrder _ Ple Pos.le_refl Pos.le_trans.
  Instance lift_le_eq : AAC_lift Ple eq := Build_AAC_lift eq_equivalence _.
End P.

Module Q.
  Require Import QArith Qminmax.
  Instance aac_Qplus_Assoc : Associative Qeq Qplus :=  Qplus_assoc.
  Instance aac_Qplus_Comm : Commutative Qeq Qplus :=  Qplus_comm.
 
  Instance aac_Qmult_Comm : Commutative Qeq Qmult :=  Qmult_comm.
  Instance aac_Qmult_Assoc : Associative Qeq Qmult :=  Qmult_assoc.
 
  Instance aac_Qmin_Comm : Commutative Qeq Qmin :=  Q.min_comm.
  Instance aac_Qmin_Assoc : Associative Qeq Qmin :=  Q.min_assoc.

  Instance aac_Qmax_Comm : Commutative Qeq Qmax :=  Q.max_comm.
  Instance aac_Qmax_Assoc : Associative Qeq Qmax :=  Q.max_assoc.
 
  Instance aac_one : Unit Qeq Qmult 1 :=  Build_Unit Qeq Qmult 1 Qmult_1_l Qmult_1_r. 
  Instance aac_zero_Qplus  : Unit Qeq Qplus 0 := Build_Unit Qeq Qplus 0 Qplus_0_l Qplus_0_r.

  (* We also provide liftings from le to eq *)
  Instance preorder_le : PreOrder Qle := Build_PreOrder _ Qle Qle_refl Qle_trans.
  Instance lift_le_eq : AAC_lift Qle Qeq := Build_AAC_lift QOrderedType.QOrder.TO.eq_equiv _.

End Q.

Module Prop_ops.
  Instance aac_or_Assoc : Associative iff or. Proof.  unfold Associative; tauto.  Qed.
  Instance aac_or_Comm : Commutative iff or. Proof.  unfold Commutative; tauto.  Qed.
  Instance aac_and_Assoc : Associative iff and. Proof.  unfold Associative; tauto.  Qed.
  Instance aac_and_Comm : Commutative iff and. Proof.  unfold Commutative; tauto.  Qed.
  Instance aac_True : Unit iff or False.  Proof.  constructor; firstorder.  Qed.
  Instance aac_False : Unit iff and True.  Proof.  constructor; firstorder.  Qed.
 
  Program Instance aac_not_compat : Proper (iff ==> iff) not.
  Solve All Obligations with firstorder.

  Instance lift_impl_iff : AAC_lift Basics.impl iff := Build_AAC_lift _  _.
End Prop_ops.

Module Bool.
  Instance aac_orb_Assoc : Associative eq orb. Proof.  unfold Associative; firstorder.  Qed.
  Instance aac_orb_Comm : Commutative eq orb. Proof.  unfold Commutative; firstorder.  Qed.
  Instance aac_andb_Assoc : Associative eq andb. Proof.  unfold Associative; firstorder.  Qed.
  Instance aac_andb_Comm : Commutative eq andb. Proof.  unfold Commutative; firstorder.  Qed.
  Instance aac_true : Unit eq orb false.  Proof.  constructor; firstorder.  Qed.
  Instance aac_false : Unit eq andb true.  Proof.  constructor; intros [|];firstorder.  Qed.
 
  Instance negb_compat : Proper (eq ==> eq) negb.  Proof. intros [|] [|]; auto. Qed.
End Bool.

Module Relations.
  Require Import Relations.
  Section defs.
    Variable T : Type.
    Variables R S: relation T.
    Definition inter : relation T := fun x y => R x y /\ S x y.
    Definition compo : relation T := fun x y => exists z : T, R x z /\ S z y.
    Definition negr : relation T := fun x y => ~ R x y.
    (* union and converse are already defined in the standard library *)

    Definition bot : relation T := fun _ _ => False.
    Definition top : relation T := fun _ _ => True.
  End defs.
 
  Instance eq_same_relation T : Equivalence (same_relation T). Proof. firstorder. Qed.
 
  Instance aac_union_Comm T : Commutative (same_relation T) (union T). Proof. unfold Commutative; compute; intuition.  Qed.
  Instance aac_union_Assoc T : Associative (same_relation T) (union T). Proof. unfold Associative; compute; intuition.  Qed.
  Instance aac_bot T : Unit (same_relation T) (union T) (bot T). Proof. constructor; compute; intuition. Qed.

  Instance aac_inter_Comm T : Commutative (same_relation T) (inter T). Proof. unfold Commutative; compute; intuition.  Qed.
  Instance aac_inter_Assoc T : Associative (same_relation T) (inter T). Proof. unfold Associative; compute; intuition.  Qed.
  Instance aac_top T : Unit (same_relation T) (inter T) (top T). Proof. constructor; compute; intuition. Qed.
 
  (* note that we use [eq] directly as a neutral element for composition *)
  Instance aac_compo T : Associative (same_relation T) (compo T). Proof. unfold Associative; compute; firstorder. Qed.
  Instance aac_eq T : Unit (same_relation T) (compo T) (eq). Proof.  compute; firstorder subst; trivial. Qed.

  Instance negr_compat T : Proper (same_relation T ==> same_relation T) (negr T).
  Proof. compute. firstorder. Qed.

  Instance transp_compat T : Proper (same_relation T ==> same_relation T) (transp T).
  Proof. compute. firstorder. Qed.

  Instance clos_trans_incr T : Proper (inclusion T ==> inclusion T) (clos_trans T).
  Proof.
    intros  R S H x y Hxy. induction Hxy.
      constructor 1. apply H. assumption.
      econstructor 2; eauto 3.
  Qed.
  Instance clos_trans_compat T: Proper (same_relation T ==> same_relation T) (clos_trans T).
  Proof. intros R S H; split; apply clos_trans_incr, H. Qed.

  Instance clos_refl_trans_incr T : Proper (inclusion T ==> inclusion T) (clos_refl_trans T).
  Proof.
    intros R S H x y Hxy. induction Hxy.
      constructor 1. apply H. assumption.
      constructor 2.
      econstructor 3; eauto 3.
  Qed.
  Instance clos_refl_trans_compat T : Proper (same_relation T ==> same_relation T) (clos_refl_trans T).
  Proof. intros R S H; split; apply clos_refl_trans_incr, H. Qed.

  Instance preorder_inclusion T : PreOrder (inclusion T).
  Proof. constructor; unfold Reflexive, Transitive, inclusion; intuition.   Qed.

  Instance lift_inclusion_same_relation T: AAC_lift (inclusion T) (same_relation T) :=
    Build_AAC_lift (eq_same_relation T) _.
  Proof.  firstorder. Qed.

End Relations.

Module All.
  Export Peano.
  Export Z.
  Export P.
  Export N.
  Export Prop_ops.
  Export Bool.
  Export Relations.
End All.
 
(* Here, we should not see any instance of our classes.
   Print HintDb typeclass_instances.
*)
