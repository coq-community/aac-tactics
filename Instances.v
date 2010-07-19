(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Instances for aac_rewrite.*)

(* At the moment, all the instances are exported even if they are packaged into modules. *)

Require Export  AAC.

Module Peano.
  Require Import Arith NArith Max.
  Program Instance aac_plus : @Op_AC nat eq plus 0 := @Build_Op_AC nat (@eq nat) plus 0  _ plus_0_l plus_assoc plus_comm.


  Program Instance aac_mult : Op_AC eq mult 1 := Build_Op_AC _ _ _ mult_assoc mult_comm.
  (* We also declare a default associative operation: this is currently 
     required to fill reification environments *)
  Definition default_a := AC_A aac_plus. Existing Instance default_a.
End Peano.

Module Z.
  Require Import ZArith.
  Open Scope Z_scope.
  Program Instance aac_plus : Op_AC eq Zplus 0 := Build_Op_AC _ _ _ Zplus_assoc Zplus_comm.
  Program Instance aac_mult : Op_AC eq Zmult 1 := Build_Op_AC _ _ Zmult_1_l Zmult_assoc Zmult_comm.
  Definition default_a := AC_A aac_plus. Existing Instance default_a.
End Z.

Module Q.
  Require Import QArith.
  Program Instance aac_plus : Op_AC Qeq Qplus 0 := Build_Op_AC _ _ Qplus_0_l Qplus_assoc Qplus_comm.
  Program Instance aac_mult : Op_AC Qeq Qmult 1 := Build_Op_AC _ _ Qmult_1_l Qmult_assoc Qmult_comm.
  Definition default_a := AC_A aac_plus. Existing Instance default_a.
End Q.

Module Prop_ops.
  Program Instance aac_or : Op_AC iff or False.  Solve All Obligations using tauto.

  Program Instance aac_and : Op_AC iff and True. Solve All Obligations using tauto.

  Definition default_a := AC_A aac_and. Existing Instance default_a.

  Program Instance aac_not_compat : Proper (iff ==> iff) not.
  Solve All Obligations using firstorder.
End Prop_ops.

Module Bool.
  Program  Instance aac_orb : Op_AC eq orb false.
  Solve All Obligations using firstorder.

  Program  Instance aac_andb : Op_AC eq andb true.
  Solve All Obligations using firstorder.
  
  Definition default_a := AC_A aac_andb. Existing Instance default_a.

  Instance negb_compat : Proper (eq ==> eq) negb.
  Proof. intros [|] [|]; auto. Qed.
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
  
  Program Instance aac_union T : Op_AC (same_relation T) (union T) (bot T).
  Solve All Obligations using compute; [tauto || intuition].
  
  Program Instance aac_inter T : Op_AC (same_relation T) (inter T) (top T).
  Solve All Obligations using compute; firstorder.

  (* note that we use [eq] directly as a neutral element for composition *)
  Program  Instance aac_compo T : Op_A (same_relation T) (compo T) eq.
  Solve All Obligations using compute; firstorder.
  Solve All Obligations using compute; firstorder subst; trivial.

  Instance negr_compat T : Proper (same_relation T ==> same_relation T) (negr T).
  Proof. compute. firstorder. Qed.

  Instance transp_compat T : Proper (same_relation T ==> same_relation T) (transp T).
  Proof. compute. firstorder. Qed.

  Instance clos_trans_incr T : Proper (inclusion T ==> inclusion T) (clos_trans T).
  Proof. 
    intros R S H x y Hxy. induction Hxy. 
      constructor 1. apply H. assumption.
      econstructor 2; eauto 3. 
  Qed.
  Instance clos_trans_compat T : Proper (same_relation T ==> same_relation T) (clos_trans T).
  Proof. intros  R S H; split; apply clos_trans_incr, H. Qed.

  Instance clos_refl_trans_incr T : Proper (inclusion T ==> inclusion T) (clos_refl_trans T).
  Proof. 
    intros  R S H x y Hxy. induction Hxy. 
      constructor 1. apply H. assumption.
      constructor 2.
      econstructor 3; eauto 3. 
  Qed.
  Instance clos_refl_trans_compat T : Proper (same_relation T ==> same_relation T) (clos_refl_trans T).
  Proof. intros  R S H; split; apply clos_refl_trans_incr, H. Qed.
  
End Relations.

Module All.
  Export Peano.
  Export Z.
  Export Prop_ops.
  Export Bool.
  Export Relations.
End All.

(* A small test to ensure that everything can live together *)
(* Section test.
  Import All.
  Require Import ZArith.
  Open Scope Z_scope.
  Notation "x ^2" := (x*x) (at level 40).
  Hypothesis H : forall x y, x^2 + y^2 + x*y + x* y = (x+y)^2.  
  Goal forall a b c, a*1*(a ^2)*a + c + (b+0)*1*b + a^2*b + a*b*a = (a^2+b)^2+c.
    intros. 
    aac_rewrite H.
    aac_rewrite <- H .
    symmetry.
    aac_rewrite <- H .
    aac_reflexivity.
  Qed.
  Open Scope nat_scope.
  Notation "x ^^2" := (x * x) (at level 40).
  Hypothesis H' : forall (x y : nat), x^^2 + y^^2 + x*y + x* y = (x+y)^^2.  
  
  Goal forall (a b c : nat), a*1*(a ^^2)*a + c + (b+0)*1*b + a^^2*b + a*b*a = (a^^2+b)^^2+c.
    intros. aac_rewrite H'. aac_reflexivity.
  Qed.
End test. 
  
*) 
  
