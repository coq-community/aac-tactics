(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

Require List.
(* Require Arith NArith Max Min. *)
Require ZArith Zminmax.
Require QArith Qminmax.
Require Relations.

From AAC_tactics
Require Export AAC.

(** Instances for aac_rewrite.*)


(* This one is not declared as an instance: this interferes badly with setoid_rewrite *)
Lemma eq_subr {X} {R} `{@Reflexive X R}: subrelation eq R.
Proof. intros x y ->. reflexivity. Qed.

(* At the moment, all the instances are exported even if they are packaged into modules. Even using LocalInstances in fact*)

Module Peano.
  Import PeanoNat.
  #[global] Instance aac_add_Assoc : Associative eq Nat.add := Nat.add_assoc.
  #[global] Instance aac_add_Comm : Commutative eq Nat.add := Nat.add_comm.

  #[global] Instance aac_mult_Comm : Commutative eq Nat.mul := Nat.mul_comm.
  #[global] Instance aac_mult_Assoc : Associative eq Nat.mul := Nat.mul_assoc.
 
  #[global] Instance aac_min_Comm : Commutative eq Nat.min := Nat.min_comm.
  #[global] Instance aac_min_Assoc : Associative eq Nat.min := Nat.min_assoc.
  #[global] Instance aac_min_Idem : Idempotent eq Nat.min := Nat.min_idempotent.

  #[global] Instance aac_max_Comm : Commutative eq Nat.max := Nat.max_comm.
  #[global] Instance aac_max_Assoc : Associative eq Nat.max := Nat.max_assoc.
  #[global] Instance aac_max_Idem : Idempotent eq Nat.max := Nat.max_idempotent.
 
  #[global] Instance aac_one : Unit eq Nat.mul 1 := Build_Unit eq Nat.mul 1 Nat.mul_1_l Nat.mul_1_r. 
  #[global] Instance aac_zero_add : Unit eq Nat.add O := Build_Unit eq Nat.add (O) Nat.add_0_l Nat.add_0_r.
  #[global] Instance aac_zero_max : Unit eq Nat.max  O := Build_Unit eq Nat.max 0 Nat.max_0_l Nat.max_0_r. 


  (* We also provide liftings from le to eq *)
  #[global] Instance preorder_le : PreOrder le := Build_PreOrder _ Nat.le_refl Nat.le_trans.
  #[global] Instance lift_le_eq : AAC_lift le eq := Build_AAC_lift eq_equivalence _.

End Peano.


Module Z.
  Import ZArith Zminmax.
  Open Scope Z_scope.
  #[global] Instance aac_Zplus_Assoc : Associative eq Zplus :=  Zplus_assoc.
  #[global] Instance aac_Zplus_Comm : Commutative eq Zplus :=  Zplus_comm.
 
  #[global] Instance aac_Zmult_Comm : Commutative eq Zmult :=  Zmult_comm.
  #[global] Instance aac_Zmult_Assoc : Associative eq Zmult :=  Zmult_assoc.
 
  #[global] Instance aac_Zmin_Comm : Commutative eq Z.min :=  Z.min_comm.
  #[global] Instance aac_Zmin_Assoc : Associative eq Z.min :=  Z.min_assoc.
  #[global] Instance aac_Zmin_Idem : Idempotent eq Z.min :=  Z.min_idempotent.

  #[global] Instance aac_Zmax_Comm : Commutative eq Z.max :=  Z.max_comm.
  #[global] Instance aac_Zmax_Assoc : Associative eq Z.max :=  Z.max_assoc.
  #[global] Instance aac_Zmax_Idem : Idempotent eq Z.max :=  Z.max_idempotent.
 
  #[global] Instance aac_one : Unit eq Zmult 1 :=  Build_Unit eq Zmult 1 Zmult_1_l Zmult_1_r. 
  #[global] Instance aac_zero_Zplus  : Unit eq Zplus 0 := Build_Unit eq Zplus 0 Zplus_0_l Zplus_0_r.

  (* We also provide liftings from le to eq *)
  #[global] Instance preorder_Zle : PreOrder Z.le := Build_PreOrder _ Z.le_refl Z.le_trans.
  #[global] Instance lift_le_eq : AAC_lift Z.le eq := Build_AAC_lift eq_equivalence _.

End Z.

Module Lists.
   Import List.
  #[global] Instance aac_append_Assoc {A} : Associative eq (@app A) := @app_assoc A.
  #[global] Instance aac_nil_append  {A} : @Unit (list A) eq (@app A) (@nil A) := Build_Unit _ (@app A) (@nil A) (@app_nil_l A) (@app_nil_r A).
  #[global] Instance aac_append_Proper {A} : Proper (eq ==> eq ==> eq) (@app A).
   Proof.
     repeat intro.
     subst.
     reflexivity.
   Qed.
End Lists.


Module N.
  Import NArith.
  Open Scope N_scope.
  #[global] Instance aac_Nplus_Assoc : Associative eq Nplus :=  Nplus_assoc.
  #[global] Instance aac_Nplus_Comm : Commutative eq Nplus :=  Nplus_comm.
 
  #[global] Instance aac_Nmult_Comm : Commutative eq Nmult :=  Nmult_comm.
  #[global] Instance aac_Nmult_Assoc : Associative eq Nmult :=  Nmult_assoc.
 
  #[global] Instance aac_Nmin_Comm : Commutative eq N.min :=  N.min_comm.
  #[global] Instance aac_Nmin_Assoc : Associative eq N.min :=  N.min_assoc.
  #[global] Instance aac_Nmin_Idem : Idempotent eq N.min :=  N.min_idempotent.

  #[global] Instance aac_Nmax_Comm : Commutative eq N.max :=  N.max_comm.
  #[global] Instance aac_Nmax_Assoc : Associative eq N.max :=  N.max_assoc.
  #[global] Instance aac_Nmax_Idem : Idempotent eq N.max :=  N.max_idempotent.
 
  #[global] Instance aac_one  : Unit eq Nmult (1)%N := Build_Unit eq Nmult (1)%N Nmult_1_l Nmult_1_r. 
  #[global] Instance aac_zero  : Unit eq Nplus (0)%N := Build_Unit eq Nplus (0)%N Nplus_0_l Nplus_0_r.
  #[global] Instance aac_zero_max  :  Unit eq N.max 0 := Build_Unit eq N.max 0 N.max_0_l N.max_0_r. 
   
  (* We also provide liftings from le to eq *)
  #[global] Instance preorder_le : PreOrder N.le := Build_PreOrder N.le N.le_refl N.le_trans.
  #[global] Instance lift_le_eq : AAC_lift N.le eq := Build_AAC_lift eq_equivalence _.

End N.

Module P.
  Import NArith.
  Open Scope positive_scope.
  #[global] Instance aac_Pplus_Assoc : Associative eq Pplus :=  Pplus_assoc.
  #[global] Instance aac_Pplus_Comm : Commutative eq Pplus :=  Pplus_comm.
 
  #[global]
  Instance aac_Pmult_Comm : Commutative eq Pmult :=  Pmult_comm.
  #[global] Instance aac_Pmult_Assoc : Associative eq Pmult :=  Pmult_assoc.
 
  #[global] Instance aac_Pmin_Comm : Commutative eq Pos.min :=  Pos.min_comm.
  #[global] Instance aac_Pmin_Assoc : Associative eq Pos.min :=  Pos.min_assoc.
  #[global] Instance aac_Pmin_Idem : Idempotent eq Pos.min :=  Pos.min_idempotent.

  #[global] Instance aac_Pmax_Comm : Commutative eq Pos.max :=  Pos.max_comm.
  #[global] Instance aac_Pmax_Assoc : Associative eq Pos.max :=  Pos.max_assoc.
  #[global] Instance aac_Pmax_Idem : Idempotent eq Pos.max :=  Pos.max_idempotent.

  (*  TODO : add this lemma in the stdlib *)
  Lemma Pmult_1_l (x : positive) : 1 * x = x.
  Proof. reflexivity. Qed.

  #[global] Instance aac_one  : Unit eq Pmult 1 := Build_Unit eq Pmult 1 Pmult_1_l Pmult_1_r.
  #[global] Instance aac_one_max  :  Unit eq Pos.max 1 := Build_Unit eq Pos.max 1 Pos.max_1_l Pos.max_1_r. 

  (* We also provide liftings from le to eq *)
  #[global] Instance preorder_le : PreOrder Pos.le := Build_PreOrder Pos.le Pos.le_refl Pos.le_trans.
  #[global] Instance lift_le_eq : AAC_lift Pos.le eq := Build_AAC_lift eq_equivalence _.
End P.

Module Q.
  Import QArith Qminmax.
  #[global] Instance aac_Qplus_Assoc : Associative Qeq Qplus :=  Qplus_assoc.
  #[global] Instance aac_Qplus_Comm : Commutative Qeq Qplus :=  Qplus_comm.
 
  #[global] Instance aac_Qmult_Comm : Commutative Qeq Qmult :=  Qmult_comm.
  #[global] Instance aac_Qmult_Assoc : Associative Qeq Qmult :=  Qmult_assoc.
 
  #[global] Instance aac_Qmin_Comm : Commutative Qeq Qmin :=  Q.min_comm.
  #[global] Instance aac_Qmin_Assoc : Associative Qeq Qmin :=  Q.min_assoc.
  #[global] Instance aac_Qmin_Idem : Idempotent Qeq Qmin :=  Q.min_idempotent.

  #[global] Instance aac_Qmax_Comm : Commutative Qeq Qmax :=  Q.max_comm.
  #[global] Instance aac_Qmax_Assoc : Associative Qeq Qmax :=  Q.max_assoc.
  #[global] Instance aac_Qmax_Idem : Idempotent Qeq Qmax :=  Q.max_idempotent.
 
  #[global] Instance aac_one : Unit Qeq Qmult 1 :=  Build_Unit Qeq Qmult 1 Qmult_1_l Qmult_1_r. 
  #[global] Instance aac_zero_Qplus  : Unit Qeq Qplus 0 := Build_Unit Qeq Qplus 0 Qplus_0_l Qplus_0_r.

  (* We also provide liftings from le to eq *)
  #[global] Instance preorder_le : PreOrder Qle := Build_PreOrder Qle Qle_refl Qle_trans.
  #[global] Instance lift_le_eq : AAC_lift Qle Qeq := Build_AAC_lift QOrderedType.QOrder.TO.eq_equiv _.

End Q.

Module Prop_ops.
  #[global] Instance aac_or_Assoc : Associative iff or. Proof.  unfold Associative; tauto.  Qed.
  #[global] Instance aac_or_Comm : Commutative iff or. Proof.  unfold Commutative; tauto.  Qed.
  #[global] Instance aac_or_Idem : Idempotent iff or. Proof.  unfold Idempotent; tauto.  Qed.
  #[global] Instance aac_and_Idem : Idempotent iff and. Proof.  unfold Idempotent; tauto.  Qed.
  #[global] Instance aac_True : Unit iff or False.  Proof.  constructor; firstorder.  Qed.
  #[global] Instance aac_False : Unit iff and True.  Proof.  constructor; firstorder.  Qed.
 
  #[global] Program Instance aac_not_compat : Proper (iff ==> iff) not.
  Solve All Obligations with firstorder.

  #[global] Instance lift_impl_iff : AAC_lift Basics.impl iff := Build_AAC_lift _  _.
End Prop_ops.

Module Bool.
  #[global] Instance aac_orb_Assoc : Associative eq orb. Proof.  unfold Associative; firstorder with bool.  Qed.
  #[global] Instance aac_orb_Comm : Commutative eq orb. Proof.  unfold Commutative; firstorder with bool.  Qed.
  #[global] Instance aac_orb_Idem : Idempotent eq orb. Proof.  intro; apply Bool.orb_diag.  Qed.
  #[global] Instance aac_andb_Assoc : Associative eq andb. Proof.  unfold Associative; firstorder with bool.  Qed.
  #[global] Instance aac_andb_Comm : Commutative eq andb. Proof.  unfold Commutative; firstorder with bool.  Qed.
  #[global] Instance aac_andb_Idem : Idempotent eq andb. Proof.  intro; apply Bool.andb_diag.  Qed.
  #[global] Instance aac_true : Unit eq orb false.  Proof.  constructor; firstorder with bool.  Qed.
  #[global] Instance aac_false : Unit eq andb true.  Proof.  constructor; intros [|];firstorder.  Qed.
 
  #[global] Instance negb_compat : Proper (eq ==> eq) negb.  Proof. intros [|] [|]; auto. Qed.
End Bool.

Module Relations.
  Import Relations.Relations.
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
 
  #[global] Instance eq_same_relation T : Equivalence (same_relation T). Proof. firstorder. Qed.
 
  #[global]
  Instance aac_union_Comm T : Commutative (same_relation T) (union T). Proof. unfold Commutative; compute; intuition.  Qed.
  #[global] Instance aac_union_Assoc T : Associative (same_relation T) (union T). Proof. unfold Associative; compute; intuition.  Qed.
  #[global] Instance aac_union_Idem T : Idempotent (same_relation T) (union T). Proof. unfold Idempotent; compute; intuition.  Qed.
  #[global] Instance aac_bot T : Unit (same_relation T) (union T) (bot T). Proof. constructor; compute; intuition. Qed.

  #[global] Instance aac_inter_Comm T : Commutative (same_relation T) (inter T). Proof. unfold Commutative; compute; intuition.  Qed.
  #[global] Instance aac_inter_Assoc T : Associative (same_relation T) (inter T). Proof. unfold Associative; compute; intuition.  Qed.
  #[global] Instance aac_inter_Idem T : Idempotent (same_relation T) (inter T). Proof. unfold Idempotent; compute; intuition.  Qed.
  #[global] Instance aac_top T : Unit (same_relation T) (inter T) (top T). Proof. constructor; compute; intuition. Qed.
 
  (* note that we use [eq] directly as a neutral element for composition *)
  #[global] Instance aac_compo T : Associative (same_relation T) (compo T). Proof. unfold Associative; compute; firstorder. Qed.
  #[global] Instance aac_eq T : Unit (same_relation T) (compo T) (eq). Proof.  compute; firstorder subst; trivial. Qed.

  #[global] Instance negr_compat T : Proper (same_relation T ==> same_relation T) (negr T).
  Proof. compute. firstorder. Qed.

  #[global] Instance transp_compat T : Proper (same_relation T ==> same_relation T) (transp T).
  Proof. compute. firstorder. Qed.

  #[global]
  Instance clos_trans_incr T : Proper (inclusion T ==> inclusion T) (clos_trans T).
  Proof.
    intros  R S H x y Hxy. induction Hxy.
      constructor 1. apply H. assumption.
      econstructor 2; eauto 3.
  Qed.
  #[global]
  Instance clos_trans_compat T: Proper (same_relation T ==> same_relation T) (clos_trans T).
  Proof. intros R S H; split; apply clos_trans_incr, H. Qed.

  #[global]
  Instance clos_refl_trans_incr T : Proper (inclusion T ==> inclusion T) (clos_refl_trans T).
  Proof.
    intros R S H x y Hxy. induction Hxy.
      constructor 1. apply H. assumption.
      constructor 2.
      econstructor 3; eauto 3.
  Qed.
  #[global]
  Instance clos_refl_trans_compat T : Proper (same_relation T ==> same_relation T) (clos_refl_trans T).
  Proof. intros R S H; split; apply clos_refl_trans_incr, H. Qed.

  #[global]
  Instance preorder_inclusion T : PreOrder (inclusion T).
  Proof. constructor; unfold Reflexive, Transitive, inclusion; intuition.   Qed.

  #[global]
  Program Instance lift_inclusion_same_relation T: AAC_lift (inclusion T) (same_relation T) :=
    Build_AAC_lift (eq_same_relation T) _.
  Next Obligation. firstorder. Qed.

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
