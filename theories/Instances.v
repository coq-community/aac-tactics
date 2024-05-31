(* *********************************************************************** *)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(* *********************************************************************** *)

(** * Instances for AAC Tactics *)

From Coq Require PeanoNat ZArith Zminmax NArith List Permutation.
From Coq Require QArith Qminmax Relations.
From AAC_tactics Require Export AAC.

(** This one is not declared as an instance; this would interfere badly with setoid_rewrite *)
Lemma eq_subr {X} {R} `{@Reflexive X R} : subrelation eq R.
Proof. intros x y ->. reflexivity. Qed.

Module Peano.
  Import PeanoNat.

  (** ** Peano instances *)

  #[export] Instance aac_Nat_add_Assoc : Associative eq Nat.add := Nat.add_assoc.
  #[export] Instance aac_Nat_add_Comm : Commutative eq Nat.add := Nat.add_comm.

  #[export] Instance aac_Nat_mul_Comm : Commutative eq Nat.mul := Nat.mul_comm.
  #[export] Instance aac_Nat_mul_Assoc : Associative eq Nat.mul := Nat.mul_assoc.

  #[export] Instance aac_Nat_min_Comm : Commutative eq Nat.min := Nat.min_comm.
  #[export] Instance aac_Nat_min_Assoc : Associative eq Nat.min := Nat.min_assoc.
  #[export] Instance aac_Nat_min_Idem : Idempotent eq Nat.min := Nat.min_idempotent.

  #[export] Instance aac_Nat_max_Comm : Commutative eq Nat.max := Nat.max_comm.
  #[export] Instance aac_Nat_max_Assoc : Associative eq Nat.max := Nat.max_assoc.
  #[export] Instance aac_Nat_max_Idem : Idempotent eq Nat.max := Nat.max_idempotent.

  #[export] Instance aac_Nat_gcd_Comm : Commutative eq Nat.gcd := Nat.gcd_comm.
  #[export] Instance aac_Nat_gcd_Assoc : Associative eq Nat.gcd := Nat.gcd_assoc.
  #[export] Instance aac_Nat_gcd_Idem : Idempotent eq Nat.gcd := Nat.gcd_diag.

  #[export] Instance aac_Nat_lcm_Comm : Commutative eq Nat.lcm := Nat.lcm_comm.
  #[export] Instance aac_Nat_lcm_Assoc : Associative eq Nat.lcm := Nat.lcm_assoc.
  #[export] Instance aac_Nat_lcm_Idem : Idempotent eq Nat.lcm := Nat.lcm_diag.

  #[export] Instance aac_Nat_mul_1_Unit : Unit eq Nat.mul 1 :=
    Build_Unit eq Nat.mul 1 Nat.mul_1_l Nat.mul_1_r.
  #[export] Instance aac_Nat_lcm_1_Unit : Unit eq Nat.lcm 1 :=
    Build_Unit eq Nat.lcm 1 Nat.lcm_1_l Nat.lcm_1_r.
  #[export] Instance aac_Nat_add_0_Unit : Unit eq Nat.add 0 :=
    Build_Unit eq Nat.add (0) Nat.add_0_l Nat.add_0_r.
  #[export] Instance aac_Nat_max_0_Unit : Unit eq Nat.max 0 :=
    Build_Unit eq Nat.max 0 Nat.max_0_l Nat.max_0_r.
  #[export] Instance aac_Nat_gcd_0_Unit : Unit eq Nat.gcd 0 :=
    Build_Unit eq Nat.gcd 0 Nat.gcd_0_l Nat.gcd_0_r.

  (** We also provide liftings from  [Nat.le] to [eq] *)
  #[export] Instance Nat_le_PreOrder : PreOrder Nat.le :=
    Build_PreOrder _ Nat.le_refl Nat.le_trans.
  #[export] Instance aac_Nat_le_eq_lift : AAC_lift Nat.le eq :=
    Build_AAC_lift eq_equivalence _.
End Peano.

Module Z.
  Import ZArith Zminmax.
  Open Scope Z_scope.

  (** ** Z instances *)

  #[export] Instance aac_Z_add_Assoc : Associative eq Z.add := Z.add_assoc.
  #[export] Instance aac_Z_add_Comm : Commutative eq Z.add := Z.add_comm.
 
  #[export] Instance aac_Z_mul_Comm : Commutative eq Z.mul := Z.mul_comm.
  #[export] Instance aac_Z_mul_Assoc : Associative eq Z.mul := Z.mul_assoc.
 
  #[export] Instance aac_Z_min_Comm : Commutative eq Z.min := Z.min_comm.
  #[export] Instance aac_Z_min_Assoc : Associative eq Z.min := Z.min_assoc.
  #[export] Instance aac_Z_min_Idem : Idempotent eq Z.min := Z.min_idempotent.

  #[export] Instance aac_Z_max_Comm : Commutative eq Z.max := Z.max_comm.
  #[export] Instance aac_Z_max_Assoc : Associative eq Z.max := Z.max_assoc.
  #[export] Instance aac_Z_max_Idem : Idempotent eq Z.max := Z.max_idempotent.

  #[export] Instance aac_Z_gcd_Comm : Commutative eq Z.gcd := Z.gcd_comm.
  #[export] Instance aac_Z_gcd_Assoc : Associative eq Z.gcd := Z.gcd_assoc.

  #[export] Instance aac_Z_lcm_Comm : Commutative eq Z.lcm := Z.lcm_comm.
  #[export] Instance aac_Z_lcm_Assoc : Associative eq Z.lcm := Z.lcm_assoc.
  
  #[export] Instance aac_Z_mul_1_Unit : Unit eq Z.mul 1 :=
    Build_Unit eq Z.mul 1 Z.mul_1_l Z.mul_1_r.
  #[export] Instance aac_Z_add_0_Unit : Unit eq Z.add 0 :=
    Build_Unit eq Z.add 0 Z.add_0_l Z.add_0_r.

  (** We also provide liftings from [Z.le] to [eq] *)
  #[export] Instance Z_le_PreOrder : PreOrder Z.le :=
    Build_PreOrder _ Z.le_refl Z.le_trans.
  #[export] Instance aac_Z_le_eq_lift : AAC_lift Z.le eq :=
    Build_AAC_lift eq_equivalence _.
End Z.

Module Lists.
  Import List Permutation.

  (** ** List instances *)

  #[export] Instance aac_List_app_Assoc {A} : Associative eq (@app A) :=
    @app_assoc A.
  #[export] Instance aac_List_app_nil_Unit  {A} : Unit eq (@app A) (@nil A) :=
    Build_Unit _ (@app A) (@nil A) (@app_nil_l A) (@app_nil_r A).
  (** Exported [Morphisms] module provides a [Proper] instance *)

  #[export] Instance aac_List_app_Permutation_Assoc {A} :
    Associative (@Permutation A) (@app A).
  Proof. repeat intro; rewrite app_assoc; apply Permutation_refl. Qed.
  #[export] Instance aac_List_app_Permutation_Comm {A} :
    Commutative (@Permutation A) (@app A) := @Permutation_app_comm A.
  #[export] Instance aac_List_app_nil_Permutation_Unit {A} :
    Unit (@Permutation A) (@app A) (@nil A) :=
    Build_Unit (@Permutation A) (@app A) (@nil A) (fun x => Permutation_refl x)
     (fun x => eq_ind_r (fun l => Permutation l _) (Permutation_refl x) (app_nil_r x)).
  (** [Permutation_app'] in the Stdlib provides a [Proper] instance *)
End Lists.

Module N.
  Import NArith.
  Open Scope N_scope.

  (** ** N instances *)

  #[export] Instance aac_N_add_Assoc : Associative eq N.add := N.add_assoc.
  #[export] Instance aac_N_add_Comm : Commutative eq N.add := N.add_comm.

  #[export] Instance aac_N_mul_Comm : Commutative eq N.mul := N.mul_comm.
  #[export] Instance aac_N_mul_Assoc : Associative eq N.mul := N.mul_assoc.

  #[export] Instance aac_N_min_Comm : Commutative eq N.min := N.min_comm.
  #[export] Instance aac_N_min_Assoc : Associative eq N.min := N.min_assoc.
  #[export] Instance aac_N_min_Idem : Idempotent eq N.min := N.min_idempotent.

  #[export] Instance aac_N_max_Comm : Commutative eq N.max := N.max_comm.
  #[export] Instance aac_N_max_Assoc : Associative eq N.max := N.max_assoc.
  #[export] Instance aac_N_max_Idem : Idempotent eq N.max := N.max_idempotent.
  
  #[export] Instance aac_N_gcd_Comm : Commutative eq N.gcd := N.gcd_comm.
  #[export] Instance aac_N_gcd_Assoc : Associative eq N.gcd := N.gcd_assoc.
  #[export] Instance aac_N_gcd_Idem : Idempotent eq N.gcd := N.gcd_diag.

  #[export] Instance aac_N_lcm_Comm : Commutative eq N.lcm := N.lcm_comm.
  #[export] Instance aac_N_lcm_Assoc : Associative eq N.lcm := N.lcm_assoc.
  #[export] Instance aac_N_lcm_Idem : Idempotent eq N.lcm := N.lcm_diag.

  #[export] Instance aac_N_mul_1_Unit : Unit eq N.mul (1)%N :=
    Build_Unit eq N.mul 1 N.mul_1_l N.mul_1_r.
  #[export] Instance aac_N_lcm_1_Unit : Unit eq N.lcm (1)%N :=
    Build_Unit eq N.lcm 1 N.lcm_1_l N.lcm_1_r.
  #[export] Instance aac_N_add_0_Unit : Unit eq N.add (0)%N :=
    Build_Unit eq N.add 0 N.add_0_l N.add_0_r.
  #[export] Instance aac_N_max_0_Unit : Unit eq N.max 0 :=
    Build_Unit eq N.max 0 N.max_0_l N.max_0_r.
  #[export] Instance aac_N_gcd_0_Unit : Unit eq N.gcd 0 :=
    Build_Unit eq N.gcd 0 N.gcd_0_l N.gcd_0_r.

  (* We also provide liftings from [N.le] to [eq] *)
  #[export] Instance N_le_PreOrder : PreOrder N.le :=
    Build_PreOrder N.le N.le_refl N.le_trans.
  #[export] Instance aac_N_le_eq_lift : AAC_lift N.le eq :=
    Build_AAC_lift eq_equivalence _.
End N.

Module P.
  Import NArith.
  Open Scope positive_scope.

  (** ** Positive instances *)

  #[export] Instance aac_Pos_add_Assoc : Associative eq Pos.add := Pos.add_assoc.
  #[export] Instance aac_Pos_add_Comm : Commutative eq Pos.add := Pos.add_comm.

  #[export] Instance aac_Pos_mul_Comm : Commutative eq Pos.mul := Pos.mul_comm.
  #[export] Instance aac_Pos_mul_Assoc : Associative eq Pos.mul := Pos.mul_assoc.

  #[export] Instance aac_Pos_min_Comm : Commutative eq Pos.min := Pos.min_comm.
  #[export] Instance aac_Pos_min_Assoc : Associative eq Pos.min := Pos.min_assoc.
  #[export] Instance aac_Pos_min_Idem : Idempotent eq Pos.min := Pos.min_idempotent.

  #[export] Instance aac_Pos_max_Comm : Commutative eq Pos.max := Pos.max_comm.
  #[export] Instance aac_Pos_max_Assoc : Associative eq Pos.max := Pos.max_assoc.
  #[export] Instance aac_Pos_max_Idem : Idempotent eq Pos.max := Pos.max_idempotent.

  #[export] Instance aac_Pos_mul_1_Unit : Unit eq Pos.mul 1 :=
    Build_Unit eq Pos.mul 1 Pos.mul_1_l Pos.mul_1_r.
  #[export] Instance aac_Pos_max_1_Unit : Unit eq Pos.max 1 :=
    Build_Unit eq Pos.max 1 Pos.max_1_l Pos.max_1_r.

  (** We also provide liftings from [Pos.le] to [eq] *)
  #[export] Instance Pos_le_PreOrder : PreOrder Pos.le :=
    Build_PreOrder Pos.le Pos.le_refl Pos.le_trans.
  #[export] Instance aac_Pos_le_eq_lift : AAC_lift Pos.le eq :=
    Build_AAC_lift eq_equivalence _.
End P.

Module Q.
  Import QArith Qminmax.

  (** ** Q instances *)

  #[export] Instance aac_Q_Qplus_Qeq_Assoc : Associative Qeq Qplus := Qplus_assoc.
  #[export] Instance aac_Q_Qplus_Qeq_Comm : Commutative Qeq Qplus := Qplus_comm.

  #[export] Instance aac_Q_Qmult_Qeq_Comm : Commutative Qeq Qmult := Qmult_comm.
  #[export] Instance aac_Q_Qmult_Qeq_Assoc : Associative Qeq Qmult := Qmult_assoc.

  #[export] Instance aac_Q_Qmin_Qeq_Comm : Commutative Qeq Qmin := Q.min_comm.
  #[export] Instance aac_Q_Qmin_Qeq_Assoc : Associative Qeq Qmin := Q.min_assoc.
  #[export] Instance aac_Q_Qmin_Qeq_Idem : Idempotent Qeq Qmin := Q.min_idempotent.

  #[export] Instance aac_Q_Qmax_Qeq_Comm : Commutative Qeq Qmax := Q.max_comm.
  #[export] Instance aac_Q_Qmax_Qeq_Assoc : Associative Qeq Qmax := Q.max_assoc.
  #[export] Instance aac_Q_Qmax_Qeq_Idem : Idempotent Qeq Qmax := Q.max_idempotent.

  #[export] Instance aac_Q_Qmult_1_Qeq_Unit : Unit Qeq Qmult 1 :=
    Build_Unit Qeq Qmult 1 Qmult_1_l Qmult_1_r.
  #[export] Instance aac_Q_Qplus_0_Qeq_Unit : Unit Qeq Qplus 0 :=
    Build_Unit Qeq Qplus 0 Qplus_0_l Qplus_0_r.

  (** we also provide liftings from le to eq *)
  #[export] Instance Q_Qle_PreOrder : PreOrder Qle :=
    Build_PreOrder Qle Qle_refl Qle_trans.
  #[export] Instance aac_Q_Qle_eq_lift : AAC_lift Qle Qeq :=
    Build_AAC_lift QOrderedType.QOrder.TO.eq_equiv _.
End Q.

Module Prop_ops.
  (** ** Prop instances *)

  #[export] Instance aac_Prop_or_iff_Assoc : Associative iff or.
  Proof. unfold Associative; tauto. Qed.
  #[export] Instance aac_Prop_or_iff_Comm : Commutative iff or.
  Proof. unfold Commutative; tauto. Qed.
  #[export] Instance aac_Prop_or_iff_Idem : Idempotent iff or.
  Proof. unfold Idempotent; tauto. Qed.

  #[export] Instance aac_Prop_and_iff_Assoc : Associative iff and.
  Proof. unfold Associative; tauto. Qed.
  #[export] Instance aac_Prop_and_iff_Comm : Commutative iff and.
  Proof. unfold Commutative; tauto. Qed.
  #[export] Instance aac_Prop_and_iff_Idem : Idempotent iff and.
  Proof. unfold Idempotent; tauto. Qed.

  #[export] Instance aac_Prop_or_False_iff_Unit : Unit iff or False.
  Proof. constructor; firstorder. Qed.
  #[export] Instance aac_Prop_and_True_iff_Unit : Unit iff and True.
  Proof. constructor; firstorder. Qed.
 
  #[export] Program Instance not_iff_compat : Proper (iff ==> iff) not.
  Next Obligation. unfold iff; split; intros; tauto. Qed.

  Solve All Obligations with firstorder.
  #[export] Instance aac_Prop_impl_iff_lift : AAC_lift Basics.impl iff :=
    Build_AAC_lift _  _.
End Prop_ops.

Module Bool.

  (** ** Boolean instances *)

  #[export] Instance aac_Bool_orb_Assoc : Associative eq orb.
  Proof. unfold Associative; firstorder with bool. Qed.
  #[export] Instance aac_Bool_orb_Comm : Commutative eq orb.
  Proof. unfold Commutative; firstorder with bool. Qed.
  #[export] Instance aac_Bool_orb_Idem : Idempotent eq orb.
  Proof. intro; apply Bool.orb_diag. Qed.

  #[export] Instance aac_Bool_andb_Assoc : Associative eq andb.
  Proof. unfold Associative; firstorder with bool. Qed.
  #[export] Instance aac_Bool_andb_Comm : Commutative eq andb.
  Proof. unfold Commutative; firstorder with bool. Qed.
  #[export] Instance aac_Bool_andb_Idem : Idempotent eq andb.
  Proof. intro; apply Bool.andb_diag. Qed.

  #[export] Instance aac_Bool_orb_false_Unit : Unit eq orb false.
  Proof. constructor; firstorder with bool. Qed.
  #[export] Instance aac_Bool_andb_true_Unit : Unit eq andb true.
  Proof. constructor; intros [|]; firstorder. Qed.

  #[export] Instance negb_compat : Proper (eq ==> eq) negb.
  Proof. intros [|] [|]; auto. Qed.
End Bool.

Module Relations.
  Import Relations.Relations.

  (** ** Relation instances *)

  Section defs.
    Variable T : Type.
    Variables R S: relation T.
    Definition inter : relation T := fun x y => R x y /\ S x y.
    Definition compo : relation T := fun x y => exists z : T, R x z /\ S z y.
    Definition negr : relation T := fun x y => ~ R x y.
    (** union and converse are already defined in the standard library *)
    Definition bot : relation T := fun _ _ => False.
    Definition top : relation T := fun _ _ => True.
  End defs.
 
  #[export] Instance same_relation_Equivalence T :
    Equivalence (same_relation T).
  Proof. firstorder. Qed.
 
  #[export] Instance aac_union_same_relation_Comm T :
    Commutative (same_relation T) (union T).
  Proof. unfold Commutative; compute; intuition. Qed.
  #[export] Instance aac_union_same_relation_Assoc T :
    Associative (same_relation T) (union T).
  Proof. unfold Associative; compute; intuition. Qed.
  #[export] Instance aac_union_same_relation_Idem T :
    Idempotent (same_relation T) (union T).
  Proof. unfold Idempotent; compute; intuition. Qed.
  #[export] Instance aac_bot_union_same_relation_Unit T :
    Unit (same_relation T) (union T) (bot T).
  Proof. constructor; compute; intuition. Qed.

  #[export] Instance aac_inter_same_relation_Comm T :
    Commutative (same_relation T) (inter T).
  Proof. unfold Commutative; compute; intuition. Qed.
  #[export] Instance aac_inter_same_relation_Assoc T :
    Associative (same_relation T) (inter T).
  Proof. unfold Associative; compute; intuition. Qed.
  #[export] Instance aac_inter_same_relation_Idem T :
    Idempotent (same_relation T) (inter T).
  Proof. unfold Idempotent; compute; intuition. Qed.
  #[export] Instance aac_inter_top_same_relation_Unit T :
    Unit (same_relation T) (inter T) (top T).
  Proof. constructor; compute; intuition. Qed.
 
  (** Note that we use [eq] directly as a neutral element for composition *)
  #[export] Instance aac_compo_same_relation_Assoc T :
    Associative (same_relation T) (compo T).
  Proof. unfold Associative; compute; firstorder. Qed.
  #[export] Instance aac_compo_eq_same_relation_Unit T :
    Unit (same_relation T) (compo T) (eq).
  Proof. compute; firstorder subst; trivial. Qed.

  #[export] Instance negr_same_relation_compat T :
   Proper (same_relation T ==> same_relation T) (negr T).
  Proof. compute. firstorder. Qed.

  #[export] Instance transp_same_relation_compat T :
   Proper (same_relation T ==> same_relation T) (transp T).
  Proof. compute. firstorder. Qed.

  #[export] Instance clos_trans_incr T :
   Proper (inclusion T ==> inclusion T) (clos_trans T).
  Proof.
    intros R S H x y Hxy. induction Hxy.
    constructor 1. apply H. assumption.
    econstructor 2; eauto 3.
  Qed.

  #[export] Instance clos_trans_same_relation_compat T :
   Proper (same_relation T ==> same_relation T) (clos_trans T).
  Proof. intros R S H; split; apply clos_trans_incr, H. Qed.

  #[export] Instance clos_refl_trans_incr T :
    Proper (inclusion T ==> inclusion T) (clos_refl_trans T).
  Proof.
    intros R S H x y Hxy. induction Hxy.
    constructor 1. apply H. assumption.
    constructor 2.
    econstructor 3; eauto 3.
  Qed.

  #[export] Instance clos_refl_trans_same_relation_compat T :
    Proper (same_relation T ==> same_relation T) (clos_refl_trans T).
  Proof. intros R S H; split; apply clos_refl_trans_incr, H. Qed.

  #[export] Instance inclusion_PreOrder T : PreOrder (inclusion T).
  Proof. constructor; unfold Reflexive, Transitive, inclusion; intuition. Qed.

  #[export] Program Instance aac_inclusion_same_relation_lift T :
   AAC_lift (inclusion T) (same_relation T) :=
    Build_AAC_lift (same_relation_Equivalence T) _.
  Next Obligation. firstorder. Qed.
End Relations.

Module All.
  Export Peano.
  Export Z.
  Export Lists.
  Export P.
  Export N.
  Export Prop_ops.
  Export Bool.
  Export Relations.
End All.

(**
  Here, we should not see any instance of our classes:
  Print HintDb typeclass_instances.
*)
