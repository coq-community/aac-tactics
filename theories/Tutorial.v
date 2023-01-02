(* *********************************************************************** *)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(* *********************************************************************** *)

(** * Tutorial for using AAC Tactics *)

From Coq Require PeanoNat ZArith List Permutation Lia.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.

(** ** Introductory example 

   Here is a first example with relative numbers ([Z]): one can
   rewrite an universally quantified hypothesis modulo the
   associativity and commutativity of [Z.add]. *)

Section introduction.
  Import ZArith.
  Import Instances.Z.

  Variables a b c : Z.
  Hypothesis H: forall x, x + Z.opp x = 0.

  Goal a + b + c + Z.opp (c + a) = b.
    aac_rewrite H.
    aac_reflexivity.
  Qed.

  Goal a + c + Z.opp (b + a + Z.opp b) = c.
    do 2 aac_rewrite H.
    reflexivity.
  Qed.

  (** note:
     - the tactic handles arbitrary function symbols like [Z.opp] (as
       long as they are proper morphisms w.r.t. the considered
       equivalence relation)
     - here, the [ring] tactic would have done the job
   *)

  (** several associative/commutative operations can be used at the same time,
      here, [Z.mul] and [Z.add], which are both associative and commutative (AC)
   *)
  Goal (b + c) * (c + b) + a + Z.opp ((c + b) * (b + c)) = a.
    aac_rewrite H.
    aac_reflexivity.
  Qed.

  (** some commutative operations can be declared as idempotent, here [Z.max]
      which is taken into account by the [aac_normalise] and [aac_reflexivity] tactics;
      however, [aac_rewrite] does not match modulo idempotency
   *)
  Goal Z.max (b + c) (c + b) + a + Z.opp (c + b) = a.
    aac_normalise.
    aac_rewrite H.
    aac_reflexivity.
  Qed.

  Goal Z.max c (Z.max b c) + a + Z.opp (Z.max c b) = a.
    aac_normalise.
    aac_rewrite H.
    aac_reflexivity.
  Qed.
  
End introduction.

(** ** Usage

   One can also work in an abstract context, with arbitrary
   associative and commutative operators. (Note that one can declare
   several operations of each kind.) 
*)

Section base.
  Context {X} {R} {E: Equivalence R}
  {plus} {dot} {zero} {one}
  {dot_A:  @Associative X R dot }       
  {plus_A: @Associative X R plus }
  {plus_C: @Commutative X R plus }
  {dot_Proper :Proper (R ==> R ==> R) dot}
  {plus_Proper :Proper (R ==> R ==> R) plus}
  {Zero : Unit R plus zero}
  {One : Unit R dot one}.

  Notation "x == y"  := (R x y) (at level 70).
  Notation "x * y"   := (dot x y) (at level 40, left associativity).
  Notation "1"       := (one).
  Notation "x + y"   := (plus x y) (at level 50, left associativity).
  Notation "0"       := (zero).

  (** in the very first example, [ring] would have solved the
    goal; here, since [dot] does not necessarily distribute over [plus],
    it is not possible to rely on it *)
  Section reminder.
    Hypothesis H : forall x, x * x == x.
    Variables a b c : X.
   
    Goal (a+b+c)*(c+a+b) == a+b+c.
      aac_rewrite H.
      aac_reflexivity.
    Qed.

    (** the tactic starts by normalising terms, so that trailing units
    are always eliminated *)
    Goal ((a+b)+0+c)*((c+a)+b*1) == a+b+c.
      aac_rewrite H.
      aac_reflexivity.
    Qed.
  End reminder.
 
  (** the tactic can deal with "proper" morphisms of arbitrary arity
    (here [f] and [g], or [Z.opp] earlier): it rewrites under such
    morphisms ([g]), and, more importantly, it is able to reorder
    terms modulo AC under these morphisms ([f]) *)
  Section morphisms.
    Variable f : X -> X -> X.
    Hypothesis Hf : Proper (R ==> R ==> R) f.
    Variable g : X -> X.
    Hypothesis Hg : Proper (R ==> R) g.  
    Variable a b: X.
    Hypothesis H : forall x y, x+f (b+y) x == y+x.

    Goal g ((f (a+b) a) + a) == g (a+a).
      aac_rewrite H.
      reflexivity.
    Qed.
  End morphisms.

  (** *** Selecting what and where to rewrite 

     There are sometimes several solutions to the matching problem. We
     now show how to interact with the tactic to select the desired one.
   *)

  Section occurrence.
    Variable f : X -> X.
    Variable a : X.
    Hypothesis Hf : Proper (R ==> R) f.
    Hypothesis H : forall x, x + x == x.

    Goal f(a+a)+f(a+a) == f a.
      (* in case there are several possible solutions, one can print
        the different solutions using the [aac_instances] tactic (in
        ProofGeneral, look at the *coq* buffer): *)
      aac_instances H.
      (* the default choice is the occurrence with the smallest
        possible context (number 0), but one can choose the desired one *)
      aac_rewrite H at 1.           
      (* now the goal is [f a + f a  == f a], there is only one solution *)     
      aac_rewrite H.
      reflexivity.
    Qed.
 
  End occurrence.

  Section subst.
    Variables a b c d : X.
    Hypothesis H: forall x y, a*x*y*b == a*(x+y)*b.
    Hypothesis H': forall x, x + x == x.
   
    Goal a*c*d*c*d*b  == a*c*d*b.
      (* here, there is only one possible occurrence, but several substitutions: *)
      aac_instances H.
      (* one can select them with the proper keyword: *)
      aac_rewrite H subst 1.
      aac_rewrite H'.
      aac_reflexivity.
    Qed.
  End subst.
 
  (** As expected, one can use both keywords together to select the
     occurrence and the substitution. We also provide a keyword to
     specify that the rewrite should be done in the right-hand side of
     the equation. 
   *)

  Section both.
    Variables a b c d : X.
    Hypothesis H: forall x y, a*x*y*b == a*(x+y)*b.
    Hypothesis H': forall x, x + x == x.
   
    Goal a*c*d*c*d*b*b == a*(c*d*b)*b.
      aac_instances H.
      aac_rewrite H at 1 subst 1.
      aac_instances H.
      aac_rewrite H.
      aac_rewrite H'.
      aac_rewrite H at 0 subst 1 in_right.
      aac_reflexivity.
    Qed.
     
  End both.

  (** *** Distinction between [aac_rewrite] and [aacu_rewrite]:

    [aac_rewrite] rejects solutions in which variables are instantiated
    by units, while the companion tactic, [aacu_rewrite] allows such
    solutions.  
   *)

  Section dealing_with_units.
    Variables a b c: X.
    Hypothesis H: forall x, a*x*a == x.

    Goal a*a == 1.
      (* here, [x] must be instantiated with [1], so that the [aac_*]
        tactics give no solutions: *)
      try aac_instances H.           
      (* while we get solutions with the [aacu_*] tactics: *)     
      aacu_instances H.
      aacu_rewrite H.
      reflexivity.
    Qed.
     
    (** we introduced this distinction because it allows us to rule
      out dummy cases in common situations: *)
    Hypothesis H': forall x y z,  x*y + x*z == x*(y+z).
    Goal a*b*c + a*c + a*b == a*(c+b*(1+c)).
      (* 6 solutions without units  *)
      aac_instances H'.        
      aac_rewrite H' at 0.
      (* more than 52 with units *)
      aacu_instances H'.
    Abort.

  End dealing_with_units. 
End base.

(** *** Declaring instances

   To use one's own operations: it suffices to declare them as
   instances of our classes. (Note that the following instances are
   already declared in the Instances module.) 
 *)

Section Peano.
  Import PeanoNat.

  #[local] Instance aac_Nat_add_Assoc : Associative eq Nat.add := Nat.add_assoc.
  #[local] Instance aac_Nat_add_Comm : Commutative eq Nat.add := Nat.add_comm.

  #[local] Instance aac_Nat_mul_Comm : Commutative eq Nat.mul := Nat.mul_comm.
  #[local] Instance aac_Nat_mul_Assoc : Associative eq Nat.mul := Nat.mul_assoc.

  #[local] Instance aac_Nat_mul_1_Unit : Unit eq Nat.mul 1 :=
    Build_Unit eq Nat.mul 1 Nat.mul_1_l Nat.mul_1_r.
  #[local] Instance aac_Nat_add_0_Unit : Unit eq Nat.add 0 :=
    Build_Unit eq Nat.add (O) Nat.add_0_l Nat.add_0_r.

  (** Two (or more) operations may share the same units: in the
  following example, [0] is understood as the unit of [Nat.max] as well as
  the unit of [Nat.add]. *)

  #[local] Instance aac_Nat_max_Comm : Commutative eq Nat.max := Nat.max_comm.
  #[local] Instance aac_Nat_max_Assoc : Associative eq Nat.max := Nat.max_assoc.

  (** Commutative operations may additionally be declared as idempotent.
    This does not change the behaviour of [aac_rewrite], but this enables
    more simplifications in [aac_normalise] and [aac_reflexivity].
   *)

  #[local] Instance aac_Nat_max_Idem : Idempotent eq Nat.max := Nat.max_idempotent.

  #[local] Instance aac_Nat_max_0_Unit : Unit eq Nat.max 0 :=
    Build_Unit eq Nat.max 0 Nat.max_0_l Nat.max_0_r.

  Variable a b c : nat.

  Goal Nat.max (a + 0) 0 = a.
    aac_reflexivity.
  Qed.

  (** here, we use idempotency: *)
  Goal Nat.max (a + 0) a = a.
    aac_reflexivity.
  Qed.
   
  (** furthermore, several operators can be mixed: *)
  Hypothesis H : forall x y z, Nat.max (x + y) (x + z) = x + Nat.max y z.
 
  Goal Nat.max (a + b) (c + (a * 1)) = Nat.max c b + a.
    aac_instances H. aac_rewrite H. aac_reflexivity.
  Qed.
 
  Goal Nat.max (a + b) (c + Nat.max (a*1+0) 0) = a + Nat.max b c.
    aac_instances H. aac_rewrite H. aac_reflexivity.
  Qed.
 
  (** *** Working with inequations

     To be able to use the tactics, the goal must be a relation [R]
     applied to two arguments, and the rewritten hypothesis must end
     with a relation [Q] applied to two arguments. These relations are
     not necessarily equivalences, but they should be related
     according to the occurrence where the rewrite takes place; we
     leave this check to the underlying call to [setoid_rewrite].
   *)

  (** one can rewrite equations in the left member of inequations: *)
  Goal (forall x, x + x = x) -> a + b + b + a <= a + b.
    intro Hx.
    aac_rewrite Hx.
    reflexivity.
  Qed.

  (** or in the right member of inequations, using the [in_right] keyword: *)
  Goal (forall x, x + x = x) -> a + b  <= a + b + b + a.
    intro Hx.
    aac_rewrite Hx in_right.
    reflexivity.
  Qed.
 
  (** similarly, one can rewrite inequations in inequations: *)
  Goal (forall x, x + x <= x) -> a + b + b + a <= a + b.
    intro Hx.
    aac_rewrite Hx.
    reflexivity.
  Qed. 

  (** possibly in the right-hand side: *)
  Goal (forall x, x <= x + x) -> a + b <= a + b + b + a.
    intro Hx.
    aac_rewrite <- Hx in_right.
    reflexivity.
  Qed.

  (** [aac_reflexivity] deals with "trivial" inequations too: *)
  Goal Nat.max (a + b) (c + a) <= Nat.max (b + a) (c + 1*a).
    aac_reflexivity.
  Qed.

  (** In the last three examples, there were no equivalence relations
     involved in the goal. However, we actually had to guess the
     equivalence relation with respect to which the operators
     ([add,max,0]) were AC.  In this case, it was Leibniz equality
     [eq] so that it was automatically inferred; more generally, one
     can specify which equivalence relation to use by declaring
     instances of the [AAC_lift] type class: 
   *)

  #[local] Instance aac_le_eq_lift : AAC_lift le eq := {}.
  (** (This instance is automatically inferred because [eq] is always a
     valid candidate, here for [le].) *)

End Peano.

(** *** Normalising goals

   We also provide a tactic to normalise terms modulo AC. This
   normalisation is the one we use internally.
 *)

Section AAC_normalise.
  Import Instances.Z.
  Import ZArith.
  Open Scope Z_scope.
 
  Variable a b c d : Z.
  Goal a + (b + c*c*d) + a + 0 + d*1 = a.
    aac_normalise.
  Abort.

  Goal Z.max (a+b) (b+a) = a+b.
    aac_reflexivity.
    Show Proof.
  Abort.

End AAC_normalise.

(** ** Examples from previous website *)

Section Examples.

  Import Instances.Z.
  Import ZArith Lia.
  Open Scope Z_scope.

  (** *** Reverse triangle inequality *)

  Lemma Z_abs_triangle : forall x y, Z.abs (x + y) <= Z.abs x + Z.abs y.
  Proof Z.abs_triangle.

  Lemma Z_add_opp_diag_r : forall x, x + -x = 0.
  Proof Z.add_opp_diag_r.

  (** the following morphisms are required to perform the required rewrites: *)
  #[local] Instance Z_opp_ge_le_compat : Proper (Z.ge ==> Z.le) Z.opp.
  Proof. intros x y. lia. Qed.

  #[local] Instance Z_add_le_compat : Proper (Z.le ==> Z.le ==> Z.le) Z.add.
  Proof. intros ? ? ? ? ? ?; lia. Qed.

  Goal forall a b, Z.abs a - Z.abs b <= Z.abs (a - b).
    intros. unfold Z.sub.
    aac_instances <- (Z.sub_diag b).
    aac_rewrite <- (Z.sub_diag b) at 3.
    unfold Z.sub.
    aac_rewrite Z_abs_triangle.
    aac_rewrite Z_add_opp_diag_r.
    aac_reflexivity.
  Qed.

  (** *** Pythagorean triples *)

  Notation "x ^2" := (x*x) (at level 40).
  Notation "2 ⋅ x" := (x+x) (at level 41).

  Lemma Hbin1: forall x y, (x+y)^2   = x^2 + y^2 +  2⋅x*y.
  Proof. intros; ring. Qed.
  Lemma Hbin2: forall x y, x^2 + y^2 = (x+y)^2 + -(2⋅x*y).
  Proof. intros; ring. Qed.
  Lemma Hopp : forall x, x + -x = 0.
  Proof. apply Zplus_opp_r. Qed.
 
  Variables a b c : Z.
  Hypothesis H : c^2 + 2⋅(a+1)*b  = (a+1+b)^2.

  Goal a^2 + b^2 + 2⋅a + 1 = c^2.
    aacu_rewrite <- Hbin1.
    rewrite Hbin2.
    aac_rewrite <- H.
    aac_rewrite Hopp.
    aac_reflexivity.
  Qed.
  (** note: after the [aac_rewrite <- H], one could use [ring] to close the proof *)

End Examples.

(** ** List examples *)

Section Lists.
  Import List Permutation.
  Import Instances.Lists.

  Variables (X : Type) (l1 l2 l3 : list X).

  Goal l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
    aac_reflexivity.
  Qed.

  Goal Permutation (l1 ++ l2) (l2 ++ l1).
    aac_reflexivity.
  Qed.

  Hypothesis H : Permutation l1 l2.

  Goal Permutation (l1 ++ l3) (l3 ++ l2).
    aac_rewrite H.
    aac_reflexivity.
  Qed.
End Lists.
