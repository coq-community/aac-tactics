(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** * Examples about uses of the aac_rewrite library *)

(*
   Depending on your installation, either uncomment the following two
   lines, or add them to your .coqrc files, replacing path_to_aac_tactics
   with the correct path for your installation:

   Add Rec LoadPath "path_to_aac_tactics".
   Add ML Path "path_to_aac_tactics".
*)
Require Export  AAC.
Require Instances.

(** ** Introductory examples  *)

(** First, we settle in the context of Z, and show an usage of our
tactics: we rewrite an universally quantified hypothesis modulo
associativity and commutativity. *)

Section introduction.
  Import ZArith.
  Import Instances.Z.
  
  Variables a b c : Z.
  Hypothesis H: forall x, x + Zopp x = 0.
  Goal a + b + c + Zopp (c + a) = b.
    aac_rewrite H.
    aac_reflexivity.
  Qed.
  Goal a + c+ Zopp (b + a + Zopp b) = c.
    do 2 aac_rewrite H.
    reflexivity.
  Qed.

  (** Notes: 
     - the tactic handles arbitrary function symbols like [Zopp] (as
       long as they are proper morphisms);
     - here, ring would have done the job.
     *)

End introduction.  

(** Second, we show how to exploit binomial identities to prove a goal
about pythagorean triples, without breaking a sweat. By comparison,
even if the goal and the hypothesis are both in normal form, making
the rewrites using standard tools is difficult.
*)

Section binomials.

  Import ZArith.
  Import Instances.Z.
 
  Notation "x ^2" := (x*x) (at level 40).
  Notation "2 ⋅ x" := (x+x) (at level 41).
  Lemma Hbin1: forall x y, (x+y)^2   = x^2 + y^2 +  2⋅x*y. Proof. intros; ring. Qed.
  Lemma Hbin2: forall x y, x^2 + y^2 = (x+y)^2   + -(2⋅x*y). Proof. intros; ring.  Qed.
  Lemma Hopp : forall x, x + -x = 0. Proof Zplus_opp_r.  
  
  Variables a b c : Z.
  Hypothesis H : c^2 + 2⋅(a+1)*b  = (a+1+b)^2.
  Goal a^2 + b^2 + 2⋅a + 1 = c^2.
    aacu_rewrite <- Hbin1.
    aac_rewrite Hbin2.
    aac_rewrite <- H.
    aac_rewrite Hopp.
    aac_reflexivity.
  Qed.

  (** Note: after the [aac_rewrite <- H], one could use [ring] to close the proof.*)

End binomials.

(** ** Usage *)

(** One can also work in an abstract context, with arbitrary
   associative and commutative operators.

   (Note that one can declare several operations of each kind;
   however, to be able to use this plugin, one currently needs at least
   one associative operator, and one associative-commutative
   operator.) *)

Section base.
  
  Context {X} {R} {E: Equivalence R} 
  {plus} {zero}
  {dot} {one}
  {A:  @Op_A X R dot one}        
  {AC: Op_AC R plus zero}.      
 
  Notation "x == y"  := (R x y) (at level 70).
  Notation "x * y"   := (dot x y) (at level 40, left associativity).
  Notation "1"       := (one).
  Notation "x + y"   := (plus x y) (at level 50, left associativity).
  Notation "0"       := (zero).

  (** In the very first example, [ring] would have solved the
  goal. Here, since [dot] does not necessarily distribute over [plus],
  it is not possible to rely on it. *)

  Section reminder.
    Hypothesis H : forall x, x * x == x.
    Variables a b c : X.
    
    Goal (a+b+c)*(c+a+b) == a+b+c.
      aac_rewrite H.
      aac_reflexivity.
    Qed.

    (** Note: the tactic starts by normalizing terms, so that trailing
    units are always eliminated. *)

    Goal ((a+b)+0+c)*((c+a)+b*1) == a+b+c.
      aac_rewrite H.
      aac_reflexivity.
    Qed.
  End reminder.
  
  (** We can deal with "proper" morphisms of arbitrary arity (here [f],
     or [Zopp] earlier), and rewrite under morphisms (here [g]). *)

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

  (** ** Selecting what and where to rewrite  *)

  (** There are sometimes several possible rewriting. We now show how
  to interact with the tactic to select the desired one. *)

  Section occurrence.
    Variable f : X -> X  .
    Variable a : X.
    Hypothesis Hf : Proper (R ==> R) f.
    Hypothesis H : forall x, x + x == x. 

    Goal f(a+a)+f(a+a) == f a.
      (** In case there are several possible solutions, one can print
         the different solutions using the [aac_instances] tactic (in
         proofgeneral, look at buffer *coq* ): *)
      aac_instances H.
      (** the default choice is the smallest possible context (number
      0), but one can choose the desired context; *)
      aac_rewrite H subterm 1.            
      (** now the goal is [f a + f a  == f a], there is only one solution. *)      
      aac_rewrite H.
      reflexivity.
    Qed.
  
  End occurrence.

  Section subst.
    Variables a b c d : X.
    Hypothesis H: forall x y, a*x*y*b == a*(x+y)*b.
    Hypothesis H': forall x, x + x == x.
    
    Goal a*c*d*c*d*b  == a*c*d*b.
    (** Here, there is only one possible context, but several substitutions; *)
      aac_instances H.
      (** we can select them with the proper keyword.  *)
      aac_rewrite H subst 1. 
      aac_rewrite H'.
      aac_reflexivity.
    Qed.
  End subst.
  
  (** As expected, one can use both keyword together to select the
     correct subterm and the correct substitution. *)

  Section both.
    Variables a b c d : X.
    Hypothesis H: forall x y, a*x*y*b == a*(x+y)*b.
    Hypothesis H': forall x, x + x == x.
    
    Goal a*c*d*c*d*b*b == a*(c*d+b)*b.
      aac_instances H.
      aac_rewrite H subterm 1 subst 1.
      aac_rewrite H.
      aac_rewrite H'.
      aac_reflexivity.
    Qed.
      
  End both.

  (** We now turn on explaining the distinction between [aac_rewrite]
  and [aacu_rewrite]: [aac_rewrite] rejects solutions in which
  variables are instantiated by units, the companion tactic,
  [aacu_rewrite] allows such solutions.  *)

  Section dealing_with_units.
    Variables a b c: X.
    Hypothesis H: forall x, a*x*a == x.
    Goal a*a == 1.
      (** Here, x must be instantiated with 1, hence no solutions; *)
      aac_instances H.            
      (** while we get solutions with the "aacu" tactic. *)      
      aacu_instances H.
      aacu_rewrite H.
      reflexivity.
    Qed.
      
    (** We introduced this distinction because it allows us to rule
    out dummy cases in common situations: *)

    Hypothesis H': forall x y z,  x*y + x*z == x*(y+z).
    Goal a*b*c + a*c+ a*b == a*(c+b*(1+c)).
    (** 6 solutions without units,  *)
      aac_instances H'.
    (** more than 52 with units. *)
      aacu_instances H'.
    Abort.    
    
  End dealing_with_units.  
End base.

(** ** Declaring instances *)

(** One can use one's own operations: it suffices to declare them as
   instances of our classes. (Note that these instances are already
   declared in file [Instances.v].) *)

Section Peano.
  Require Import Arith.
     
  Program  Instance nat_plus : Op_AC eq plus O.
  Solve All Obligations using firstorder.

  Program  Instance nat_dot : Op_AC eq mult 1.
  Solve All Obligations using firstorder.
  

  (** Caveat: we need at least an instance of an operator that is AC
   and one that is A for a given relation. However, one can reuse an
   AC operator as an A operator. *)

  Definition default_a := AC_A nat_dot. Existing Instance default_a.
End Peano.

(** ** Caveats  *)

Section Peano'.
  Import Instances.Peano.

  (** 1. We have a special treatment for units, thus, [S x + x] does not
    match [S 0], which is considered as a unit (one) of the mult
    operation. *)

  Section caveat_one.
    Definition double_plus_one x := 2*x + 1. 
    Hypothesis H : forall x, S x + x = double_plus_one x.
    Goal S O = double_plus_one O.
      try aac_rewrite H.         (** 0 solutions (normal since it would use 0 to instantiate x) *)
      try aacu_rewrite H.        (** 0 solutions (abnormal) *)
    Abort.
  End caveat_one.

  (** 2. We cannot at the moment have two classes with the same
  units: in the following example, [0] is understood as the unit of
  [max] rather than as the unit of [plus]. *)

  Section max.
    Program Instance aac_max  : Op_AC eq Max.max O  := Build_Op_AC _ _ _ Max.max_assoc Max.max_comm.
    Variable a : nat.
    Goal 0 +  a = a.
      try aac_reflexivity.
    Abort.
  End max.
End Peano'.

(** 3. If some computations are possible in the goal or in the
hypothesis, the inference mechanism we use will make the
conversion. However, it seems that in most cases, these conversions
can be done by hand using simpl rather than rewrite. *)

Section Z.

  (* The order of the following lines is important in order to get the right scope afterwards. *)
  Import ZArith.
  Open Scope Z_scope.
  Opaque Zmult.
  
  Hypothesis dot_ann_left :forall x, x * 0 = 0. 
  Hypothesis dot_ann_right :forall x, 0 * x = 0. 

  Goal forall a, a*0 = 0.
    intros. aacu_rewrite dot_ann_left. reflexivity.
  Qed.

  (** Here the tactic fails, since the 0*a is converted to 0, and no
  rewrite can occur (even though Zmult is opaque). *)
  Goal forall a,  0*a = 0.
    intros. try aacu_rewrite dot_ann_left.
  Abort. 

  (**  Here the tactic fails, since the 0*x is converted to 0 in the hypothesis. *)
  Goal forall a,  a*0 = 0.
    intros. try aacu_rewrite dot_ann_right.
  Abort. 
  
 
End Z.

