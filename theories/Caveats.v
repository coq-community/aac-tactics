(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** * Currently known caveats and limitations of the [aac_tactics] library.

   Depending on your installation, either uncomment the following two
   lines, or add them to your .coqrc files, replacing "."
   with the path to the [aac_tactics] library
*)

Require NArith PeanoNat.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.

(** ** Limitations *)

(** *** 1. Dependent parameters
   The type of the rewriting hypothesis must be of the form

   [forall (x_1: T_1) ... (x_n: T_n), R l r],

   where [R] is a relation over some type [T] and such that for all
   variable [x_i] appearing in the left-hand side ([l]), we actually
   have [T_i]=[T]. The goal should be of the form [S g d], where [S]
   is a relation on [T].

   In other words, we cannot instantiate arguments of an exogeneous
   type. *)

Section parameters.

  Context {X} {R} {E: @Equivalence X R}
  {plus} {plus_A: Associative R plus} {plus_C: Commutative R plus}
         {plus_Proper: Proper (R ==> R ==> R) plus}
  {zero} {Zero: Unit R plus zero}.

  Notation "x == y"  := (R x y) (at level 70).
  Notation "x + y"   := (plus x y) (at level 50, left associativity).
  Notation "0"       := (zero).

  Variable f: nat -> X -> X.

  (** in [Hf], the parameter [n] has type [nat], it cannot be instantiated automatically *)
  Hypothesis Hf: forall n x, f n x + x == x.
  Hypothesis Hf': forall n, Proper (R ==> R) (f n).

  Goal forall a b k, a + f k (b+a) + b == a+b.
    intros.
    Fail aac_rewrite Hf. (** [aac_rewrite] does not instantiate [n] automatically *)
    aac_rewrite (Hf k).         (** of course, this argument can be given explicitly *)
    aac_reflexivity.
  Qed. 

  (** for the same reason, we cannot handle higher-order parameters (here, [g])*)
  Hypothesis H : forall g x y, g x + g y == g (x + y).
  Variable g : X -> X.
  Hypothesis Hg : Proper (R ==> R) g.
  Goal forall a b c, g a + g b + g c == g (a + b + c).
    intros.
    Fail aac_rewrite H.
    do 2 aac_rewrite (H g). aac_reflexivity.
  Qed.

End parameters.


(** *** 2. Exogeneous morphisms

   We do not handle `exogeneous' morphisms: morphisms that move from
   type [T] to some other type [T']. *)

Section morphism.
  Import NArith PeanoNat.
  Open Scope nat_scope.

  (** Typically, although [N_of_nat] is a proper morphism from
     [@eq nat] to [@eq N], we cannot rewrite under [N_of_nat] *)
  Goal forall a b: nat, N_of_nat (a+b-(b+a)) = 0%N.
    intros.
    Fail aac_rewrite Nat.sub_diag.
  Abort.


  (* More generally, this prevents us from rewriting under
     propositional contexts *)
  Context {P} {HP : Proper (@eq nat ==> iff) P}.
  Hypothesis H : P 0.

  Goal forall a b, P (a + b - (b + a)).
    intros a b.
    Fail aac_rewrite Nat.sub_diag.
    (** a solution is to introduce an evar to replace the part to be
       rewritten. This tiresome process should be improved in the
       future. Here, it can be done using eapply and the morphism. *)
    eapply HP.
    aac_rewrite Nat.sub_diag.
     reflexivity.
     exact H.
  Qed.

  Goal forall a b, a+b-(b+a) = 0 /\ b-b = 0.
    intros.
    (** similarly, we need to bring equations to the toplevel before
    being able to rewrite *)
    Fail aac_rewrite Nat.sub_diag.
    split; aac_rewrite Nat.sub_diag; reflexivity.
  Qed.
   
End morphism.


(** *** 3. Treatment of variance with inequations.

   We do not take variance into account when we compute the set of
   solutions to a matching problem modulo AC. As a consequence,
   [aac_instances] may propose solutions for which [aac_rewrite] will
   fail, due to the lack of adequate morphisms *)

Section ineq. 

  Import ZArith.
  Import Instances.Z.
  Open Scope Z_scope.

  Instance Zplus_incr: Proper (Z.le ==> Z.le ==> Z.le) Zplus.
  Proof. intros ? ? H ? ? H'. apply Zplus_le_compat; assumption. Qed. 

  Hypothesis H: forall x, x+x <= x.
  Goal forall a b c, c + - (a + a) + b + b <= c.
    intros.
    (** this fails because the first solution is not valid ([Zopp] is not increasing), *)
    Fail aac_rewrite H.
    aac_instances H.       
    (** on the contrary, the second solution is valid: *) 
    aac_rewrite H at 1.
    (** Currently, we cannot filter out such invalid solutions in an easy way;
       this should be fixed in the future  *)
  Abort.

End ineq. 



(** ** Caveats  *)

(** *** 1. Special treatment for units.
   [S O] is considered as a unit for multiplication whenever a [Peano.mult]
   appears in the goal. The downside is that [S x] does not match [1],
   and [1] does not match [S(0+0)] whenever [Peano.mult] appears in
   the goal. *)

Section Peano.
  Import Instances.Peano.

  Hypothesis H : forall x, x + S x = S (x+x).

  Goal 1 = 1.
  (** ok (no multiplication around), [x] is instantiated with [O] *)
    aacu_rewrite H.
  Abort.

  Goal 1*1 = 1.
  (** fails since 1 is seen as a unit, not the application of the
     morphism [S] to the constant [O] *)
    Fail aacu_rewrite H.
  Abort.

  Hypothesis H': forall x, x+1 = 1+x.

  Goal forall a, a+S(0+0) = 1+a.
  (** ok (no multiplication around), [x] is instantiated with [a]*)
    intro. aac_rewrite H'.
  Abort.

  Goal forall a, a*a+S(0+0) = 1+a*a.
  (** fails: although [S(0+0)] is understood as the application of
     the morphism [S] to the constant [O], it is not recognised
     as the unit [S O] of multiplication *)
    intro. Fail aac_rewrite H'.
  Abort.

  (** More generally, similar counter-intuitive behaviours can appear
     when declaring an applied morphism as an unit. *)

End Peano.



(** *** 2. Existential variables.
We implemented an algorithm for _matching_ modulo AC, not for
_unifying_ modulo AC. As a consequence, existential variables
appearing in a goal are considered as constants, they will not be
instantiated. *)

Section evars.
  Import ZArith.
  Import Instances.Z.

  Variable P: Prop.
  Hypothesis H: forall x y, x+y+x = x -> P.
  Hypothesis idem: forall x, x+x = x.
  Goal P.
    eapply H.
    aac_rewrite idem. (** this works: [x] is instantiated with an evar *)
    instantiate (2 := 0).
    symmetry. aac_reflexivity. (** this does work but there are remaining evars in the end *)
  Abort.

  Hypothesis H': forall x, 3+x = x -> P.
  Goal P.
    eapply H'.
    Fail aac_rewrite idem. (** this fails since we do not instantiate evars *)
  Abort.
End evars.


(** *** 3. Distinction between [aac_rewrite] and [aacu_rewrite] *)

Section U.
  Context {X} {R} {E: @Equivalence X R}
  {dot}  {dot_A: Associative R dot} {dot_Proper: Proper (R ==> R ==> R) dot}
  {one}  {One: Unit R dot one}.

  Infix "=="   := R (at level 70).
  Infix "*"    := dot.
  Notation "1" := one.

  (** In some situations, the [aac_rewrite] tactic allows
  instantiations of a variable with a unit, when the variable occurs
  directly under a function symbol: *)

  Variable f : X -> X.
  Hypothesis Hf : Proper (R ==> R) f.
  Hypothesis dot_inv_left : forall x, f x*x  == x.
  Goal f 1 == 1.
    aac_rewrite dot_inv_left. reflexivity.
  Qed.

  (** This behaviour seems desirable in most situations: these
  solutions with units are less peculiar than the other ones, since
  the unit comes from the goal. However, this policy is not properly
  enforced for now (hard to do with the current algorithm): *)

  Hypothesis dot_inv_right : forall x, x*f x  == x.
  Goal f 1 == 1.
    Fail aac_rewrite dot_inv_right.
    aacu_rewrite dot_inv_right. reflexivity.
  Qed.

End U.

(** *** 4. Rewriting units *)
Section V.
  Context {X} {R} {E: @Equivalence X R}
  {dot}  {dot_A: Associative R dot} {dot_Proper: Proper (R ==> R ==> R) dot}
  {one}  {One: Unit R dot one}.

  Infix "=="   := R (at level 70).
  Infix "*"    := dot.
  Notation "1" := one.
 
  (** [aac_rewrite] uses the symbols appearing in the goal and the
     hypothesis to infer the AC and A operations. In the following
     example, [dot] appears neither in the left-hand-side of the goal,
     nor in the right-hand side of the hypothesis. Hence, 1 is not
     recognised as a unit. To circumvent this problem, we can force
     [aac_rewrite] to take into account a given operation, by giving
     it an extra argument. This extra argument seems useful only in
     this peculiar case. *)

  Lemma inv_unique: forall x y y', x*y == 1 -> y'*x == 1 -> y==y'.
  Proof.
    intros x y y' Hxy Hy'x.
    aac_instances <- Hy'x [dot].
    aac_rewrite <- Hy'x at 1 [dot].
    aac_rewrite Hxy. aac_reflexivity.
  Qed.
End V.

(** *** 5. Rewriting too much things.  *)
Section W.
  Variables a b c: nat.
  Hypothesis H: 0 = c.

  Goal  b*(a+a) <= b*(c+a+a+1).
   
  (** [aac_rewrite] finds a pattern modulo AC that matches a given
     hypothesis, and then makes a call to [setoid_rewrite]. This
     [setoid_rewrite] can unfortunately make several rewrites (in a
     non-intuitive way: below, the [1] in the right-hand side is
     rewritten into [S c]) *)
    aac_rewrite H.

    (** To this end, we provide a companion tactic to [aac_rewrite]
    and [aacu_rewrite], that makes the transitivity step, but not the
    setoid_rewrite:
   
    This allows the user to select the relevant occurrences in which
    to rewrite. *)
    aac_pattern H at 2. setoid_rewrite H at 1.
  Abort.

End W.

(** *** 6. Rewriting nullifiable patterns.  *)
Section Z.

(** If the pattern of the rewritten hypothesis does not contain "hard"
symbols (like constants, function symbols, AC or A symbols without
units), there can be infinitely many subterms such that the pattern
matches: it is possible to build "subterms" modulo ACU that make the
size of the term increase (by making neutral elements appear in a
layered fashion). Hence, we settled with heuristics to propose only
"some" of these solutions. In such cases, the tactic displays a
(conservative) warning.  *)

Variables a b c: nat.
Variable f: nat -> nat.
Hypothesis H0: forall x, 0 = x - x.
Hypothesis H1: forall x, 1 = x * x.

Goal a+b*c = c.
  aac_instances H0.
  (** In this case, only three solutions are proposed, while there are
  infinitely many solutions. E.g.
     - a+b*c*(1+[])
     - a+b*c*(1+0*(1+ []))
     - ...
     *)
Abort.

(** **** If the pattern is a unit or can be instantiated to be equal
   to a unit:
  
   The heuristic is to make the unit appear at each possible position
   in the term, e.g. transforming [a] into [1*a] and [a*1], but this
   process is not recursive (we will not transform [1*a]) into
   [(1+0*1)*a] *)

Goal a+b+c = c.
 
  aac_instances H0 [mult].            
  (** 1 solution, we miss solutions like [(a+b+c*(1+0*(1+[])))] and so on  *)
 
  aac_instances H1 [mult].     
  (** 7 solutions, we miss solutions like [(a+b+c+0*(1+0*[]))]*)
Abort.

(** *** Another example of the former case is the following, where the hypothesis can be instantiated to be equal to [1] *)
Hypothesis H : forall x y, (x+y)*x = x*x + y *x.
Goal a*a+b*a + c = c.
  (** Here, only one solution if we use the aac_instance tactic  *)
  aac_instances <- H.

  (** There are 8 solutions using aacu_instances (but, here,
     there are infinitely many different solutions). We miss e.g. [a*a +b*a
     + (x*x + y*x)*c], which seems to be more peculiar. *)
  aacu_instances <- H.

  (** The 7 last solutions are the same as if we were matching [1] *)
  aacu_instances H1.  Abort.

(** The behavior of the tactic is not satisfying in this case. It is
still unclear how to handle properly this kind of situation : we plan
to investigate on this in the future *)

End Z.

