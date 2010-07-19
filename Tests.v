(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

Require Import AAC.

Section sanity.  

  Context {X} {R} {E: Equivalence R} {plus} {zero}
  {dot} {one} {A: @Op_A X R dot one} {AC: Op_AC R plus zero}.
 

  Notation "x == y"  := (R x y) (at level 70).
  Notation "x * y"   := (dot x y) (at level 40, left associativity).
  Notation "1"       := (one).
  Notation "x + y"   := (plus x y) (at level 50, left associativity).
  Notation "0"       := (zero).

  Section t0.
  Hypothesis H : forall x, x+x == x.
  Goal forall a b, a+b +a == a+b.
    intros a b; aacu_rewrite H; aac_reflexivity.
  Qed.
  End t0.
  
  Section t1.
    Variables a b : X.
    
    Variable P : X -> Prop.
    Hypothesis H : forall x y, P y -> x+y+x == x.
    Hypothesis Hb : P b.
    Goal  a+b +a == a.
      aacu_rewrite H.
      aac_reflexivity.
      auto.
    Qed.
  End t1.

  Section t.
  Variable f : X -> X.
  Hypothesis Hf : Proper (R ==> R) f.
  Hypothesis H : forall x, x+x == x.
  Goal forall y, f(y+y) == f (y).
    intros y.
    aacu_instances H.
    aacu_rewrite H.
    aac_reflexivity.
  Qed.

  Goal forall y z, f(y+z+z+y) == f (y+z).
    intros y z.
    aacu_instances H.
    aacu_rewrite H.
    aac_reflexivity.
  Qed.

  Hypothesis H' : forall x, x*x == x.
  Goal forall y z, f(y*z*y*z) == f (y*z).
    intros y z.
    aacu_instances H'.
    aacu_rewrite H'.
    aac_reflexivity.
  Qed.
  End t.

  Goal forall x y, (plus x y) == (plus y x). intros.
    aac_reflexivity. 
  Qed.

  Goal forall x y, R (plus (dot x one) y) (plus y x). intros.
    aac_reflexivity. 
  Qed.

  Goal (forall f y, f y + f y == y) -> forall a b g (Hg: Proper (R ==> R) g), g (a+b) + g b + g (b+a) == a + b + g b.
    intros.
    try aacu_rewrite H. 
    aacu_rewrite (H g).
    Restart.
    intros.
    set (H' := H g).
    aacu_rewrite H'.
    aac_reflexivity.
  Qed.

  Section t2.
    Variables a b: X.
    Variables g : X ->X.
    Hypothesis Hg:Proper (R ==> R) g.
    Hypothesis H: (forall y, (g y) + y == y).    
    Goal  g (a+b) +  b +a+a == a + b +a.
    intros.
    aacu_rewrite H.
    aac_reflexivity.
  Qed.
  End t2.
  Section t3.
    Variables a b: X.
    Variables g : X ->X.
    Hypothesis Hg:Proper (R ==> R) g.
    Hypothesis H: (forall f y, f y + y == y).
    
    Goal  g (a+b) +  b +a+a == a + b +a.
    intros.
    aacu_rewrite (H g).
    aac_reflexivity.
  Qed.
End t3.

Section null.
  Hypothesis dot_ann : forall x, 0 * x == 0.
  Goal forall a, 0*a == 0.
    intros a. aac_rewrite dot_ann. reflexivity.
  Qed.
End null.

End sanity.

Section abs.
  Context 
    {X} {E: Equivalence (@eq X)} 
    {plus}  {zero}  {AC: @Op_AC X eq plus zero}
    {plus'} {zero'} {AC': @Op_AC X eq plus' zero'}
    {dot}   {one}   {A: @Op_A X eq dot one} 
    {dot'}  {one'}  {A': @Op_A X eq dot' one'}. 
 
  Notation "x * y"   := (dot x y) (at level 40, left associativity).
  Notation "x @ y"   := (dot' x y) (at level 20, left associativity).
  Notation "1"       := (one).
  Notation "1'"      := (one').
  Notation "x + y"   := (plus x y) (at level 50, left associativity).
  Notation "x ^ y"   := (plus' x y) (at level 30, right associativity).
  Notation "0"       := (zero).
  Notation "0'"      := (zero').

  Variables a b c d e k: X.
  Variables f g: X -> X.
  Hypothesis Hf: Proper (eq ==> eq) f.
  Hypothesis Hg: Proper (eq ==> eq) g.

  Variables h: X -> X -> X.
  Hypothesis Hh: Proper (eq ==> eq ==> eq) h.

  Variables q: X -> X -> X -> X.
  Hypothesis Hq: Proper (eq ==> eq ==> eq ==> eq) q.




  Hypothesis dot_ann_left: forall x, 0*x = 0.

  Goal f (a*0*b*c*d) = k.
    aac_rewrite dot_ann_left.
    Restart.
    aac_rewrite dot_ann_left subterm 1 subst 0.
  Abort.




  Hypothesis distr_dp: forall x y z, x*(y+z) = x*y+x*z.
  Hypothesis distr_dp': forall x y z, x*y+x*z = x*(y+z).

  Hypothesis distr_pp: forall x y z, x^(y+z) = x^y+x^z.
  Hypothesis distr_pp': forall x y z, x^y+x^z = x^(y+z).

  Hypothesis distr_dd: forall x y z, x@(y*z) = x@y * x@z.
  Hypothesis distr_dd': forall x y z, x@y * x@z = x@(y*z).


  Goal a*b*(c+d+e) = k.
    aac_instances distr_dp.
    aacu_instances distr_dp.
    aac_rewrite distr_dp subterm 0 subst 4.

    aac_instances distr_dp'.
    aac_rewrite distr_dp'.
  Abort.

  Goal a@(b*c)@d@(e*e) = k.
    aacu_instances distr_dd.
    aac_instances distr_dd.
    aac_rewrite distr_dd.
  Abort.

  Goal a^(b+c)^d^(e+e) = k.
    aacu_instances distr_dd.
    aac_instances distr_dd.
    aacu_instances distr_pp.
    aac_instances distr_pp.
    aac_rewrite distr_pp subterm 9.
  Abort.


    

  Hypothesis plus_idem: forall x, x+x = x.
  Hypothesis plus_idem3: forall x, x+x+x = x.
  Hypothesis dot_idem: forall x, x*x = x.
  Hypothesis dot_idem3: forall x, x*x*x = x.

  Goal a*b*a*b = k.
    aac_instances dot_idem.
    aacu_instances dot_idem.
    aac_rewrite dot_idem.
    aac_instances distr_dp.     (* TODO: no solution -> fail ? *)
    aacu_instances distr_dp.
  Abort.

  Goal a+a+a+a = k.
    aac_instances plus_idem3.
    aac_rewrite plus_idem3.
  Abort.

  Goal a*a*a*a = k.
    aac_instances dot_idem3.
    aac_rewrite dot_idem3.
  Abort.

  Goal a*a*a*a*a*a = k.
    aac_instances dot_idem3.
    aac_rewrite dot_idem3.
  Abort.

  Goal f(a*a)*f(a*a) = k.
    aac_instances dot_idem.
    (* TODO: pas clair qu'on doive réécrire les deux petits
    sous-termes quand on nous demande de n'en réécrire qu'un... 
    d'autant plus que le comportement est nécessairement 
    imprévisible (cf. les deux exemples en dessous)
    ceci dit, je suis conscient que c'est relou à empêcher... *)
    aac_rewrite dot_idem subterm 1. 
  Abort.

  Goal f(a*a*b)*f(a*a*b) = k.
    aac_instances dot_idem.
    aac_rewrite dot_idem subterm 2. (* une seule instance réécrite *)
  Abort.

  Goal f(b*a*a)*f(b*a*a) = k.
    aac_instances dot_idem.
    aac_rewrite dot_idem subterm 2. (* deux instances réécrites *)
  Abort.

  Goal h (a*a) (a*b*c*d*e) = k.
    aac_rewrite dot_idem.       
  Abort.

  Goal h (a+a) (a+b+c+d+e) = k.
    aac_rewrite plus_idem.       
  Abort.

  Goal (a*a+a*a+b)*c = k.
    aac_rewrite plus_idem.
    Restart.
    aac_rewrite dot_idem.
  Abort.

 


  Hypothesis dot_inv: forall x, x*f x = 1.
  Hypothesis plus_inv: forall x, x+f x = 0.
  Hypothesis dot_inv': forall x, f x*x = 1.

  Goal a*f(1)*b = k.
    try aac_rewrite dot_inv.    (* TODO: à terme, j'imagine qu'on souhaite accepter ça, même en aac *)
    aacu_rewrite dot_inv.
  Abort.

  Goal f(1) = k.
    aacu_rewrite dot_inv.   
    Restart.
    aacu_rewrite dot_inv'.  
  Abort.

  Goal b*f(b) = k.
    aac_rewrite dot_inv.  
  Abort.

  Goal f(b)*b = k.
    aac_rewrite dot_inv'.
  Abort.

  Goal a*f(a*b)*a*b*c = k.
    aac_rewrite dot_inv'.
  Abort.

  Goal g (a*f(a*b)*a*b*c+d) = k.
    aac_rewrite dot_inv'.
  Abort.

  Goal g (a+f(a+b)+c+b+b) = k.
    aac_rewrite plus_inv.
  Abort.

  Goal g (a+f(0)+c) = k.
    aac_rewrite plus_inv.
  Abort.





  Goal forall R S, Equivalence R -> Equivalence S -> R a k -> S a k.
    intros R S HR HS H. 
    try (aac_rewrite H ; fail 1 "ne doit pas passer"). 
    try (aac_instances H; fail 1 "ne doit pas passer").
  Abort.

  Goal forall R S, Equivalence R -> Equivalence S -> (forall x, R (f x) k) -> S (f a) k.
    intros R S HR HS H. 
    try (aac_instances H; fail 1 "ne doit pas passer").
    try (aac_rewrite H ; fail 1 "ne doit pas passer"). 
  Abort.





  Hypothesis star_f: forall x y, x*f(y*x) = f(x*y)*x.

  Goal g (a+b*c*d*f(a*b*c*d)+b) = k.
    aac_instances star_f.
    aac_rewrite star_f.
  Abort.

  Goal b*f(a*b)*f(b*b*f(a*b)) = k.
    aac_instances star_f.
    aac_rewrite star_f.
    aac_rewrite star_f.
  Abort.





  Hypothesis dot_select: forall x y, f x * y * g x = g y*x*f y.

  Goal f(a+b)*c*g(b+a) = k.
    aac_rewrite dot_select.
  Abort. 

  Goal f(a+b)*g(b+a) = k.
    try (aac_rewrite dot_select; fail 1 "ne doit pas passer").
    aacu_rewrite dot_select.
  Abort. 

  Goal f b*f(a+b)*g(b+a)*g b = k.
    aacu_instances dot_select.
    aac_instances dot_select.
    aac_rewrite dot_select.
    aacu_rewrite dot_select.
    aacu_rewrite dot_select.
  Abort. 




  Hypothesis galois_dot: forall x y z, h x (y*z) = h (x*y) z.
  Hypothesis galois_plus: forall x y z, h x (y+z) = h (x+y) z.

  Hypothesis select_dot: forall x y, h x (y*x) = h (x*y) x.
  Hypothesis select_plus: forall x y, h x (y+x) = h (x+y) x.

  Hypothesis h_dot: forall x y, h (x*y) (y*x) = h x y.
  Hypothesis h_plus: forall x y, h (x+y) (y+x) = h x y.

End abs.

