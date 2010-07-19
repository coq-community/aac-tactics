(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Main module for the Coq plug-in ; provides the [aac_rewrite] and
    [aac_reflexivity] tactics.
    
    This file defines the entry point for the tactic aac_rewrite. It
    does Joe-the-plumbing, given a goal, reifies the interesting
    subterms (rewrited hypothesis, goal) into abstract syntax tree
    {!Matcher.Terms} (see {!Theory.Trans.t_of_constr}). Then, we use the
    results from the matcher to rebuild terms and make a transitivity
    step toward a term in which the hypothesis can be rewritten using
    the standard rewrite.
    
    Doing so, we generate a sub-goal which we solve using a reflexive
    decision procedure for the equality of terms modulo
    AAC. Therefore, we also need to reflect the goal into a concrete
    data-structure. See {i AAC.v} for more informations,
    especially the data-type {b T} and the {b decide} theorem.
    
*)

(** {2 Transitional functions} 
    
    We define some plumbing functions that will be removed when we
    integrate the new rewrite features of Coq 8.3
*)

(** [find_applied_equivalence goal eq]  checks that the goal is
    an applied equivalence relation, with two operands of the same
    type.

*)
val find_applied_equivalence : Proof_type.goal Tacmach.sigma -> Term.constr -> Coq.eqtype * Term.constr * Term.constr * Proof_type.goal Tacmach.sigma

(** Build a couple of [t] from an hypothesis (variable names are not
    relevant) *)
val t_of_hyp :  Proof_type.goal Tacmach.sigma ->  Coq.reltype ->  Theory.Trans.envs -> Term.types -> (Matcher.Terms.t * Matcher.Terms.t) * int

(** {2 Tactics} *)

(** the [aac_reflexivity] tactic solves equalities modulo AAC, by
    reflection: it reifies the goal to apply theorem [decide], from
    file {i AAC.v}, and then concludes using [vm_compute]
    and [reflexivity]
*)
val aac_reflexivity : Proof_type.tactic

(** [aac_rewrite] is the tactic for in-depth reqwriting modulo AAC
with some options to choose the orientation of the rewriting and a
solution (first the subterm, then the solution)*)

val aac_rewrite : Term.constr -> ?l2r:bool -> ?show:bool -> ?strict: bool -> ?occ_subterm:int -> ?occ_sol:int -> Proof_type.tactic

