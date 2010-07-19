(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Interface with Coq where we import several definitions from Coq's
    standard library. 

    This general purpose library could be reused by other plugins.
    
    Some salient points:
    - we use Caml's module system to mimic Coq's one, and avoid cluttering
    the namespace;
    - we also provide several handlers for standard coq tactics, in
    order to provide a unified setting (we replace functions that
    modify the evar_map by functions that operate on the whole
    goal, and repack the modified evar_map with it).

*)

(** {2 Getting Coq terms from the environment}  *)

val init_constant : string list -> string -> Term.constr

(** {2 General purpose functions} *)

type goal_sigma =  Proof_type.goal Tacmach.sigma 
val goal_update : goal_sigma -> Evd.evar_map -> goal_sigma
val resolve_one_typeclass : Proof_type.goal Tacmach.sigma -> Term.types -> Term.constr * goal_sigma
val nf_evar : goal_sigma -> Term.constr -> Term.constr
val evar_unit :goal_sigma ->Term.constr*Term.constr->  Term.constr* goal_sigma
val evar_binary: goal_sigma -> Term.constr*Term.constr -> Term.constr* goal_sigma 


(** [mk_letin name v] binds the constr [v] using a letin tactic  *)
val mk_letin : string  ->Term.constr ->Term.constr * Proof_type.tactic 

(** [mk_letin' name v] is a drop-in replacement for [mk_letin' name v]
    that does not make a binding (useful to test whether using lets is
    efficient) *)
val mk_letin' : string  ->Term.constr ->Term.constr * Proof_type.tactic 

(* decomp_term :  constr -> (constr, types) kind_of_term *)
val decomp_term : Term.constr -> (Term.constr , Term.types) Term.kind_of_term


(** {2 Bindings with Coq' Standard Library}  *)

(** Coq lists *)
module List:
sig
  (** [of_list ty l]  *)
  val of_list:Term.constr ->Term.constr list ->Term.constr
    
  (** [type_of_list ty] *)
  val type_of_list:Term.constr ->Term.constr
end

(** Coq pairs *)
module Pair:
sig
  val typ:Term.constr lazy_t
  val pair:Term.constr lazy_t
end

(** Coq positive numbers (pos) *)
module Pos:
sig
  val typ:Term.constr lazy_t
  val of_int: int ->Term.constr
end

(** Coq unary numbers (peano) *)
module Nat:
sig
  val typ:Term.constr lazy_t
  val of_int: int ->Term.constr
end


(** Coq typeclasses *)
module Classes:
sig
  val mk_morphism: Term.constr -> Term.constr -> Term.constr -> Term.constr
  val mk_equivalence: Term.constr ->  Term.constr -> Term.constr
end 

(** Both in OCaml and Coq, we represent finite multisets using
    weighted lists ([('a*int) list]), see {!Matcher.mset}.

    [mk_mset ty l] constructs a Coq multiset from an OCaml multiset
    [l] of Coq terms of type [ty] *)

val mk_mset:Term.constr -> (Term.constr * int) list ->Term.constr

(** pairs [(x,r)] such that [r: Relation x]  *)
type reltype = Term.constr * Term.constr

(** triples [((x,r),e)] such that [e : @Equivalence x r]*)
type eqtype = reltype * Term.constr


(** {2 Some tacticials}  *)

(** time the execution of a tactic *)
val tclTIME : string -> Proof_type.tactic -> Proof_type.tactic

(** emit debug messages to see which tactics are failing *)
val tclDEBUG : string -> Proof_type.tactic -> Proof_type.tactic

(** print the current goal *)
val tclPRINT : Proof_type.tactic -> Proof_type.tactic


