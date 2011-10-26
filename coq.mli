(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Interface with Coq where we define some handlers for Coq's API,
    and we import several definitions from Coq's standard library.

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
val cps_resolve_one_typeclass: ?error:string -> Term.types -> (Term.constr  -> Proof_type.tactic) -> Proof_type.tactic
val nf_evar : goal_sigma -> Term.constr -> Term.constr
val fresh_evar :goal_sigma -> Term.types ->  Term.constr* goal_sigma
val evar_unit :goal_sigma ->Term.constr ->  Term.constr* goal_sigma
val evar_binary: goal_sigma -> Term.constr -> Term.constr* goal_sigma
val evar_relation: goal_sigma -> Term.constr -> Term.constr* goal_sigma
val cps_evar_relation : Term.constr -> (Term.constr -> Proof_type.tactic) -> Proof_type.tactic
(** [cps_mk_letin name v] binds the constr [v] using a letin tactic  *)
val cps_mk_letin : string -> Term.constr -> ( Term.constr -> Proof_type.tactic) -> Proof_type.tactic


val decomp_term : Term.constr -> (Term.constr , Term.types) Term.kind_of_term
val lapp : Term.constr lazy_t -> Term.constr array -> Term.constr

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
  val of_pair : Term.constr -> Term.constr ->  Term.constr * Term.constr -> Term.constr
end

module Bool : sig
  val typ : Term.constr lazy_t
  val of_bool : bool -> Term.constr
end


module Comparison : sig
  val typ : Term.constr lazy_t
  val eq : Term.constr lazy_t
  val lt : Term.constr lazy_t
  val gt : Term.constr lazy_t
end

module Leibniz : sig
  val eq_refl : Term.types -> Term.constr -> Term.constr
end

module Option : sig
  val some : Term.constr -> Term.constr -> Term.constr
  val none : Term.constr -> Term.constr
  val of_option : Term.constr -> Term.constr option -> Term.constr
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
  val mk_reflexive: Term.constr ->  Term.constr -> Term.constr
  val mk_transitive: Term.constr ->  Term.constr -> Term.constr
end

module Relation : sig
  type t = {carrier : Term.constr; r : Term.constr;}	
  val make : Term.constr -> Term.constr -> t
  val split : t -> Term.constr * Term.constr
end
   
module Transitive : sig
  type t =
      {
	carrier : Term.constr;
	leq : Term.constr;
	transitive : Term.constr;
      }
  val make : Term.constr -> Term.constr -> Term.constr -> t
  val infer : goal_sigma -> Term.constr -> Term.constr -> t  * goal_sigma
  val from_relation : goal_sigma -> Relation.t -> t * goal_sigma
  val cps_from_relation : Relation.t -> (t -> Proof_type.tactic) -> Proof_type.tactic
  val to_relation : t -> Relation.t
end
	
module Equivalence : sig
  type t =
      {
	carrier : Term.constr;
	eq : Term.constr;
	equivalence : Term.constr;	     
      } 
  val make  : Term.constr -> Term.constr -> Term.constr -> t
  val infer  : goal_sigma -> Term.constr -> Term.constr -> t  * goal_sigma
  val from_relation : goal_sigma -> Relation.t -> t * goal_sigma
  val cps_from_relation : Relation.t -> (t -> Proof_type.tactic) -> Proof_type.tactic
  val to_relation : t -> Relation.t
  val split : t -> Term.constr * Term.constr * Term.constr
end

(** [match_as_equation ?context goal c] try to decompose c as a
    relation applied to two terms. An optionnal rel_context can be
    provided to ensure that the term remains typable *)
val match_as_equation  : ?context:Term.rel_context -> goal_sigma -> Term.constr -> (Term.constr * Term.constr * Relation.t) option

(** {2 Some tacticials}  *)

(** time the execution of a tactic *)
val tclTIME : string -> Proof_type.tactic -> Proof_type.tactic

(** emit debug messages to see which tactics are failing *)
val tclDEBUG : string -> Proof_type.tactic -> Proof_type.tactic

(** print the current goal *)
val tclPRINT : Proof_type.tactic -> Proof_type.tactic


(** {2 Error related mechanisms}  *)

val anomaly : string -> 'a
val user_error : string -> 'a
val warning : string -> unit


(** {2 Rewriting tactics used in aac_rewrite}  *)

module Rewrite : sig

(** The rewriting tactics used in aac_rewrite, build as handlers of the usual [setoid_rewrite]*)


(** {2 Datatypes}  *)

(** We keep some informations about the hypothesis, with an (informal)
    invariant:
    - [typeof hyp = typ]
    - [typ = forall context, body]
    - [body = rel left right]
 
*)
type hypinfo =
    {
      hyp : Term.constr;		  (** the actual constr corresponding to the hypothese  *)
      hyptype : Term.constr; 		(** the type of the hypothesis *)
      context : Term.rel_context; 	(** the quantifications of the hypothese *)
      body : Term.constr; 		(** the body of the hypothese*)
      rel : Relation.t; 		(** the relation  *)
      left : Term.constr;		(** left hand side *)
      right : Term.constr;		(** right hand side  *)
      l2r : bool; 			(** rewriting from left to right  *)
    }

(** [get_hypinfo H l2r ?check_type k] analyse the hypothesis H, and
    build the related hypinfo, in CPS style. Moreover, an optionnal
    function can be provided to check the type of every free
    variable of the body of the hypothesis.  *)
val get_hypinfo :Term.constr -> l2r:bool -> ?check_type:(Term.types -> bool) ->   (hypinfo -> Proof_type.tactic) -> Proof_type.tactic
 
(** {2 Rewriting with bindings}

    The problem : Given a term to rewrite of type [H :forall xn ... x1,
    t], we have to instanciate the subset of [xi] of type
    [carrier]. [subst : (int * constr)] is the mapping the De Bruijn
    indices in [t] to the [constrs]. We need to handle the rest of the
    indexes. Two ways :

    - either using fresh evars and rewriting [H tn ?1 tn-2 ?2 ]
    - either building a term like [fun 1 2 => H tn 1 tn-2 2]

    Both these terms have the same type.
*)

(** build the constr to rewrite, in CPS style, with lambda abstractions  *)
val build :  hypinfo ->  (int * Term.constr) list ->  (Term.constr -> Proof_type.tactic) -> Proof_type.tactic

(** build the constr to rewrite, in CPS style, with evars  *)
val build_with_evar :  hypinfo ->  (int * Term.constr) list ->  (Term.constr -> Proof_type.tactic) -> Proof_type.tactic

(** [rewrite ?abort hypinfo subst] builds the rewriting tactic
    associated with the given [subst] and [hypinfo], and feeds it to
    the given continuation. If [abort] is set to [true], we build
    [tclIDTAC] instead. *)
val rewrite : ?abort:bool -> hypinfo -> (int * Term.constr) list -> (Proof_type.tactic -> Proof_type.tactic) -> Proof_type.tactic
end
