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

val init_constant_constr : string list -> string -> Constr.t
val init_constant : string list -> string -> EConstr.constr

(** {2 General purpose functions} *)

type goal_sigma =  Goal.goal Evd.sigma
val resolve_one_typeclass : Goal.goal Evd.sigma -> EConstr.types -> EConstr.constr * goal_sigma
val cps_resolve_one_typeclass: ?error:Pp.t -> EConstr.types -> (EConstr.constr  -> Proofview.V82.tac) -> Proofview.V82.tac
val nf_evar : goal_sigma -> EConstr.constr -> EConstr.constr
val evar_unit :goal_sigma ->EConstr.constr ->  EConstr.constr* goal_sigma
val evar_binary: goal_sigma -> EConstr.constr -> EConstr.constr* goal_sigma
val evar_relation: goal_sigma -> EConstr.constr -> EConstr.constr* goal_sigma
val cps_evar_relation : EConstr.constr -> (EConstr.constr -> Proofview.V82.tac) -> Proofview.V82.tac

(** [cps_mk_letin name v] binds the constr [v] using a letin tactic  *)
val cps_mk_letin : string -> EConstr.constr -> ( EConstr.constr -> Proofview.V82.tac) -> Proofview.V82.tac

val retype : EConstr.constr -> Proofview.V82.tac

val decomp_term : Evd.evar_map -> EConstr.constr -> (EConstr.constr , EConstr.types, EConstr.ESorts.t, EConstr.EInstance.t) Constr.kind_of_term
val lapp : EConstr.constr lazy_t -> EConstr.constr array -> EConstr.constr

(** {2 Bindings with Coq' Standard Library}  *)

(** Coq lists *)
module List:
sig
  (** [of_list ty l]  *)
  val of_list:EConstr.constr ->EConstr.constr list ->EConstr.constr
   
  (** [type_of_list ty] *)
  val type_of_list:EConstr.constr ->EConstr.constr
end

(** Coq pairs *)
module Pair:
sig
  val typ:EConstr.constr lazy_t
  val pair:EConstr.constr lazy_t
  val of_pair : EConstr.constr -> EConstr.constr ->  EConstr.constr * EConstr.constr -> EConstr.constr
end

module Bool : sig
  val typ : EConstr.constr lazy_t
  val of_bool : bool -> EConstr.constr
end


module Comparison : sig
  val typ : EConstr.constr lazy_t
  val eq : EConstr.constr lazy_t
  val lt : EConstr.constr lazy_t
  val gt : EConstr.constr lazy_t
end

module Leibniz : sig
  val eq_refl : EConstr.types -> EConstr.constr -> EConstr.constr
end

module Option : sig
  val typ : EConstr.constr lazy_t
  val some : EConstr.constr -> EConstr.constr -> EConstr.constr
  val none : EConstr.constr -> EConstr.constr
  val of_option : EConstr.constr -> EConstr.constr option -> EConstr.constr
end   

(** Coq positive numbers (pos) *)
module Pos:
sig
  val typ:EConstr.constr lazy_t
  val of_int: int ->EConstr.constr
end

(** Coq unary numbers (peano) *)
module Nat:
sig
  val typ:EConstr.constr lazy_t
  val of_int: int ->EConstr.constr
end

(** Coq typeclasses *)
module Classes:
sig
  val mk_morphism: EConstr.constr -> EConstr.constr -> EConstr.constr -> EConstr.constr
  val mk_equivalence: EConstr.constr ->  EConstr.constr -> EConstr.constr
  val mk_reflexive: EConstr.constr ->  EConstr.constr -> EConstr.constr
  val mk_transitive: EConstr.constr ->  EConstr.constr -> EConstr.constr
end

module Relation : sig
  type t = {carrier : EConstr.constr; r : EConstr.constr;}
  val make : EConstr.constr -> EConstr.constr -> t
  val split : t -> EConstr.constr * EConstr.constr
end
   
module Transitive : sig
  type t =
      {
	carrier : EConstr.constr;
	leq : EConstr.constr;
	transitive : EConstr.constr;
      }
  val make : EConstr.constr -> EConstr.constr -> EConstr.constr -> t
  val infer : goal_sigma -> EConstr.constr -> EConstr.constr -> t  * goal_sigma
  val from_relation : goal_sigma -> Relation.t -> t * goal_sigma
  val cps_from_relation : Relation.t -> (t -> Proofview.V82.tac) -> Proofview.V82.tac
  val to_relation : t -> Relation.t
end
	
module Equivalence : sig
  type t =
      {
	carrier : EConstr.constr;
	eq : EConstr.constr;
	equivalence : EConstr.constr;
      } 
  val make  : EConstr.constr -> EConstr.constr -> EConstr.constr -> t
  val infer  : goal_sigma -> EConstr.constr -> EConstr.constr -> t  * goal_sigma
  val from_relation : goal_sigma -> Relation.t -> t * goal_sigma
  val cps_from_relation : Relation.t -> (t -> Proofview.V82.tac) -> Proofview.V82.tac
  val to_relation : t -> Relation.t
  val split : t -> EConstr.constr * EConstr.constr * EConstr.constr
end

(** [match_as_equation ?context goal c] try to decompose c as a
    relation applied to two terms. An optionnal rel-context can be
    provided to ensure that the term remains typable *)
val match_as_equation  : ?context:EConstr.rel_context -> goal_sigma -> EConstr.constr -> (EConstr.constr * EConstr.constr * Relation.t) option

(** {2 Some tacticials}  *)

(** time the execution of a tactic *)
val tclTIME : string -> Proofview.V82.tac -> Proofview.V82.tac

(** emit debug messages to see which tactics are failing *)
val tclDEBUG : string -> Proofview.V82.tac -> Proofview.V82.tac

(** print the current goal *)
val tclPRINT : Proofview.V82.tac -> Proofview.V82.tac


(** {2 Error related mechanisms}  *)

val anomaly : string -> 'a
val user_error : Pp.t -> 'a
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
      hyp : EConstr.constr;		  (** the actual constr corresponding to the hypothese  *)
      hyptype : EConstr.constr; 		(** the type of the hypothesis *)
      context : EConstr.rel_context;		(** the quantifications of the hypothese *)
      body : EConstr.constr; 		(** the body of the hypothese*)
      rel : Relation.t; 		(** the relation  *)
      left : EConstr.constr;		(** left hand side *)
      right : EConstr.constr;		(** right hand side  *)
      l2r : bool; 			(** rewriting from left to right  *)
    }

(** [get_hypinfo H l2r ?check_type k] analyse the hypothesis H, and
    build the related hypinfo, in CPS style. Moreover, an optionnal
    function can be provided to check the type of every free
    variable of the body of the hypothesis.  *)
val get_hypinfo :EConstr.constr -> l2r:bool -> ?check_type:(EConstr.types -> bool) ->   (hypinfo -> Proofview.V82.tac) -> Proofview.V82.tac
 
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
val build :  hypinfo ->  (int * EConstr.constr) list ->  (EConstr.constr -> Proofview.V82.tac) -> Proofview.V82.tac

(** build the constr to rewrite, in CPS style, with evars  *)
val build_with_evar :  hypinfo ->  (int * EConstr.constr) list ->  (EConstr.constr -> Proofview.V82.tac) -> Proofview.V82.tac

(** [rewrite ?abort hypinfo subst] builds the rewriting tactic
    associated with the given [subst] and [hypinfo], and feeds it to
    the given continuation. If [abort] is set to [true], we build
    [tclIDTAC] instead. *)
val rewrite : ?abort:bool -> hypinfo -> (int * EConstr.constr) list -> (Proofview.V82.tac -> Proofview.V82.tac) -> Proofview.V82.tac
end
