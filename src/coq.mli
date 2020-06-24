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
type lazy_ref = Names.GlobRef.t Lazy.t

val get_fresh : lazy_ref -> Constr.constr
val get_efresh : lazy_ref -> EConstr.constr
  
val find_global : string -> lazy_ref


(** {2 General purpose functions} *)

type goal_sigma =  Goal.goal Evd.sigma
val resolve_one_typeclass : Goal.goal Evd.sigma -> EConstr.types -> EConstr.constr * goal_sigma
val cps_resolve_one_typeclass: ?error:Pp.t -> EConstr.types -> (EConstr.constr  -> Proofview.V82.tac) -> Proofview.V82.tac
val nf_evar : goal_sigma -> EConstr.constr -> EConstr.constr
val evar_binary: Environ.env -> Evd.evar_map -> EConstr.constr -> Evd.evar_map * EConstr.constr
val evar_relation: Environ.env -> Evd.evar_map -> EConstr.constr -> Evd.evar_map * EConstr.constr

(** [cps_mk_letin name v] binds the constr [v] using a letin tactic  *)
val cps_mk_letin : string -> EConstr.constr -> ( EConstr.constr -> Proofview.V82.tac) -> Proofview.V82.tac
val mk_letin : string -> EConstr.constr -> EConstr.constr Proofview.tactic

val retype : EConstr.constr -> Proofview.V82.tac
val tclRETYPE : EConstr.constr -> unit Proofview.tactic

val decomp_term : Evd.evar_map -> EConstr.constr -> (EConstr.constr , EConstr.types, EConstr.ESorts.t, EConstr.EInstance.t) Constr.kind_of_term

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
  val typ: lazy_ref
  val pair: lazy_ref
  val of_pair : EConstr.constr -> EConstr.constr ->  EConstr.constr * EConstr.constr -> EConstr.constr
end


module Option : sig
  val typ : lazy_ref
  val some : EConstr.constr -> EConstr.constr -> EConstr.constr
  val none : EConstr.constr -> EConstr.constr
  val of_option : EConstr.constr -> EConstr.constr option -> EConstr.constr
end   

(** Coq positive numbers (pos) *)
module Pos:
sig
  val typ:lazy_ref
  val of_int: int ->EConstr.constr
end

(** Coq unary numbers (peano) *)
module Nat:
sig
  val typ:lazy_ref
  val of_int: int -> Constr.constr
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
  val to_relation : t -> Relation.t
  val split : t -> EConstr.constr * EConstr.constr * EConstr.constr
end

(** [match_as_equation ?context env sigma c] try to decompose c as a
    relation applied to two terms.  *)
val match_as_equation  : ?context:EConstr.rel_context -> Environ.env -> Evd.evar_map -> EConstr.constr -> (EConstr.constr * EConstr.constr * Relation.t) option

(** {2 Some tacticials}  *)

(** time the execution of a tactic *)
val tclTIME : string -> Proofview.V82.tac -> Proofview.V82.tac

(** emit debug messages to see which tactics are failing *)
val tclDEBUG : string -> unit Proofview.tactic

(** print the current goal *)
val tclPRINT : unit Proofview.tactic

(** {2 Error related mechanisms}  *)

val anomaly : string -> 'a
val user_error : Pp.t -> 'a
val warning : string -> unit

(** {2 Helpers}  *)

(** print the current proof term *)
val show_proof : Declare.Proof.t -> unit

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

(** [get_hypinfo H ?check_type l2r] analyse the hypothesis H, and
    build the related hypinfo. Moreover, an optionnal
    function can be provided to check the type of every free
    variable of the body of the hypothesis.  *)
val get_hypinfo : Environ.env -> Evd.evar_map ->  EConstr.constr -> ?check_type:(EConstr.types -> bool) -> l2r:bool -> hypinfo
 
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

(** build the constr to rewrite, with lambda abstractions  *)
val build :  hypinfo ->  (int * EConstr.constr) list ->  EConstr.constr

(** build the constr to rewrite, in CPS style, with evars  *)
(* val build_with_evar :  hypinfo ->  (int * EConstr.constr) list ->  (EConstr.constr -> Proofview.V82.tac) -> Proofview.V82.tac *)

(** [rewrite ?abort hypinfo subst] builds the rewriting tactic
    associated with the given [subst] and [hypinfo]. 
If [abort] is set to [true], we build
    [tclIDTAC] instead. *)
val rewrite : ?abort:bool -> hypinfo -> (int * EConstr.constr) list -> unit Proofview.tactic
end
