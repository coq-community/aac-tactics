(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Bindings for Coq constants that are specific to the plugin;
    reification and translation functions.
   
    Note: this module is highly correlated with the definitions of {i
    AAC_rewrite.v}.

    This module interfaces with the above Coq module; it provides
    facilities to interpret a term with arbitrary operators as an
    abstract syntax tree, and to convert an AST into a Coq term
    (either using the Coq "raw" terms, as written in the starting
    goal, or using the reified Coq datatypes we define in {i
    AAC_rewrite.v}).
*)

(** Both in OCaml and Coq, we represent finite multisets using
    weighted lists ([('a*int) list]), see {!Matcher.mset}.

    [mk_mset ty l] constructs a Coq multiset from an OCaml multiset
    [l] of Coq terms of type [ty] *)

val mk_mset:EConstr.constr -> (EConstr.constr * int) list ->EConstr.constr

(** {2 Packaging modules} *)

(** Environments *)
module Sigma:
sig
  (**  [add ty n x map] adds the value [x] of type [ty] with key [n] in [map]  *)
  val add: EConstr.constr ->EConstr.constr ->EConstr.constr ->EConstr.constr ->EConstr.constr
   
  (** [empty ty] create an empty map of type [ty]  *)
  val empty: EConstr.constr ->EConstr.constr

  (** [of_list ty null l] translates an OCaml association list into a Coq one *)
  val of_list: EConstr.constr -> EConstr.constr -> (int * EConstr.constr ) list -> EConstr.constr

  (** [to_fun ty null map] converts a Coq association list into a Coq function (with default value [null]) *)
  val to_fun: EConstr.constr ->EConstr.constr ->EConstr.constr ->EConstr.constr
end


(** Dynamically typed morphisms *)
module Sym:
sig
  (** mimics the Coq record [Sym.pack] *)
  type pack = {ar: Constr.t; value: Constr.t ; morph: Constr.t}

  val typ: EConstr.constr lazy_t


  (** [mk_pack rlt (ar,value,morph)]  *)
  val mk_pack: Coq.Relation.t -> pack -> EConstr.constr
   
  (** [null] builds a dummy (identity) symbol, given an {!Coq.Relation.t} *)
  val null: Coq.Relation.t -> EConstr.constr
 
end


(** We need to export some Coq stubs out of this module. They are used
    by the main tactic, see {!Rewrite} *)
module Stubs : sig
  val lift : EConstr.constr Lazy.t
  val lift_proj_equivalence : EConstr.constr Lazy.t
  val lift_transitivity_left : EConstr.constr Lazy.t
  val lift_transitivity_right : EConstr.constr Lazy.t
  val lift_reflexivity : EConstr.constr Lazy.t
    (** The evaluation fonction, used to convert a reified coq term to a
	raw coq term *)
  val eval: EConstr.constr lazy_t
   
  (** The main lemma of our theory, that is
      [compare (norm u) (norm v) = Eq -> eval u == eval v] *)
  val decide_thm:EConstr.constr lazy_t

  val lift_normalise_thm : EConstr.constr lazy_t
end

(** {2 Building reified terms}
   
    We define a bundle of functions to build reified versions of the
    terms (those that will be given to the reflexive decision
    procedure). In particular, each field takes as first argument the
    index of the symbol rather than the symbol itself. *)
 
(** Tranlations between Coq and OCaml  *)
module Trans :  sig

  (** This module provides facilities to interpret a term with
      arbitrary operators as an instance of an abstract syntax tree
      {!Matcher.Terms.t}.

      For each Coq application [f x_1 ... x_n], this amounts to
      deciding whether one of the partial applications [f x_1
      ... x_i], [i<=n] is a proper morphism, whether the partial
      application with [i=n-2] yields an A or AC binary operator, and
      whether the whole term is the unit for some A or AC operator. We
      use typeclass resolution to test each of these possibilities.

      Note that there are ambiguous terms:
      - a term like [f x y] might yield a unary morphism ([f x]) and a
      binary one ([f]); we select the latter one (unless [f] is A or
      AC, in which case we declare it accordingly);
      - a term like [S O] can be considered as a morphism ([S])
      applied to a unit for [(+)], or as a unit for [( * )]; we
      chose to give priority to units, so that the latter
      interpretation is selected in this case; 
      - an element might be the unit for several operations
  *)
 
  (** To achieve this reification, one need to record informations
      about the collected operators (symbols, binary operators,
      units). We use the following imperative internal data-structure to
      this end. *)
 
  type envs
  val empty_envs : unit -> envs
   

  (** {2 Reification: from Coq terms to AST {!Matcher.Terms.t}  } *)


  (** [t_of_constr goal rlt envs (left,right)] builds the abstract
      syntax tree of the terms [left] and [right]. We rely on the [goal]
      to perform typeclasses resolutions to find morphisms compatible
      with the relation [rlt]. Doing so, it modifies the reification
      environment [envs]. Moreover, we need to create fresh
      evars; this is why we give back the [goal], accordingly
      updated. *)
  
  val t_of_constr : Coq.goal_sigma -> Coq.Relation.t -> envs -> (EConstr.constr * EConstr.constr) -> Matcher.Terms.t * Matcher.Terms.t * Coq.goal_sigma

  (** [add_symbol] adds a given binary symbol to the environment of
      known stuff. *)
  val add_symbol : Coq.goal_sigma -> Coq.Relation.t -> envs -> Constr.t -> Coq.goal_sigma

  (** {2 Reconstruction: from AST back to Coq terms  }
     
      The next functions allow one to map OCaml abstract syntax trees
      to Coq terms. We need two functions to rebuild different kind of
      terms: first, raw terms, like the one encountered by
      {!t_of_constr}; second, reified Coq terms, that are required for
      the reflexive decision procedure. *)

  type ir
  val ir_of_envs : Coq.goal_sigma -> Coq.Relation.t -> envs -> Coq.goal_sigma * ir
  val ir_to_units : ir -> Matcher.ext_units

  (** {2 Building raw, natural, terms} *)
       
  (** [raw_constr_of_t] rebuilds a term in the raw representation, and
      reconstruct the named products on top of it. In particular, this
      allow us to print the context put around the left (or right)
      hand side of a pattern. *)
  val raw_constr_of_t : ir ->  Coq.Relation.t -> EConstr.rel_context -> Matcher.Terms.t -> EConstr.constr

  (** {2 Building reified terms} *)

  (** The reification environments, as Coq constrs *)

  type sigmas = {
    env_sym : EConstr.constr;
    env_bin : EConstr.constr;
    env_units : EConstr.constr; 		(* the [idx -> X:constr] *)
  }
    


  (** We need to reify two terms (left and right members of a goal)
      that share the same reification envirnoment. Therefore, we need
      to add letins to the proof context in order to ensure some
      sharing in the proof terms we produce.

      Moreover, in order to have as much sharing as possible, we also
      add letins for various partial applications that are used
      throughout the terms.
     
      To achieve this, we decompose the reconstruction function into
      two steps: first, we build the reification environment and then
      reify each term successively.*)
  type reifier

  val mk_reifier :   Coq.Relation.t -> EConstr.constr -> ir -> (sigmas * reifier -> Proof_type.tactic) -> Proof_type.tactic

  (** [reif_constr_of_t  reifier t] rebuilds the term [t] in the
      reified form. *)
  val reif_constr_of_t : reifier -> Matcher.Terms.t -> EConstr.constr

end
