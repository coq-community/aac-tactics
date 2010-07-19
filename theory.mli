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
    AAC.v}.

    This module interfaces with the above Coq module; it provides
    facilities to interpret a term with arbitrary operators as an
    abstract syntax tree, and to convert an AST into a Coq term
    (either using the Coq "raw" terms, as written in the starting
    goal, or using the reified Coq datatypes we define in {i
    AAC.v}).
*)




(** Environments *)
module Sigma:
sig
  (**  [add ty n x map] adds the value [x] of type [ty] with key [n] in [map]  *)
  val add: Term.constr ->Term.constr ->Term.constr ->Term.constr ->Term.constr
    
  (** [empty ty] create an empty map of type [ty]  *)
  val empty: Term.constr ->Term.constr

  (** [of_list ty null l] translates an OCaml association list into a Coq one *)
  val of_list: Term.constr -> Term.constr -> (int * Term.constr ) list -> Term.constr

  (** [to_fun ty null map] converts a Coq association list into a Coq function (with default value [null]) *)
  val to_fun: Term.constr ->Term.constr ->Term.constr ->Term.constr
end

(** The constr associated with our typeclasses for AC or A operators *)
val op_ac:Term.constr lazy_t
val op_a:Term.constr lazy_t
  
(** The evaluation fonction, used to convert a reified coq term to a
    raw coq term *)
val eval: Term.constr lazy_t
  
(** The main lemma of our theory, that is 
    [compare (norm u) (norm v) = Eq -> eval u == eval v] *)
val decide_thm:Term.constr lazy_t

(** {2 Packaging modules} *)

(** Dynamically typed morphisms *)
module Sym:
sig
  (** mimics the Coq record [Sym.pack] *)
  type pack = {ar: Term.constr; value: Term.constr ; morph: Term.constr}

  val typ: Term.constr lazy_t

  (** [mk_typeof rlt int]  *)
  val mk_typeof: Coq.reltype ->int ->Term.constr

  (** [mk_typeof rlt int]  *)
  val mk_relof:  Coq.reltype ->int ->Term.constr

  (** [mk_pack rlt (ar,value,morph)]  *)
  val mk_pack: Coq.reltype -> pack -> Term.constr
    
  (** [null] builds a dummy symbol, given an {!Coq.eqtype} and a
      constant *)
  val null: Coq.eqtype -> Term.constr -> Term.constr
  
end

(** Dynamically typed AC operations *)
module Sum:
sig

  (** mimics the Coq record [Sum.pack] *)
  type pack = {plus : Term.constr; zero: Term.constr ; opac: Term.constr}

  val typ: Term.constr lazy_t

  (** [mk_pack rlt (plus,zero,opac)]  *)
  val mk_pack: Coq.reltype -> pack -> Term.constr
    
  (** [zero rlt pack]*)
  val zero: Coq.reltype -> Term.constr -> Term.constr

  (** [plus rlt pack]*)
  val plus: Coq.reltype -> Term.constr -> Term.constr

end


(** Dynamically typed A operations *)
module Prd:
sig

  (** mimics the Coq record [Prd.pack] *)
  type pack = {dot: Term.constr; one: Term.constr ; opa: Term.constr}

  val typ: Term.constr lazy_t

  (** [mk_pack rlt (dot,one,opa)]  *)
  val mk_pack: Coq.reltype -> pack -> Term.constr
    
  (** [one rlt pack]*)
  val one: Coq.reltype -> Term.constr -> Term.constr

  (** [dot rlt pack]*)
  val dot: Coq.reltype -> Term.constr -> Term.constr
    
end


(** [mk_equal rlt l r] builds the term [l == r] *)
val mk_equal : Coq.reltype -> Term.constr -> Term.constr -> Term.constr


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
      - an element might be the unit for several operations; the
      behaviour in this case is almost unspecified: we simply give
      priority to AC operations.
  *)
  

  (** To achieve this reification, one need to record informations
      about the collected operators (symbols, binary operators,
      units). We use the following imperative internal data-structure to
      this end. *)
  
  type envs 
  val empty_envs : unit -> envs

  (** {1 Reification: from Coq terms to AST {!Matcher.Terms.t}  } *)

  (** [t_of_constr goal rlt envs cstr] builds the abstract syntax tree
      of the term [cstr]. We rely on the [goal] to perform typeclasses
      resolutions to find morphisms compatible with the relation
      [rlt]. Doing so, it modifies the reification environment
      [envs]. Moreover, we need to create creates fresh evars; this is
      why we give back the [goal], accordingly updated. *)
  val t_of_constr : Coq.goal_sigma -> Coq.reltype -> envs -> Term.constr -> Matcher.Terms.t * Coq.goal_sigma

  (** {1 Reconstruction: from AST back to Coq terms  }
      
      The next functions allow one to map OCaml abstract syntax trees
      to Coq terms. We need two functions to rebuild different kind of
      terms: first, raw terms, like the one encountered by
      {!t_of_constr}; second, reified Coq terms, that are required for
      the reflexive decision procedure. *)

  (** {2 Building raw, natural, terms} *)

  (** [raw_constr_of_t] rebuilds a term in the raw representation *)
  val raw_constr_of_t : envs -> Coq.reltype -> Matcher.Terms.t -> Term.constr

  (** {2 Building reified terms} *)
 
  (** The reification environments, as Coq constrs *)
  type sigmas = {
    env_sym : Term.constr;
    env_sum : Term.constr;
    env_prd : Term.constr;
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

  val mk_reifier : Coq.eqtype -> envs -> Coq.goal_sigma -> sigmas * reifier * Proof_type.tactic 

  (** [reif_constr_of_t  reifier t] rebuilds the term [t] in the
      reified form. *)
  val reif_constr_of_t : reifier -> Matcher.Terms.t -> Term.constr
end
