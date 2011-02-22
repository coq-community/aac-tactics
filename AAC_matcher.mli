(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Standalone module containing the algorithm for matching modulo
    associativity and associativity and commutativity
    (AAC). Additionnaly, some A or AC operators can have units (U).

    This module could be reused outside of the Coq plugin.

    Matching a pattern [p] against a term [t] modulo AACU boils down
    to finding a substitution [env] such that the pattern [p]
    instantiated with [env] is equal to [t] modulo AACU.

    We proceed by structural decomposition of the pattern, trying all
    possible non-deterministic splittings of the subject, when needed. The
    function {!matcher} is limited to top-level matching, that is, the
    subject must make a perfect match against the pattern ([x+x] does
    not match [a+a+b] ).
   
    We use a search monad {!AAC_search_monad} to perform non-deterministic
    choices in an almost transparent way.

    We also provide a function {!subterm} for finding a match that is
    a subterm of the subject modulo AACU. In particular, this function
    gives a solution to the aforementioned case ([x+x] against
    [a+b+a]).

    On a slightly more involved level :
    - it must be noted that we allow several AC/A operators to share
    the same units, but that a given AC/A operator can have at most
    one unit.

    - if the pattern does not contain "hard" symbols (like constants,
    function symbols, AC or A symbols without units), there can be
    infinitely many subterms such that the pattern matches: it is
    possible to build "subterms" modulo AAC and U that make the size
    of the term increase (by making neutral elements appear in a
    layered fashion). Hence, in this case, a warning is issued, and
    some solutions are omitted.
   
*)

(** {2 Utility functions}  *)

type symbol = int
type var = int

(** Relationship between units and operators. This is a sparse
    representation of a matrix of couples [(op,unit)] where [op] is
    the index of the operation, and [unit] the index of the relevant
    unit. We make the assumption that any operation has 0 or 1 unit,
    and that operations can share a unit). *)

type units =(symbol * symbol) list (* from AC/A symbols to the unit *)
type ext_units =
    {
      unit_for : units; (* from AC/A symbols to the unit *)     
      is_ac : (symbol * bool) list
    } 	


(** The arguments of sums (or AC operators) are represented using finite multisets.
    (Typically, [a+b+a] corresponds to [2.a+b], i.e. [Sum[a,2;b,1]]) *)
type 'a mset = ('a * int) list

(** [linear] expands a multiset into a simple list *)
val linear : 'a mset -> 'a list

(** Representations of expressions

    The module {!Terms} defines  two different types for expressions.
    - a public type {!Terms.t} that represents abstract syntax trees
    of expressions with binary associative and commutative operators
    - a private type {!Terms.nf_term}, corresponding to a canonical
    representation for the above terms modulo AACU. The construction
    functions on this type ensure that these terms are in normal form
    (that is, no sum can appear as a subterm of the same sum, no
    trailing units, lists corresponding to multisets are sorted,
    etc...).

*)
module Terms  :
sig

  (** {2 Abstract syntax tree of terms and patterns}

      We represent both terms and patterns using the following datatype.

      Values of type [symbol] are used to index symbols. Typically,
      given two associative operations [(^)] and [( * )], and two
      morphisms [f] and [g], the term [f (a^b) (a*g b)] is represented
      by the following value
      [Sym(0,[| Dot(1, Sym(2,[||]), Sym(3,[||]));
                Dot(4, Sym(2,[||]), Sym(5,[|Sym(3,[||])|])) |])]
      where the implicit symbol environment associates
      [f] to [0], [(^)] to [1], [a] to [2], [b] to [3], [( * )] to [4], and [g] to [5],

      Accordingly, the following value, that contains "variables"
      [Sym(0,[| Dot(1, Var x, Unit (1); Dot(4, Var x,
      Sym(5,[|Sym(3,[||])|])) |])] represents the pattern [forall x, f
      (x^1) (x*g b)]. The relationship between [1] and [( * )] is only
      mentionned in the units table.  *)

  type t =
      Dot of (symbol * t * t)
    | Plus of (symbol * t * t)
    | Sym of (symbol * t array)
    | Var of var
    | Unit of symbol

  (** Test for equality of terms modulo AACU (relies on the following
      canonical representation of terms).  Note than two different
      units of a same operator are not considered equal.  *)
  val equal_aac : units ->  t -> t -> bool


  (** {2 Normalised terms (canonical representation) }
     
      A term in normal form is the canonical representative of the
      equivalence class of all the terms that are equal modulo AACU.
      This representation is only used internally; it is exported here
      for the sake of completeness *)

  type nf_term

  (** {3 Comparisons} *)

  val nf_term_compare : nf_term -> nf_term -> int
  val nf_equal : nf_term -> nf_term -> bool   

  (** {3 Printing function}  *)

  val sprint_nf_term : nf_term -> string

  (** {3 Conversion functions}  *)

  (** we have the following property: [a] and [b] are equal modulo AACU
      iif [nf_equal (term_of_t a) (term_of_t b) = true]   *)
  val term_of_t : units -> t -> nf_term
  val t_of_term  : nf_term -> t

end


(** Substitutions (or environments)

    The module {!Subst} contains infrastructure to deal with
    substitutions, i.e., functions from variables to terms.  Only a
    restricted subsets of these functions need to be exported.
   
    As expected, a particular substitution can be used to
    instantiate a pattern.
*)
module Subst :
sig
  type t
  val sprint : t -> string
  val instantiate : t -> Terms.t-> Terms.t
  val to_list : t -> (var*Terms.t) list
end


(** {2 Main functions exported by this module}  *)

(** [matcher p t] computes the set of solutions to the given top-level
    matching problem ([p] is the pattern, [t] is the term).  If the
    [strict] flag is set, solutions where units are used to
    instantiate some variables are excluded, unless this unit appears
    directly under a function symbol (e.g., f(x) still matches f(1),
    while x+x+y does not match a+b+c, since this would require to
    assign 1 to x).
*)
val matcher : ?strict:bool -> ext_units -> Terms.t -> Terms.t -> Subst.t AAC_search_monad.m

(** [subterm p t] computes a set of solutions to the given
    subterm-matching problem.
   
    Return a collection of possible solutions (each with the
    associated depth, the context, and the solutions of the matching
    problem). The context is actually a {!Terms.t} where the variables
    are yet to be instantiated by one of the associated substitutions
*)
val subterm : ?strict:bool -> ext_units -> Terms.t -> Terms.t -> (int * Terms.t * Subst.t AAC_search_monad.m) AAC_search_monad.m

