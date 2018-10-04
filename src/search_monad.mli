(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Search monad that allows to express non-deterministic algorithms
    in a legible maner, or programs that solve combinatorial problems.

    @see <http://spivey.oriel.ox.ac.uk/mike/search-jfp.pdf> the
    inspiration of this module
*)

(** A data type that represent a collection of ['a] *)
type 'a m

  (** {2 Monadic operations}  *)

(** bind and return *)
val ( >> ) : 'a m -> ('a -> 'b m) -> 'b m
val return : 'a -> 'a m

(** non-deterministic choice *)
val ( >>| ) : 'a m -> 'a m -> 'a m

(** failure *)
val fail : unit -> 'a m

(** folding through the collection *)
val fold : ('a -> 'b -> 'b) -> 'a m -> 'b -> 'b

(** {2 Derived facilities }  *)

val sprint : ('a -> string) -> 'a m -> string
val count : 'a m -> int
val choose : 'a m -> 'a option
val to_list : 'a m -> 'a list
val sort :  ('a -> 'a -> int) -> 'a m -> 'a m
val is_empty: 'a m -> bool
val filter : ('a -> bool) -> 'a m -> 'a m 
