(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Debugging functions, that can be triggered on a per-file base.  *)

module type CONTROL =			
sig
  val debug : bool
  val time : bool
  val printing : bool
end
module Debug :
  functor (X : CONTROL) ->
sig
      (** {!debug} prints the string and end it with a newline  *)
      val debug : string -> unit
      val debug_exception : string -> exn -> unit

      (** {!time} computes the time spent in a function, and then
      print it using the given format *)
      val time :
        ('a -> 'b) -> 'a -> (float -> unit, out_channel, unit) format -> 'b
	
      (** {!pr_constr} print a Coq constructor, that can be labelled
      by a string *)
      val pr_constr : string -> Term.constr -> unit

    end
