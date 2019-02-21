(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** aac_rewrite -- rewriting modulo A or AC*)

val aac_reflexivity : unit Proofview.tactic
val aac_normalise : unit Proofview.tactic

val aac_rewrite :
  args:(string * int) list ->
  ?abort:bool ->
  ?l2r:bool ->
  ?show:bool ->
  ?strict:bool -> ?extra:EConstr.t -> EConstr.constr -> unit Proofview.tactic

val add : string -> 'a -> (string * 'a) list -> (string * 'a) list

val pr_aac_args : 'a -> 'b -> 'c -> (string * int) list -> Pp.t
