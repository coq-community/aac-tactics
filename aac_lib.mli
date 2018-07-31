(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

val aac_rewrite :
  args:(string * int) list -> ?abort:bool -> EConstr.constr -> ?l2r:bool ->
  ?show:bool -> ?strict:bool -> ?extra:EConstr.t -> Proof_type.tactic

val aac_reflexivity : Coq.goal_sigma -> Proof_type.goal list Evd.sigma

val aac_normalise : Coq.goal_sigma -> Proof_type.goal list Evd.sigma

val add : string -> 'a -> (string * 'a) list -> (string * 'a) list

val pr_aac_args : 'a -> 'b -> 'c -> (string * int) list -> Pp.t
