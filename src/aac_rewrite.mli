(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** aac_rewrite -- rewriting modulo A or AC*)

val aac_reflexivity : Coq.goal_sigma -> Proof_type.goal list Evd.sigma
val aac_normalise : Coq.goal_sigma -> Proof_type.goal list Evd.sigma

val aac_rewrite :
  ?abort:bool ->
  EConstr.constr ->
  ?l2r:bool ->
  ?show:bool ->
  ?in_left:bool ->
  ?strict:bool ->
  occ_subterm:int option ->
  occ_sol:int option -> ?extra:EConstr.t -> Proof_type.tactic
