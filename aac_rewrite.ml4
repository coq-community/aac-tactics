(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** aac_rewrite -- rewriting modulo  *)

open Pcoq.Prim
open Pcoq.Constr
open Ltac_plugin
open Stdarg
open Extraargs
open Genarg

open Aac_lib

DECLARE PLUGIN "aac"


ARGUMENT EXTEND aac_args  
TYPED AS ((string * int) list ) 
PRINTED BY pr_aac_args
| [ "at" integer(n) aac_args(q) ] -> [ add "at" n q ]
| [ "subst" integer(n) aac_args(q) ] -> [ add "subst" n q ]
| [ "in_right" aac_args(q) ] -> [ add "in_right" 0 q ]
| [ ] -> [ [] ]
END

let pr_constro _ _ _ = fun b ->
  match b with
    | None ->  Pp.str ""
    | Some o -> Pp.str "<constr>"

ARGUMENT EXTEND constro
TYPED AS (constr option) 
PRINTED BY pr_constro
| [ "[" constr(c) "]" ] -> [ Some c ]
| [ ] -> [ None ]
END

TACTIC EXTEND _aac_reflexivity_
| [ "aac_reflexivity" ] -> [ Proofview.V82.tactic aac_reflexivity ]
END

TACTIC EXTEND _aac_normalise_
| [ "aac_normalise" ] -> [ Proofview.V82.tactic aac_normalise ]
END

TACTIC EXTEND _aac_rewrite_
| [ "aac_rewrite" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ Proofview.V82.tactic (fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:true c gl) ]
END
 
TACTIC EXTEND _aac_pattern_
| [ "aac_pattern" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ Proofview.V82.tactic (fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:true ~abort:true c gl) ]
END

TACTIC EXTEND _aac_instances_
| [ "aac_instances" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ Proofview.V82.tactic (fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:true ~show:true c gl) ]
END

TACTIC EXTEND _aacu_rewrite_
| [ "aacu_rewrite" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ Proofview.V82.tactic (fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:false c gl) ]
END
 
TACTIC EXTEND _aacu_pattern_
| [ "aacu_pattern" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ Proofview.V82.tactic (fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:false ~abort:true c gl) ]
END

TACTIC EXTEND _aacu_instances_
| [ "aacu_instances" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ Proofview.V82.tactic (fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:false ~show:true c gl) ]
END
