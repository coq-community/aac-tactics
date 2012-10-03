(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** aac_rewrite -- rewriting modulo  *)


module Control =   struct
    let debug = false
    let printing = false
    let time = false
end

module Debug = Helper.Debug (Control)
open Debug

let time_tac msg tac =
  if Control.time then  Coq.tclTIME msg tac else tac

let tac_or_exn tac exn msg = fun gl ->
  try tac gl with e ->
    pr_constr "last goal" (Tacmach.pf_concl gl);
    exn msg e

(* helper to be used with the previous function: raise a new anomaly
   except if a another one was previously raised *)
let push_anomaly msg = function
  | Util.Anomaly _ as e -> raise e
  | _ -> Coq.anomaly msg

module M = Matcher

open Term
open Names
open Coqlib
open Proof_type

(** The various kind of relation we can encounter, as a hierarchy *)
type rew_relation =
  | Bare of Coq.Relation.t
  | Transitive of Coq.Transitive.t
  | Equivalence of Coq.Equivalence.t

(** {!promote try to go higher in the aforementionned hierarchy} *)
let promote (rlt : Coq.Relation.t) (k : rew_relation -> Proof_type.tactic) =
  try Coq.Equivalence.cps_from_relation rlt
	(fun e -> k (Equivalence e))
  with
    | Not_found ->
      begin
	try Coq.Transitive.cps_from_relation rlt
	      (fun trans -> k (Transitive trans))
	with
	  |Not_found -> k (Bare rlt)
      end


(*
  Various situations:
  p == q |- left == right : rewrite <- ->
  p <= q |- left <= right : rewrite ->
  p <= q |- left == right : failure
  p == q |- left <= right : rewrite <- ->
 
  Not handled
  p <= q |- left >= right : failure
*)

(** aac_lift : the ideal type beyond AAC.v/Lift

    A base relation r, together with an equivalence relation, and the
    proof that the former lifts to the later. Howver, we have to
    ensure manually the invariant : r.carrier == e.carrier, and that
    lift connects the two things *)
type aac_lift =
    {
      r : Coq.Relation.t;
      e : Coq.Equivalence.t;
      lift : Term.constr    
    }
     
type rewinfo =
    {
      hypinfo : Coq.Rewrite.hypinfo;
     
      in_left : bool; 	     		(** are we rewriting in the left hand-sie of the goal *)
      pattern : constr;
      subject : constr;
      morph_rlt : Coq.Relation.t; (** the relation we look for in morphism *)
      eqt : Coq.Equivalence.t;    (** the equivalence we use as workbase *)
      rlt : Coq.Relation.t;	  (** the relation in the goal  *)
      lifting: aac_lift
    }

let infer_lifting (rlt: Coq.Relation.t) (k : lift:aac_lift -> Proof_type.tactic) : Proof_type.tactic =
  Coq.cps_evar_relation rlt.Coq.Relation.carrier (fun e ->
    let lift_ty =
      mkApp (Lazy.force Theory.Stubs.lift,
	     [|
	       rlt.Coq.Relation.carrier;
	       rlt.Coq.Relation.r;
	       e
	     |]
      ) in
    Coq.cps_resolve_one_typeclass ~error:"Cannot infer a lifting"
      lift_ty (fun lift goal ->
      let x = rlt.Coq.Relation.carrier in
      let r = rlt.Coq.Relation.r in
      let eq =  (Coq.nf_evar goal e) in 
      let equiv = Coq.lapp Theory.Stubs.lift_proj_equivalence [| x;r;eq; lift |] in
      let lift =
	{
	  r = rlt;
	  e = Coq.Equivalence.make x eq equiv;
	  lift = lift;
	}
      in
      k ~lift:lift  goal
    ))
     
(** Builds a rewinfo, once and for all *)
let dispatch in_left (left,right,rlt) hypinfo (k: rewinfo -> Proof_type.tactic ) : Proof_type.tactic=
  let l2r = hypinfo.Coq.Rewrite.l2r in
  infer_lifting rlt
    (fun ~lift ->
      let eq = lift.e in
      k {
	hypinfo = hypinfo;
	in_left = in_left;
	pattern = if l2r then hypinfo.Coq.Rewrite.left else hypinfo.Coq.Rewrite.right;
	subject = if in_left then  left else right;
	morph_rlt = Coq.Equivalence.to_relation eq;
	eqt = eq;
	lifting = lift;
	rlt = rlt
      }
    )
   
   

(** {1 Tactics} *)


(** Build the reifiers, the reified terms, and the evaluation fonction  *)
let handle eqt zero envs (t : Matcher.Terms.t) (t' : Matcher.Terms.t) k =

  let (x,r,_) = Coq.Equivalence.split eqt  in
  Theory.Trans.mk_reifier (Coq.Equivalence.to_relation eqt) zero envs 
    (fun (maps, reifier) ->
      (* fold through a term and reify *)
      let t = Theory.Trans.reif_constr_of_t reifier t in
      let t' = Theory.Trans.reif_constr_of_t reifier  t' in
      (* Some letins  *)
      let eval = (mkApp (Lazy.force Theory.Stubs.eval, [|x;r; maps.Theory.Trans.env_sym; maps.Theory.Trans.env_bin; maps.Theory.Trans.env_units|])) in
     
      Coq.cps_mk_letin "eval" eval (fun eval ->
	Coq.cps_mk_letin "left" t (fun t ->
	  Coq.cps_mk_letin "right" t' (fun t' ->
	    k maps eval t t'))))

(** [by_aac_reflexivity] is a sub-tactic that closes a sub-goal that
      is merely a proof of equality of two terms modulo AAC *) 
let by_aac_reflexivity zero
    eqt envs (t : Matcher.Terms.t) (t' : Matcher.Terms.t) : Proof_type.tactic =
  handle eqt zero envs t t'
    (fun maps eval t t' ->
      let (x,r,e) = Coq.Equivalence.split eqt in
      let decision_thm = Coq.lapp Theory.Stubs.decide_thm
	[|x;r;e;
	  maps.Theory.Trans.env_sym;
	  maps.Theory.Trans.env_bin;
	  maps.Theory.Trans.env_units;
	  t;t';
	|]
      in
      (* This convert is required to deal with evars in a proper
	 way *)
      let convert_to = mkApp (r, [| mkApp (eval,[| t |]); mkApp (eval, [|t'|])|])   in
      let convert = Tactics.convert_concl convert_to Term.VMcast in
      let apply_tac = Tactics.apply decision_thm in
      (Tacticals.tclTHENLIST
	 [
	   convert ;
	   tac_or_exn apply_tac Coq.user_error "unification failure";
	   tac_or_exn (time_tac "vm_norm" (Tactics.normalise_in_concl)) Coq.anomaly "vm_compute failure";
	   Tacticals.tclORELSE Tactics.reflexivity
	     (Tacticals.tclFAIL 0 (Pp.str "Not an equality modulo A/AC"))
	 ])
    )

let by_aac_normalise zero lift ir t t' =
  let eqt = lift.e in
  let rlt = lift.r in
  handle eqt zero ir t t'
    (fun  maps eval t t' ->
      let (x,r,e) = Coq.Equivalence.split eqt in
      let normalise_thm = Coq.lapp Theory.Stubs.lift_normalise_thm
	[|x;r;e;
	  maps.Theory.Trans.env_sym;
	  maps.Theory.Trans.env_bin;
	  maps.Theory.Trans.env_units;
	  rlt.Coq.Relation.r;
	  lift.lift;
	  t;t';
	|]
      in
      (* This convert is required to deal with evars in a proper
	 way *)
      let convert_to = mkApp (rlt.Coq.Relation.r, [| mkApp (eval,[| t |]); mkApp (eval, [|t'|])|])   in
      let convert = Tactics.convert_concl convert_to Term.VMcast in
      let apply_tac = Tactics.apply normalise_thm in
      (Tacticals.tclTHENLIST
	 [
	   convert ;
	   apply_tac;
	 ])
	
    )

(** A handler tactic, that reifies the goal, and infer the liftings,
    and then call its continuation *)
let aac_conclude
    (k : Term.constr -> aac_lift -> Theory.Trans.ir -> Matcher.Terms.t -> Matcher.Terms.t -> Proof_type.tactic) = fun goal ->

    let (equation : Term.types) = Tacmach.pf_concl goal in
    let envs = Theory.Trans.empty_envs () in
    let left, right,r =
      match Coq.match_as_equation goal equation with
	| None -> Coq.user_error "The goal is not an applied relation"
	| Some x -> x in    
    try infer_lifting r
      (fun ~lift  goal ->
	let eq = Coq.Equivalence.to_relation lift.e in
	let tleft,tright, goal = Theory.Trans.t_of_constr goal eq envs (left,right)   in
	let goal, ir = Theory.Trans.ir_of_envs goal eq envs in
	let concl = Tacmach.pf_concl goal in
	let _ = pr_constr "concl "concl in 	     
	let evar_map = Tacmach.project goal in
	Tacticals.tclTHEN
	  (Refiner.tclEVARS evar_map)
	  (k left lift ir tleft tright)
	  goal
      )goal
  with
    | Not_found -> Coq.user_error "No lifting from the goal's relation to an equivalence"

open Libnames
open Tacinterp

let aac_normalise = fun goal ->
  let ids = Tacmach.pf_ids_of_hyps goal in
  Tacticals.tclTHENLIST
    [
      aac_conclude by_aac_normalise;
      Tacinterp.interp (
	(* TODO: replace "__aac_x/y__" with dynamically generated fresh names
	   (I don't know how to do this with this syntax) *)
      	<:tactic<
	  intro __aac_x__;
	  intro __aac_y__;
	  vm_compute in __aac_x__;
	  vm_compute in __aac_y__;
	  unfold __aac_x__;
	  unfold __aac_y__;
      	  compute [Internal.eval Internal.fold_map Internal.copy Prect]; simpl
      	>>
      );
      Tactics.keep ids
    ] goal

let aac_reflexivity = fun goal ->
  aac_conclude
    (fun zero lift ir t t' ->
      let x,r = Coq.Relation.split (lift.r) in
      let r_reflexive = (Coq.Classes.mk_reflexive x r) in
      Coq.cps_resolve_one_typeclass ~error:"The goal's relation is not reflexive"
	r_reflexive
	(fun reflexive ->
	  let lift_reflexivity =
	    mkApp (Lazy.force (Theory.Stubs.lift_reflexivity),
		   [|
		     x;
		     r;
		     lift.e.Coq.Equivalence.eq;
		     lift.lift;
		     reflexive
		   |])
	  in
	  Tacticals.tclTHEN
	    (Tactics.apply lift_reflexivity)
	    (fun goal ->
	      let concl = Tacmach.pf_concl goal in
	      let _ = pr_constr "concl "concl in 	     
	      by_aac_reflexivity zero lift.e ir t t' goal)
	)
    ) goal

(** A sub-tactic to lift the rewriting using Lift  *)
let lift_transitivity in_left (step:constr) preorder lifting (using_eq : Coq.Equivalence.t): tactic =
  fun goal ->
    (* catch the equation and the two members*)
    let concl = Tacmach.pf_concl goal in
    let (left, right, _ ) = match  Coq.match_as_equation goal concl with
      | Some x -> x
      | None -> Coq.user_error "The goal is not an equation"
    in
    let lift_transitivity =
      let thm = 
	if in_left
	then
	  Lazy.force Theory.Stubs.lift_transitivity_left
	else
	  Lazy.force Theory.Stubs.lift_transitivity_right
      in
      mkApp (thm,
	     [|
	       preorder.Coq.Relation.carrier;
	       preorder.Coq.Relation.r;
	       using_eq.Coq.Equivalence.eq;
	       lifting;
	       step;
	       left;
	       right;
	     |])
    in
    Tacticals.tclTHENLIST
      [
	Tactics.apply lift_transitivity
      ] goal


(** The core tactic for aac_rewrite *)
let core_aac_rewrite ?abort
    rewinfo
    subst
    (by_aac_reflexivity : Matcher.Terms.t -> Matcher.Terms.t -> Proof_type.tactic)
    (tr : constr) t left : tactic =
  pr_constr "transitivity through" tr;   
  let tran_tac =
    lift_transitivity rewinfo.in_left tr rewinfo.rlt rewinfo.lifting.lift rewinfo.eqt
  in
  Coq.Rewrite.rewrite ?abort rewinfo.hypinfo subst (fun rew -> 
    Tacticals.tclTHENSV
      (tac_or_exn (tran_tac) Coq.anomaly "Unable to make the transitivity step")
      (
	if rewinfo.in_left
	then [| by_aac_reflexivity left t ; rew |]
	else [| by_aac_reflexivity t left ; rew  |]
      )
  )

exception NoSolutions


(** Choose a substitution from a
    [(int * Terms.t * Env.env Search_monad.m) Search_monad.m ] *)
(* WARNING: Beware, since the printing function can change the order of the
   printed monad, this function has to be updated accordingly *)
let choose_subst  subterm sol m=
  try
    let (depth,pat,envm) =  match subterm with
      | None -> 			(* first solution *)
	List.nth ( List.rev (Search_monad.to_list m)) 0
      | Some x ->
	List.nth ( List.rev (Search_monad.to_list m)) x
    in
    let env = match sol with
	None -> 	
	  List.nth ( (Search_monad.to_list envm)) 0
      | Some x ->  List.nth ( (Search_monad.to_list envm)) x
    in
    pat, env
  with
    | _ -> raise NoSolutions
	
(** rewrite the constr modulo AC from left to right in the left member
    of the goal *)
let aac_rewrite  ?abort rew ?(l2r=true) ?(show = false) ?(in_left=true) ?strict ~occ_subterm ~occ_sol ?extra : Proof_type.tactic  = fun goal ->
  let envs = Theory.Trans.empty_envs () in
  let (concl : Term.types) = Tacmach.pf_concl goal in
  let (_,_,rlt) as concl =
    match Coq.match_as_equation goal concl with
      | None -> Coq.user_error "The goal is not an applied relation"
      | Some (left, right, rlt) -> left,right,rlt
  in
  let check_type x =
    Tacmach.pf_conv_x goal x rlt.Coq.Relation.carrier
  in
  Coq.Rewrite.get_hypinfo rew ~l2r ?check_type:(Some check_type)
    (fun hypinfo ->
      dispatch in_left concl hypinfo
	(	
	  fun rewinfo ->
	    let goal =
	      match extra with
		| Some t -> Theory.Trans.add_symbol goal rewinfo.morph_rlt envs t
		| None -> goal
	    in
	    let pattern, subject, goal =
	      Theory.Trans.t_of_constr goal rewinfo.morph_rlt envs
		(rewinfo.pattern , rewinfo.subject)  
	    in
	    let goal, ir = Theory.Trans.ir_of_envs goal rewinfo.morph_rlt envs in

	    let units = Theory.Trans.ir_to_units ir in
	    let m =  Matcher.subterm ?strict units pattern subject in
	    (* We sort the monad in increasing size of contet *)
	    let m = Search_monad.sort (fun (x,_,_) (y,_,_) -> x -  y) m in
	   
	    if show
	    then	      
	      Print.print rewinfo.morph_rlt ir m (hypinfo.Coq.Rewrite.context) 

	    else
	      try
		let pat,subst = choose_subst occ_subterm occ_sol m in
		let tr_step = Matcher.Subst.instantiate subst pat in
		let tr_step_raw = Theory.Trans.raw_constr_of_t ir rewinfo.morph_rlt [] tr_step in
		
		let conv = (Theory.Trans.raw_constr_of_t ir rewinfo.morph_rlt (hypinfo.Coq.Rewrite.context)) in
		let subst  = Matcher.Subst.to_list subst in
		let subst = List.map (fun (x,y) -> x, conv y) subst in
		let by_aac_reflexivity = (by_aac_reflexivity rewinfo.subject rewinfo.eqt  ir) in
		core_aac_rewrite ?abort rewinfo subst by_aac_reflexivity tr_step_raw tr_step subject
		 
	      with
		| NoSolutions ->
		  Tacticals.tclFAIL 0
		    (Pp.str (if occ_subterm = None && occ_sol = None
		      then "No matching occurence modulo AC found"
		      else "No such solution"))
	)   
    ) goal


open Coq.Rewrite
open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Extraargs
open Genarg

let rec add k x = function
  | [] -> [k,x]
  | k',_ as ky::q ->
      if k'=k then Coq.user_error ("redondant argument ("^k^")")
      else ky::add k x q

let get k l = try Some (List.assoc k l) with Not_found -> None

let get_lhs l = try List.assoc "in_right" l; false with Not_found -> true

let aac_rewrite ~args =
  aac_rewrite ~occ_subterm:(get "at" args) ~occ_sol:(get "subst" args) ~in_left:(get_lhs args)


let pr_aac_args _ _ _ l =
  List.fold_left
    (fun acc -> function
       | ("in_right" as s,_) -> Pp.(++) (Pp.str s) acc
       | (k,i) -> Pp.(++) (Pp.(++) (Pp.str k)  (Pp.int i)) acc
    ) (Pp.str "") l

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
| [ "aac_reflexivity" ] -> [ aac_reflexivity ]
END

TACTIC EXTEND _aac_normalise_
| [ "aac_normalise" ] -> [ aac_normalise ]
END

TACTIC EXTEND _aac_rewrite_
| [ "aac_rewrite" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:true c gl ]
END
 
TACTIC EXTEND _aac_pattern_
| [ "aac_pattern" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:true ~abort:true c gl ]
END

TACTIC EXTEND _aac_instances_
| [ "aac_instances" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:true ~show:true c gl ]
END

TACTIC EXTEND _aacu_rewrite_
| [ "aacu_rewrite" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:false c gl ]
END
 
TACTIC EXTEND _aacu_pattern_
| [ "aacu_pattern" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:false ~abort:true c gl ]
END

TACTIC EXTEND _aacu_instances_
| [ "aacu_instances" orient(l2r) constr(c) aac_args(args) constro(extra)] ->
  [ fun gl -> aac_rewrite ?extra ~args ~l2r ~strict:false ~show:true c gl ]
END
