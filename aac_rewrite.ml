(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** aac_rewrite -- rewriting modulo  *)
    
(* functions to handle the failures of our tactic. Some should be
   reported [anomaly], some are on behalf of the user [user_error]*)
let anomaly msg = 
  Util.anomaly ("aac_tactics: " ^ msg)

let user_error msg = 
  Util.error ("aac_tactics: " ^ msg)

(* debug and timing functions  *)
let debug = false
let printing = false
let time = false

let debug x = 
  if debug then 
    Printf.printf "%s\n%!" x
      
let pr_constr msg constr = 
  if printing then 
    (  Pp.msgnl (Pp.str (Printf.sprintf "=====%s====" msg));
       Pp.msgnl (Printer.pr_constr constr);
    )

let time msg tac =
  if time then  Coq.tclTIME msg tac
  else tac

let tac_or_exn tac exn msg =
  fun gl -> try tac gl with e -> exn msg e

(* helper to be used with the previous function: raise a new anomaly
   except if a another one was previously raised *)
let push_anomaly msg = function
  | Util.Anomaly _ as e -> raise e
  | _ -> anomaly msg

module M = Matcher

open Term
open Names
open Coqlib
open Proof_type 


(** [find_applied_equivalence goal eq] try to ensure that the goal is
    an applied equivalence relation, with two operands of the same type.

    This function is transitionnal, as we plan to integrate with the
    new rewrite features of Coq 8.3, that seems to handle this kind of
    things.
*)
let find_applied_equivalence goal : Term.constr -> Coq.eqtype *Term.constr *Term.constr* Coq.goal_sigma = fun equation ->
  let env = Tacmach.pf_env goal in 
  let evar_map = Tacmach.project goal  in
    match Coq.decomp_term equation with 
      | App(c,ca) when Array.length ca >= 2 ->
	  let n = Array.length ca  in 
	  let left  =  ca.(n-2) in 
	  let right =  ca.(n-1) in
	  let left_type = Tacmach.pf_type_of goal left in 
	  (* let right_type = Tacmach.pf_type_of goal right in  *)
	  let partial_app = mkApp (c, Array.sub ca 0 (n-2) ) in 
	  let eq_type = Coq.Classes.mk_equivalence left_type partial_app in 
	    begin 
	      try 
		let evar_map, equivalence = Typeclasses.resolve_one_typeclass env evar_map eq_type in 
		  let goal = Coq.goal_update goal evar_map in 
		    ((left_type, partial_app), equivalence),left, right, goal 
	      with 
		| Not_found -> user_error "The goal is not an applied equivalence"
	    end
      | _ -> user_error "The goal is not an equation"
	  

(* [find_applied_equivalence_force] brutally decomposes the given
   equation, and fail if we find a relation that is not the same as
   the one we look for [r] *)
let find_applied_equivalence_force rlt goal : Term.constr -> Term.constr *Term.constr* Coq.goal_sigma = fun equation ->
  match Coq.decomp_term equation with 
    | App(c,ca) when Array.length ca >= 2 ->
	let n = Array.length ca  in 
	let left  =  ca.(n-2) in 
	let right =  ca.(n-1) in
	let partial_app = mkApp (c, Array.sub ca 0 (n-2) ) in 
	let _ = if snd rlt = partial_app then () else user_error "The goal and the hypothesis have different top-level relations" in

	  left, right, goal 
    | _ -> user_error "The hypothesis is not an equation"
	
	
  	
(** Build a couple of [t] from an hypothesis (variable names are not
    relevant) *)
let rec t_of_hyp goal rlt envs  e =  match Coq.decomp_term e with
  | Prod (name,ty,c) -> let x, y = t_of_hyp goal rlt envs  c 
    in x,y+1
  | _ -> 
      let l,r ,goal = find_applied_equivalence_force rlt goal e in 
      let l,goal = Theory.Trans.t_of_constr goal rlt envs l in 	
      let r,goal = Theory.Trans.t_of_constr goal rlt envs r in 
	(l,r),0
      
(** @deprecated: [option_rip] will be removed as soon as a proper interface is
    given to the user *)
let option_rip = function | Some x -> x | None -> raise Not_found

let mk_hyp_app conv c env = 
  let l = Matcher.Subst.to_list env in 
  let l = List.sort (fun (x,_) (y,_) -> compare y x) l in
  let l = List.map (fun x -> conv (snd x)) l in 
  let v = Array.of_list l in 
    mkApp (c,v) 
  
    

(** {1 Tactics} *)

(** [by_aac_reflexivity] is a sub-tactic that closes a sub-goal that
      is merely a proof of equality of two terms modulo AAC *)

let by_aac_reflexivity eqt envs (t : Matcher.Terms.t) (t' : Matcher.Terms.t) : Proof_type.tactic = fun goal -> 
  let maps, reifier,reif_letins = Theory.Trans.mk_reifier eqt envs goal in 
  let ((x,r),e) = eqt in 

  (* fold through a term and reify *)
  let t = Theory.Trans.reif_constr_of_t reifier t in 
  let t' = Theory.Trans.reif_constr_of_t reifier  t' in 

  (* Some letins  *)
  let eval, eval_letin = Coq.mk_letin' "eval_name"  (mkApp (Lazy.force Theory.eval, [|x;r; maps.Theory.Trans.env_sym; maps.Theory.Trans.env_prd; maps.Theory.Trans.env_sum|])) in 
  let _ = pr_constr "left" t in     
  let _ = pr_constr "right" t' in     
  let t , t_letin = Coq.mk_letin "left" t in 
  let t', t_letin'= Coq.mk_letin "right" t' in 
  let apply_tac = Tactics.apply (
    mkApp (Lazy.force Theory.decide_thm, [|x;r;e; maps.Theory.Trans.env_sym; maps.Theory.Trans.env_prd; maps.Theory.Trans.env_sum;t;t'|])) 
  in 
    Tactics.tclABSTRACT None
      (Tacticals.tclTHENLIST
	 [
	   tac_or_exn reif_letins anomaly "invalid letin (1)";
	   tac_or_exn eval_letin  anomaly "invalid letin (2)";
	   tac_or_exn t_letin     anomaly "invalid letin (3)";
	   tac_or_exn t_letin'    anomaly "invalid letin (4)";
	   tac_or_exn apply_tac   anomaly "could not apply the decision theorem";
	   tac_or_exn (time "vm_norm" (Tactics.normalise_vm_in_concl)) anomaly "vm_compute failure";
	   Tacticals.tclORELSE Tactics.reflexivity
	     (Tacticals.tclFAIL 0 (Pp.str "Not an equality modulo A/AC"))
	 ])
      goal
      

(** The core tactic for aac_rewrite *)
let core_aac_rewrite  ?(l2r = true) envs eqt rew  p subst left = fun goal ->
  let rlt = fst eqt in 
  let t = Matcher.Subst.instantiate subst p in 
  let tr = Theory.Trans.raw_constr_of_t envs rlt t in 
  let tac_rew_l2r = 
    if l2r then Equality.rewriteLR rew else Equality.rewriteRL rew 
  in 
    pr_constr "transitivity through" tr;    
    Tacticals.tclTHENSV 
      (tac_or_exn (Tactics.transitivity tr) anomaly "Unable to make the transitivity step")
      [| 
	(* si by_aac_reflexivity foire (pas un theoreme), il fait tclFAIL, et on rattrape ici *)
	tac_or_exn (time "by_aac_refl" (by_aac_reflexivity eqt envs left t)) push_anomaly "Invalid transitivity step";
	tac_or_exn (tac_rew_l2r) anomaly "Unable to rewrite";
      |] goal

exception NoSolutions

(** Choose a substitution from a 
    [(int * Terms.t * Env.env Search.m) Search.m ] *)
let choose_subst  subterm sol m=
  try 
    let (depth,pat,envm) =  match subterm with 
      | None -> 			(* first solution *)
	  option_rip (Matcher.Search.choose m) 
      | Some x -> 
	  List.nth (List.rev (Matcher.Search.to_list m)) x 
    in 
    let env = match sol with 
	None -> 	option_rip (Matcher.Search.choose envm) 
      | Some x ->  List.nth (List.rev (Matcher.Search.to_list envm)) x 
    in 
      pat, env
  with
    | _ -> raise NoSolutions
	
(** rewrite the constr modulo AC from left to right in the
    left member of the goal
*)
let aac_rewrite  rew ?(l2r=true) ?(show = false) ?strict ?occ_subterm ?occ_sol : Proof_type.tactic  = fun goal ->
  let envs = Theory.Trans.empty_envs () in 
  let rew_type = Tacmach.pf_type_of  goal rew in  
  let (gl : Term.types) = Tacmach.pf_concl goal in 
  let _ = pr_constr "h" rew_type in 
  let _ = pr_constr "gl" gl in 
  let eqt, left, right, goal = find_applied_equivalence goal gl in 
  let rlt = fst eqt in 
  let left,goal = Theory.Trans.t_of_constr goal rlt envs left   in 
  let right,goal = Theory.Trans.t_of_constr goal rlt envs right in 
  let (hleft,hright),hn = t_of_hyp goal rlt envs rew_type in
  let pattern = if l2r then hleft else hright in  
  let m =  Matcher.subterm ?strict pattern  left in 
    
  let m = Matcher.Search.sort (fun (x,_,_) (y,_,_) -> x -  y) m in 
    if show
    then
      let _ = Pp.msgnl (Pp.str "All solutions:") in 
      let _ = Pp.msgnl (Matcher.pp_all (fun t -> Printer.pr_constr (Theory.Trans.raw_constr_of_t envs rlt t) ) m) in 
	Tacticals.tclIDTAC goal
    else
      try 
	let pat,env = choose_subst occ_subterm occ_sol m in 
	let rew = mk_hyp_app  (Theory.Trans.raw_constr_of_t envs rlt )rew env in 
	  core_aac_rewrite ~l2r envs eqt rew pat env left goal
      with 
	| NoSolutions -> Tacticals.tclFAIL 0 
	    (Pp.str (if occ_subterm = None && occ_sol = None 
		     then "No matching subterm found" 
		     else "No such solution")) goal  

  	  
let aac_reflexivity : Proof_type.tactic = fun goal ->
  let (gl : Term.types) = Tacmach.pf_concl goal in 
  let envs = Theory.Trans.empty_envs() in 
  let eqt, left, right, evar_map = find_applied_equivalence goal gl in 
  let rlt = fst eqt in 
  let left,goal = Theory.Trans.t_of_constr goal rlt envs left   in 
  let right,goal = Theory.Trans.t_of_constr goal rlt envs right in 
    by_aac_reflexivity eqt envs  left right goal


open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Extraargs

      (* Adding entries to the grammar of tactics *)
TACTIC EXTEND _aac1_    
| [ "aac_reflexivity" ] -> [ aac_reflexivity ]
END


TACTIC EXTEND _aac2_    
| [ "aac_rewrite" orient(o) constr(c) "subterm" integer(i) "subst" integer(j)] ->
    [ fun gl -> aac_rewrite ~l2r:o ~strict:true ~occ_subterm:i ~occ_sol:j c gl ]
END

TACTIC EXTEND _aac3_    
| [ "aac_rewrite" orient(o) constr(c) "subst" integer(j)] ->
    [ fun gl -> aac_rewrite  ~l2r:o ~strict:true ~occ_subterm:0 ~occ_sol:j c gl ]
END

TACTIC EXTEND _aac4_    
| [ "aac_rewrite" orient(o) constr(c) "subterm" integer(i)] ->
    [ fun gl -> aac_rewrite  ~l2r:o ~strict:true ~occ_subterm:i ~occ_sol:0 c gl ]
END

TACTIC EXTEND _aac5_    
| [ "aac_rewrite" orient(o) constr(c) ] ->
    [ fun gl -> aac_rewrite  ~l2r:o ~strict:true c gl ]
END

TACTIC EXTEND _aac6_    
| [ "aac_instances" orient(o) constr(c)] ->
    [ fun gl -> aac_rewrite  ~l2r:o ~strict:true ~show:true c gl ]
END




TACTIC EXTEND _aacu2_    
| [ "aacu_rewrite" orient(o) constr(c) "subterm" integer(i) "subst" integer(j)] ->
    [ fun gl -> aac_rewrite  ~l2r:o ~occ_subterm:i ~occ_sol:j c gl ]
END

TACTIC EXTEND _aacu3_    
| [ "aacu_rewrite" orient(o) constr(c) "subst" integer(j)] ->
    [ fun gl -> aac_rewrite  ~l2r:o ~occ_subterm:0 ~occ_sol:j c gl ]
END

TACTIC EXTEND _aacu4_    
| [ "aacu_rewrite" orient(o) constr(c) "subterm" integer(i)] ->
    [ fun gl -> aac_rewrite  ~l2r:o ~occ_subterm:i ~occ_sol:0 c gl ]
END

TACTIC EXTEND _aacu5_    
| [ "aacu_rewrite" orient(o) constr(c) ] ->
    [ fun gl -> aac_rewrite  ~l2r:o c gl ]
END

TACTIC EXTEND _aacu6_    
| [ "aacu_instances" orient(o) constr(c)] ->
    [ fun gl -> aac_rewrite  ~l2r:o ~show:true c gl ]
END
