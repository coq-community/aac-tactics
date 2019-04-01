(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** aac_rewrite -- rewriting modulo A or AC*)

open Ltac_plugin

module Control =   struct
    let debug = false
    let printing = false
    let time = false
end

module Debug = Helper.Debug (Control)
open Debug

let time_tac msg tac =
  if Control.time then  Proofview.tclTIME (Some msg) tac else tac
  
let tclTac_or_exn (tac : 'a Proofview.tactic) exn msg : 'a Proofview.tactic =
  Proofview.tclORELSE tac
    (fun e ->
      let open Proofview.Notations in
      let open Proofview in
      tclEVARMAP >>= fun sigma ->
      Goal.enter_one (fun gl ->
          let env = Proofview.Goal.env gl in
          pr_constr env sigma "last goal" (Goal.concl gl);
          exn msg e)
    )


open EConstr
open Names

(** aac_lift : the ideal type beyond AAC_rewrite.v/Lift

    A base relation r, together with an equivalence relation, and the
    proof that the former lifts to the later. Howver, we have to
    ensure manually the invariant : r.carrier == e.carrier, and that
    lift connects the two things *)
type aac_lift =
    {
      r : Coq.Relation.t;
      e : Coq.Equivalence.t;
      lift : constr
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

let infer_lifting env sigma (rlt: Coq.Relation.t) : Evd.evar_map * aac_lift  =
  let x = rlt.Coq.Relation.carrier in
  let r = rlt.Coq.Relation.r in
  let (sigma, e) = Coq.evar_relation env sigma x in
  let lift_ty = mkApp (Coq.get_efresh Theory.Stubs.lift,[|x;r;e|]) in
  let sigma, lift = try Typeclasses.resolve_one_typeclass env sigma lift_ty
                    with Not_found -> CErrors.user_err (Pp.strbrk "Cannot infer a lifting")
  in
  let eq = (Evarutil.nf_evar sigma e) in
  let equiv = mkApp (Coq.get_efresh Theory.Stubs.lift_proj_equivalence,[| x;r;eq; lift |]) in
  sigma, {
      r = rlt;
      e = Coq.Equivalence.make x eq equiv;
      lift = lift;
    }
  

(** Builds a rewinfo, once and for all *)
let dispatch env sigma in_left (left,right,rlt) hypinfo : Evd.evar_map * rewinfo =
  let l2r = hypinfo.Coq.Rewrite.l2r in
  let sigma,lift = infer_lifting env sigma rlt in
  let eq = lift.e in
  sigma,{
      hypinfo = hypinfo;
      in_left = in_left;
      pattern = if l2r then hypinfo.Coq.Rewrite.left else hypinfo.Coq.Rewrite.right;
      subject = if in_left then left else right;
      morph_rlt = Coq.Equivalence.to_relation eq;
      eqt = eq;
      lifting = lift;
      rlt = rlt
    }


(** {1 Tactics} *)


(** Build the reifiers, the reified terms, and the evaluation fonction  *)
let handle eqt zero envs (t : Matcher.Terms.t) (t' : Matcher.Terms.t) : ('a * 'b * 'c * 'd) Proofview.tactic=
  let (x,r,_) = Coq.Equivalence.split eqt  in
  let open Proofview.Notations in
  Theory.Trans.mk_reifier (Coq.Equivalence.to_relation eqt) zero envs >>= fun (maps, reifier) ->
  (* fold through a term and reify *)
  let t = Theory.Trans.reif_constr_of_t reifier t in
  let t' = Theory.Trans.reif_constr_of_t reifier  t' in
  (* Some letins  *)
  let eval = (mkApp (Coq.get_efresh Theory.Stubs.eval, [|x;r; maps.Theory.Trans.env_sym; maps.Theory.Trans.env_bin; maps.Theory.Trans.env_units|])) in

  Coq.mk_letin "eval" eval >>= fun eval ->
  Coq.mk_letin "left" t >>= fun t ->
  Coq.mk_letin "right" t' >>= fun t' ->
  Proofview.tclUNIT (maps, eval, t,t')
                                   
(** [by_aac_reflexivity] is a sub-tactic that closes a sub-goal that
      is merely a proof of equality of two terms modulo AAC *)
let by_aac_reflexivity zero
      eqt envs (t : Matcher.Terms.t) (t' : Matcher.Terms.t) : unit Proofview.tactic =
  let open Proofview.Notations in
  handle eqt zero envs t t' >>= fun (maps,eval,t,t') ->
  let (x,r,e) = Coq.Equivalence.split eqt in
  let decision_thm = mkApp (Coq.get_efresh Theory.Stubs.decide_thm,
	               [|x;r;e;
	                 maps.Theory.Trans.env_sym;
	                 maps.Theory.Trans.env_bin;
	                 maps.Theory.Trans.env_units;
	                 t;t';
	               |])
  in
  (* This convert is required to deal with evars in a proper
     way *)
  let convert_to = mkApp (r, [| mkApp (eval,[| t |]); mkApp (eval, [|t'|])|])   in
  let convert = Tactics.convert_concl convert_to Constr.VMcast in
  let apply_tac = Tactics.apply decision_thm in
  let open Proofview in
  Coq.tclRETYPE decision_thm
  <*> Coq.tclRETYPE convert_to
  <*> convert
  <*> tclTac_or_exn apply_tac Coq.user_error (Pp.strbrk "unification failure")
  <*> tclTac_or_exn (time_tac "vm_norm" Tactics.normalise_in_concl) Coq.anomaly "vm_compute failure"
  <*> tclORELSE Tactics.reflexivity
	(fun _ -> Tacticals.New.tclFAIL 0 (Pp.str "Not an equality modulo A/AC"))
  


let by_aac_normalise zero lift ir t t' =
  let eqt = lift.e in
  let rlt = lift.r in
  let open Proofview.Notations in
  handle eqt zero ir t t' >>= fun (maps,eval,t,t') ->
  let (x,r,e) = Coq.Equivalence.split eqt in
  let normalise_thm = mkApp (Coq.get_efresh Theory.Stubs.lift_normalise_thm,
	                [|x;r;e;
	                  maps.Theory.Trans.env_sym;
	                  maps.Theory.Trans.env_bin;
	                  maps.Theory.Trans.env_units;
	                  rlt.Coq.Relation.r;
	                  lift.lift;
	                  t;t';
	                |])
  in
  (* This convert is required to deal with evars in a proper
     way *)
  let convert_to = mkApp (rlt.Coq.Relation.r, [| mkApp (eval,[| t |]); mkApp (eval, [|t'|])|])   in
  let convert = Tactics.convert_concl convert_to Constr.VMcast in
  let apply_tac = Tactics.apply normalise_thm in
  Tacticals.New.tclTHENLIST
    [ Coq.tclRETYPE normalise_thm; Coq.tclRETYPE convert_to;
       convert ;
       apply_tac;
     ]
  


(** A handler function, that reifies the goal, and infers the lifting *)
let aac_conclude env sigma (concl:types): ( Evd.evar_map * constr * aac_lift * Theory.Trans.ir * Matcher.Terms.t * Matcher.Terms.t) =
  let envs = Theory.Trans.empty_envs () in
  let left, right,r =
    match Coq.match_as_equation env sigma concl with
    | None -> Coq.user_error @@ Pp.strbrk "The goal is not an applied relation"
    | Some x -> x in
  try let sigma,lift = infer_lifting env sigma r in
      let eq = Coq.Equivalence.to_relation lift.e in
      let tleft,tright, sigma = Theory.Trans.t_of_constr env sigma eq envs (left,right) in
      let sigma, ir = Theory.Trans.ir_of_envs env sigma eq envs in
      let _ = pr_constr env sigma "concl" concl in
      (sigma,left,lift,ir,tleft,tright)
  with
  | Not_found -> Coq.user_error @@ Pp.strbrk "No lifting from the goal's relation to an equivalence"

open Tacexpr

let aac_normalise =
  let mp = MPfile (DirPath.make (List.map Id.of_string ["AAC"; "AAC_tactics"])) in
  let norm_tac = KerName.make mp (Label.make "internal_normalize") in
  let norm_tac = Locus.ArgArg (None, norm_tac) in
  let open Proofview.Notations in
  let open Proofview in
  Proofview.Goal.enter (fun goal -> 
      let ids = Tacmach.New.pf_ids_of_hyps goal in
      let env = Proofview.Goal.env goal in
      tclEVARMAP >>= fun sigma ->
      let concl = Proofview.Goal.concl goal in
      let sigma,left,lift,ir,tleft,tright = aac_conclude env sigma concl in
      Tacticals.New.tclTHENLIST
    [
      Unsafe.tclEVARS sigma;
      by_aac_normalise left lift ir tleft tright;
      Tacinterp.eval_tactic (TacArg (CAst.(make @@ TacCall (make (norm_tac, [])))));
      Tactics.keep ids
    ])

let aac_reflexivity : unit Proofview.tactic =
  let open Proofview.Notations in
  let open Proofview in
  tclEVARMAP >>= fun sigma ->
  Goal.enter (fun goal ->
      let env = Proofview.Goal.env goal in
      let concl = Goal.concl goal in
      let sigma,zero,lift,ir,t,t' = aac_conclude env sigma concl in
      let x,r = Coq.Relation.split (lift.r) in
      let r_reflexive = (Coq.Classes.mk_reflexive x r) in
      let sigma,reflexive = try Typeclasses.resolve_one_typeclass env sigma r_reflexive
                            with | Not_found -> Coq.user_error @@ Pp.strbrk "The goal's relation is not reflexive"
      in
      let lift_reflexivity =
        mkApp (Coq.get_efresh (Theory.Stubs.lift_reflexivity),
	       [| x; r; lift.e.Coq.Equivalence.eq; lift.lift; reflexive |])
      in
      Unsafe.tclEVARS sigma 
      <*> Tactics.apply lift_reflexivity
      <*> (let concl = Goal.concl goal in
           tclEVARMAP >>= fun sigma ->
           let _ = pr_constr env sigma "concl "concl in
           by_aac_reflexivity zero lift.e ir t t')
    )


(** A sub-tactic to lift the rewriting using Lift  *)
let lift_transitivity in_left (step:constr) preorder lifting (using_eq : Coq.Equivalence.t): unit Proofview.tactic =
  let open Proofview.Notations in
  let open Proofview in
  Proofview.Goal.enter (fun goal ->
      (* catch the equation and the two members*)
      let concl = Proofview.Goal.concl goal in
      let env = Proofview.Goal.env goal in
      tclEVARMAP >>= fun sigma ->
      let (left, right, _ ) = match  Coq.match_as_equation env sigma concl with
        | Some x -> x
        | None -> Coq.user_error @@ Pp.strbrk "The goal is not an equation"
      in
      let lift_transitivity =
        let thm =
	  if in_left
	  then
	    Theory.Stubs.lift_transitivity_left
	  else
	    Theory.Stubs.lift_transitivity_right
        in
        mkApp (Coq.get_efresh thm,
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
      Tacticals.New.tclTHENLIST
        [ Coq.tclRETYPE lift_transitivity;
          Tactics.apply lift_transitivity
        ]
    )

(** The core tactic for aac_rewrite. *)
let core_aac_rewrite ?abort
      rewinfo
      subst
      (by_aac_reflexivity : Matcher.Terms.t -> Matcher.Terms.t -> unit Proofview.tactic)
      (tr : constr) t left : unit Proofview.tactic =
  let open Proofview.Notations in
  Proofview.Goal.enter (fun goal ->
      let env = Proofview.Goal.env goal in
      Proofview.tclEVARMAP >>= fun sigma ->
      pr_constr env sigma "transitivity through" tr;
      let tran_tac =
        lift_transitivity rewinfo.in_left tr rewinfo.rlt rewinfo.lifting.lift rewinfo.eqt
      in
      let rew = Coq.Rewrite.rewrite ?abort rewinfo.hypinfo subst in
      Tacticals.New.tclTHENS
        (tclTac_or_exn (tran_tac) Coq.anomaly "Unable to make the transitivity step")
        (
	  if rewinfo.in_left
	  then [ by_aac_reflexivity left t ; rew ]
	  else [ by_aac_reflexivity t left ; rew ]
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
let aac_rewrite_wrap  ?abort ?(l2r=true) ?(show = false) ?(in_left=true) ?strict ?extra ~occ_subterm ~occ_sol rew : unit Proofview.tactic =
  let open Proofview.Notations in
  let open Proofview in
  Proofview.Goal.enter (fun goal ->
      let envs = Theory.Trans.empty_envs () in
      let (concl : types) = Proofview.Goal.concl goal in
      let env = Proofview.Goal.env goal in
      tclEVARMAP >>= fun sigma ->
      let (_,_,rlt) as concl =
        match Coq.match_as_equation env sigma concl with
        | None -> Coq.user_error @@ Pp.strbrk "The goal is not an applied relation"
        | Some (left, right, rlt) -> left,right,rlt
      in
      let check_type x =
        Tacmach.New.pf_conv_x goal x rlt.Coq.Relation.carrier
      in
      let hypinfo = Coq.Rewrite.get_hypinfo env sigma rew ~l2r ?check_type:(Some check_type) in      
      let sigma,rewinfo = dispatch env sigma in_left concl hypinfo in
      let sigma =
        match extra with
        | Some t -> Theory.Trans.add_symbol env sigma rewinfo.morph_rlt envs (EConstr.to_constr sigma t)
        | None -> sigma
      in
      let pattern, subject, sigma =
        Theory.Trans.t_of_constr env sigma rewinfo.morph_rlt envs
          (rewinfo.pattern , rewinfo.subject)
      in
      let sigma, ir = Theory.Trans.ir_of_envs env sigma rewinfo.morph_rlt envs in
      let open Proofview.Notations in
      Proofview.Unsafe.tclEVARS sigma
      <*> let units = Theory.Trans.ir_to_units ir in
          let m =  Matcher.subterm ?strict units pattern subject in
          (* We sort the monad in increasing size of contet *)
          let m = Search_monad.sort (fun (x,_,_) (y,_,_) -> x -  y) m in

          (if show
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
               (* I'm not sure whether this is the right env/sigma for printing tr_step_raw *)
               core_aac_rewrite ?abort rewinfo subst by_aac_reflexivity tr_step_raw tr_step subject
             with
             | NoSolutions ->
                Tacticals.New.tclFAIL 0
	          (Pp.str (if occ_subterm = None && occ_sol = None
		           then "No matching occurrence modulo AC found"
		           else "No such solution"))
          ))
  

let get k l = try Some (List.assoc k l) with Not_found -> None

let get_lhs l = try ignore (List.assoc "in_right" l); false with Not_found -> true

let aac_rewrite ~args =
  aac_rewrite_wrap ~occ_subterm:(get "at" args) ~occ_sol:(get "subst" args) ~in_left:(get_lhs args)



let rec add k x = function
  | [] -> [k,x]
  | k',_ as ky::q ->
      if k'=k then Coq.user_error @@ Pp.strbrk ("redondant argument ("^k^")")
      else ky::add k x q

let pr_aac_args _ _ _ l =
  List.fold_left
    (fun acc -> function
       | ("in_right" as s,_) -> Pp.(++) (Pp.str s) acc
       | (k,i) -> Pp.(++) (Pp.(++) (Pp.str k)  (Pp.int i)) acc
    ) (Pp.str "") l
