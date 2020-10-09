(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(* A very basic way to interact with the envs, to choose a possible
   solution *)
open Pp
open Matcher
open Context.Rel.Declaration
open Names

type named_env = (Name.t * Terms.t) list
 


(** {pp_env} prints a substitution mapping names to terms, using the
provided printer *)
let pp_env pt  : named_env  -> Pp.t = fun env ->
  List.fold_left
    (fun acc (v,t) ->
       begin match v with
	 | Names.Name s -> str (Printf.sprintf "%s: " (Id.to_string s))
	 | Names.Anonymous -> str ("_")
       end
       ++ pt t ++ str "; " ++ acc
    ) 
    (str "")
    env
   
(** {pp_envm} prints a collection of possible environments, and number
them. This number must remain compatible with the parameters given to
{!aac_rewrite} *)
let pp_envm pt : named_env Search_monad.m -> Pp.t = fun m ->
  let _,s =
    Search_monad.fold
      (fun env (n,acc) ->
	 n+1,  h (str (Printf.sprintf "%i:\t[" n) ++pp_env pt env ++ str "]") ++ fnl () :: acc
      ) m (0,[])
  in
    List.fold_left (fun acc s -> s ++ acc) (str "") (s)
   
let trivial_substitution envm =
  match Search_monad.choose envm with
    | None -> true			(* assert false *)
    | Some l -> l=[]

(** {pp_all} prints a collection of possible contexts and related
possibles substitutions, giving a number to each. This number must
remain compatible with the parameters of {!aac_rewrite} *)
let pp_all pt : (int * Terms.t * named_env Search_monad.m) Search_monad.m -> Pp.t = fun m ->
  let _,s = Search_monad.fold
    (fun (size,context,envm) (n,acc) -> 
       let s = str (Printf.sprintf "occurrence %i: transitivity through " n) in
       let s = s ++ pt context ++ str "\n" in
       let s = if trivial_substitution envm then s else
	 s ++ str (Printf.sprintf "%i possible(s) substitution(s)" (Search_monad.count envm) )
	   ++ fnl () ++ pp_envm pt envm 
       in
	 n+1, s::acc
    ) m (0,[]) in
    List.fold_left (fun acc s -> s ++ str "\n" ++ acc) (str "") (s)

(** The main printing function. {!print} uses the debruijn_env the
rename the variables, and rebuilds raw Coq terms (for the context, and
the terms in the environment). In order to do so, it requires the
information gathered by the {!Theory.Trans} module.*)
let print rlt ir m (context : EConstr.rel_context) : unit Proofview.tactic =
  if Search_monad.count m = 0
  then
    (
      Tacticals.New.tclFAIL 0  (Pp.str "No subterm modulo AC")
    )
  else
    let _ = Feedback.msg_notice (Pp.str "All solutions:") in
    let m = Search_monad.(>>) m
      (fun (i,t,envm) ->
	let envm = Search_monad.(>>) envm ( fun env ->
	  let l = Matcher.Subst.to_list env in
	  let l = List.sort (fun (n,_) (n',_) -> Pervasives.compare n n') l in
	  let l =
	    List.map (fun (v,t) ->
	      get_name (Context.Rel.lookup v context), t
	    ) l
	  in
	  Search_monad.return l
	) 
	in
	Search_monad.return (i,t,envm)
      )
    in
    let m = Search_monad.sort (fun (x,_,_) (y,_,_) -> x -  y) m in
    let open Proofview.Notations in
    Proofview.tclENV >>= fun env ->
    Proofview.tclEVARMAP >>= fun sigma ->
    let _ = Feedback.msg_notice
      (pp_all
	 (fun t -> Printer.pr_letype_env env sigma (Theory.Trans.raw_constr_of_t ir rlt  context  t)) m
      )
    in
    Tacticals.New.tclIDTAC
     
