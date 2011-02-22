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
open AAC_matcher
type named_env = (Names.name * Terms.t) list
 


(** {pp_env} prints a substitution mapping names to terms, using the
provided printer *)
let pp_env pt  : named_env  -> Pp.std_ppcmds = fun env ->
  List.fold_left
    (fun acc (v,t) ->
       begin match v with
	 | Names.Name s -> str (Printf.sprintf "%s: " (Names.string_of_id s))
	 | Names.Anonymous -> str ("_")
       end
       ++ pt t ++ str "; " ++ acc
    ) 
    (str "")
    env
   
(** {pp_envm} prints a collection of possible environments, and number
them. This number must remain compatible with the parameters given to
{!aac_rewrite} *)
let pp_envm pt : named_env AAC_search_monad.m -> Pp.std_ppcmds = fun m ->
  let _,s =
    AAC_search_monad.fold
      (fun env (n,acc) ->
	 n+1,  h 0 (str (Printf.sprintf "%i:\t[" n) ++pp_env pt env ++ str "]") ++ fnl () :: acc
      ) m (0,[])
  in
    List.fold_left (fun acc s -> s ++ acc) (str "") (s)
   
let trivial_substitution envm =
  match AAC_search_monad.choose envm with
    | None -> true			(* assert false *)
    | Some l -> l=[]

(** {pp_all} prints a collection of possible contexts and related
possibles substitutions, giving a number to each. This number must
remain compatible with the parameters of {!aac_rewrite} *)
let pp_all pt : (int * Terms.t * named_env AAC_search_monad.m) AAC_search_monad.m -> Pp.std_ppcmds = fun m ->
  let _,s = AAC_search_monad.fold
    (fun (size,context,envm) (n,acc) -> 
       let s = str (Printf.sprintf "occurence %i: transitivity through " n) in
       let s = s ++ pt context ++ str "\n" in
       let s = if trivial_substitution envm then s else
	 s ++ str (Printf.sprintf "%i possible(s) substitution(s)" (AAC_search_monad.count envm) )
	   ++ fnl () ++ pp_envm pt envm 
       in
	 n+1, s::acc
    ) m (0,[]) in
    List.fold_left (fun acc s -> s ++ str "\n" ++ acc) (str "") (s)

(** The main printing function. {!print} uses the debruijn_env the
rename the variables, and rebuilds raw Coq terms (for the context, and
the terms in the environment). In order to do so, it requires the
information gathered by the {!AAC_theory.Trans} module.*)
let print rlt ir m (context : Term.rel_context) goal =
  if AAC_search_monad.count m = 0
  then
    (
      Tacticals.tclFAIL 0  (Pp.str "No subterm modulo AC")  goal
    )
  else
    let _ = Pp.msgnl (Pp.str "All solutions:") in
    let m = AAC_search_monad.(>>) m
      (fun (i,t,envm) ->
	let envm = AAC_search_monad.(>>) envm ( fun env ->
	  let l = AAC_matcher.Subst.to_list env in
	  let l = List.sort (fun (n,_) (n',_) -> Pervasives.compare n n') l in
	  let l =
	    List.map (fun (v,t) ->
	      let (name,body,types) = Term.lookup_rel  v context in
	      (name,t)
	    ) l
	  in
	  AAC_search_monad.return l
	) 
	in
	AAC_search_monad.return (i,t,envm)
      )
    in
    let m = AAC_search_monad.sort (fun (x,_,_) (y,_,_) -> x -  y) m in
    let _ = Pp.msgnl
      (pp_all
	 (fun t -> Printer.pr_constr (AAC_theory.Trans.raw_constr_of_t ir rlt  context  t) ) m
      )
    in
    Tacticals.tclIDTAC goal
     
