(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Interface with Coq *)

open Term
open EConstr
open Names
open Context.Rel.Declaration

(* The contrib name is used to locate errors when loading constrs *)
let contrib_name = "aac_tactics"

(* Getting constrs (primitive Coq terms) from existing Coq
   libraries. *)
let find_constant contrib dir s =
  Universes.constr_of_global (Coqlib.find_reference contrib dir s)

let init_constant_constr dir s = find_constant contrib_name dir s

let init_constant dir s = EConstr.of_constr (find_constant contrib_name dir s)

(* A clause specifying that the [let] should not try to fold anything
   in the goal *)
let nowhere =
  { Locus.onhyps = Some [];
    Locus.concl_occs = Locus.NoOccurrences
  }

let retype c gl =
  let sigma, _ = Tacmach.pf_apply Typing.type_of gl c in
    Refiner.tclEVARS sigma gl

let cps_mk_letin
    (name:string)
    (c: constr)
    (k : constr -> Proof_type.tactic)
: Proof_type.tactic =
  fun goal ->
    let name = (Id.of_string name) in
    let name =  Tactics.fresh_id Id.Set.empty name goal in
    let letin = (Proofview.V82.of_tactic (Tactics.letin_tac None  (Name name) c None nowhere)) in
      Tacticals.tclTHENLIST [retype c; letin; (k (mkVar name))] goal

(** {1 General functions}  *)

type goal_sigma =  Proof_type.goal Evd.sigma
let goal_update (goal : goal_sigma) evar_map : goal_sigma=
  let it = Tacmach.sig_it goal in
  Tacmach.re_sig it evar_map
     
let resolve_one_typeclass goal ty : constr*goal_sigma=
  let env = Tacmach.pf_env goal in
  let evar_map = Tacmach.project goal in
  let em,c = Typeclasses.resolve_one_typeclass env evar_map ty in
    c, (goal_update goal em)

let cps_resolve_one_typeclass ?error : types -> (constr  -> Proof_type.tactic) -> Proof_type.tactic = fun t k  goal  ->
  Tacmach.pf_apply
    (fun env em -> let em ,c =  
		  try Typeclasses.resolve_one_typeclass env em t
		  with Not_found ->
		    begin match error with
		      | None -> CErrors.anomaly (Pp.str "Cannot resolve a typeclass : please report")
		      | Some x -> CErrors.user_err x
		    end
		in
		Tacticals.tclTHENLIST [Refiner.tclEVARS em; k c] goal
    )	goal


let nf_evar goal c : constr=
  let evar_map = Tacmach.project goal in
  Evarutil.nf_evar evar_map c

  (* TODO: refactor following similar functions*)

let evar_unit (gl : goal_sigma) (x : constr) : constr * goal_sigma =
  let env = Tacmach.pf_env gl in
  let evar_map = Tacmach.project gl in
  let (em,x) = Evarutil.new_evar env evar_map x in
    x,(goal_update gl em)
     
let evar_binary (gl: goal_sigma) (x : constr) =
  let env = Tacmach.pf_env gl in
  let evar_map = Tacmach.project gl in
  let ty = mkArrow x (mkArrow x x) in
  let (em,x) = Evarutil.new_evar env evar_map ty in
    x,( goal_update gl em)

let evar_relation (gl: goal_sigma) (x: constr) =
  let env = Tacmach.pf_env gl in
  let evar_map = Tacmach.project gl in
  let ty = mkArrow x (mkArrow x (mkSort Sorts.prop)) in
  let (em,r) = Evarutil.new_evar env evar_map ty in
    r,( goal_update gl em)

let cps_evar_relation (x: constr) k = fun goal -> 
  Tacmach.pf_apply
    (fun env em ->
      let ty = mkArrow x (mkArrow x (mkSort Sorts.prop)) in
      let (em, r) = Evarutil.new_evar env em ty in
      Tacticals.tclTHENLIST [Refiner.tclEVARS em; k r] goal
    )	goal

let decomp_term sigma c = kind sigma (Termops.strip_outer_cast sigma c)
   
let lapp c v  = mkApp (Lazy.force c, v)

(** {2 Bindings with Coq' Standard Library}  *)
module Std = struct  		
(* Here we package the module to be able to use List, later *)

module Pair = struct
 
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "prod")
  let pair = lazy (init_constant path "pair")
  let of_pair t1 t2 (x,y) =
    mkApp (Lazy.force pair,  [| t1; t2; x ; y|] )
end

module Bool = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "bool")
  let ctrue = lazy (init_constant path "true")
  let cfalse = lazy (init_constant path "false")
  let of_bool  b =
    if b then Lazy.force ctrue else Lazy.force cfalse
end

module Comparison = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "comparison")
  let eq = lazy (init_constant path "Eq")
  let lt = lazy (init_constant path "Lt")
  let gt = lazy (init_constant path "Gt")
end

module Leibniz = struct
  let path = ["Coq"; "Init"; "Logic"]
  let eq_refl = lazy (init_constant path "eq_refl")
  let eq_refl ty x = lapp eq_refl [| ty;x|]
end

module Option = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "option")
  let some = lazy (init_constant path "Some")
  let none = lazy (init_constant path "None")
  let some t x = mkApp (Lazy.force some, [| t ; x|])
  let none t = mkApp (Lazy.force none, [| t |])
  let of_option t x = match x with
    | Some x -> some t x
    | None -> none t
end   

module Pos = struct
   
    let path = ["Coq" ; "Numbers"; "BinNums"]
    let typ = lazy (init_constant path "positive")
    let xI =      lazy (init_constant path "xI")
    let xO =      lazy (init_constant path "xO")
    let xH =      lazy (init_constant path "xH")

    (* A coq positive from an int *)
    let of_int n =
      let rec aux n =
	begin  match n with
	  | n when n < 1 -> assert false
	  | 1 -> Lazy.force xH
	  | n -> mkApp
	      (
		(if n mod 2 = 0
		 then Lazy.force xO
		 else Lazy.force xI
		),  [| aux (n/2)|]
	      )
	end
      in
	aux n
end
   
module Nat = struct
  let path = ["Coq" ; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "nat")
  let _S =      lazy (init_constant  path "S")
  let _O =      lazy (init_constant  path "O")
    (* A coq nat from an int *)
  let of_int n =
    let rec aux n =
      begin  match n with
	| n when n < 0 -> assert false
	| 0 -> Lazy.force _O
	| n -> mkApp
	    (
	      (Lazy.force _S
	      ),  [| aux (n-1)|]
	    )
      end
    in
      aux n
end
   
(** Lists from the standard library*)
module List = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "list")
  let nil = lazy (init_constant path "nil")
  let cons = lazy (init_constant path "cons")
  let cons ty h t =
    mkApp (Lazy.force cons, [|  ty; h ; t |])
  let nil ty =
    (mkApp (Lazy.force nil, [|  ty |]))
  let rec of_list ty = function
    | [] -> nil ty
    | t::q -> cons ty t (of_list  ty q)
  let type_of_list ty =
    mkApp (Lazy.force typ, [|ty|])
end
   
(** Morphisms *)
module Classes =
struct
  let classes_path = ["Coq";"Classes"; ]
  let morphism = lazy (init_constant (classes_path@["Morphisms"]) "Proper")
  let equivalence = lazy (init_constant (classes_path@ ["RelationClasses"]) "Equivalence")
  let reflexive = lazy (init_constant (classes_path@ ["RelationClasses"]) "Reflexive")
  let transitive = lazy (init_constant (classes_path@ ["RelationClasses"]) "Transitive")

  (** build the type [Equivalence ty rel]  *)
  let mk_equivalence ty rel =
    mkApp (Lazy.force equivalence, [| ty; rel|])


  (** build the type [Reflexive ty rel]  *)
  let mk_reflexive ty rel =
    mkApp (Lazy.force reflexive, [| ty; rel|])

  (** build the type [Proper rel t] *)
  let mk_morphism ty rel t =
    mkApp (Lazy.force morphism, [| ty; rel; t|])

  (** build the type [Transitive ty rel]  *)
  let mk_transitive ty rel =
    mkApp (Lazy.force transitive, [| ty; rel|])
end

module Relation = struct
  type t =
      {
	carrier : constr;
	r : constr;
      }
	
  let make ty r = {carrier = ty; r = r }
  let split t = t.carrier, t.r
end
   
module Transitive = struct
  type t =
      {
	carrier : constr;
	leq : constr;
	transitive : constr;
      }
  let make ty leq transitive = {carrier = ty; leq = leq; transitive = transitive}
  let infer goal ty leq  =
    let ask = Classes.mk_transitive ty leq in
    let transitive , goal = resolve_one_typeclass goal ask in
      make ty leq transitive, goal
  let from_relation goal rlt =
    infer goal (rlt.Relation.carrier) (rlt.Relation.r)
  let cps_from_relation rlt k =
    let ty =rlt.Relation.carrier in
    let r = rlt.Relation.r in
    let ask = Classes.mk_transitive  ty r in
    cps_resolve_one_typeclass ask
      (fun trans -> k (make ty r trans) )
  let to_relation t =
    {Relation.carrier = t.carrier; Relation.r = t.leq}

end
	
module Equivalence = struct
  type t =
      {
	carrier : constr;
	eq : constr;
	equivalence : constr;	
      }
  let make ty eq equivalence = {carrier = ty; eq = eq; equivalence = equivalence}
  let infer goal ty eq  =
    let ask = Classes.mk_equivalence ty eq in
    let equivalence , goal = resolve_one_typeclass goal ask in
      make ty eq equivalence, goal 	 
  let from_relation goal rlt =
    infer goal (rlt.Relation.carrier) (rlt.Relation.r)
  let cps_from_relation rlt k =
    let ty =rlt.Relation.carrier in
    let r = rlt.Relation.r in
    let ask = Classes.mk_equivalence  ty r in
    cps_resolve_one_typeclass ask (fun equiv -> k (make ty r equiv) )
  let to_relation t =
    {Relation.carrier = t.carrier; Relation.r = t.eq}
  let split t =
    t.carrier, t.eq, t.equivalence
end
end
(**[ match_as_equation goal eqt] see [eqt] as an equation. An
   optionnal rel-context can be provided to ensure that the term
   remains typable*)
let match_as_equation ?(context = Context.Rel.empty) goal equation : (constr*constr* Std.Relation.t) option  =
  let env = Tacmach.pf_env goal in
  let env = EConstr.push_rel_context context env in
  let evar_map = Tacmach.project goal in
  begin
    match decomp_term evar_map equation with
      | App(c,ca) when Array.length ca >= 2 ->
	let n = Array.length ca  in
	let left  =  ca.(n-2) in
	let right =  ca.(n-1) in
	let r = (mkApp (c, Array.sub ca 0 (n - 2))) in
	let carrier =  Typing.unsafe_type_of env evar_map left in
	let rlt =Std.Relation.make carrier r
	in
	Some (left, right, rlt )
      | _ -> None
  end


(** {1 Tacticals}  *)

let tclTIME msg tac = fun gl ->
  let u = Sys.time () in
  let r = tac gl in
  let _ = Feedback.msg_notice (Pp.str (Printf.sprintf "%s:%fs" msg (Sys.time ()-.  u))) in
    r

let tclDEBUG msg tac = fun gl ->
  let _ = Feedback.msg_debug (Pp.str msg) in
    tac gl

let tclPRINT tac = fun gl ->
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let _ = Feedback.msg_notice (Printer.pr_econstr_env env sigma (Tacmach.pf_concl gl)) in
    tac gl


(** {1 Error related mechanisms}  *)
(* functions to handle the failures of our tactic. Some should be
   reported [anomaly], some are on behalf of the user [user_error]*)
let anomaly msg =
  CErrors.anomaly ~label:"[aac_tactics]" (Pp.str msg)

let user_error msg =
  CErrors.user_err Pp.(str "[aac_tactics] " ++ msg)

let warning msg =
  Feedback.msg_warning (Pp.str ("[aac_tactics]" ^ msg))

     
(** {1 Rewriting tactics used in aac_rewrite}  *)
module Rewrite = struct
(** Some informations about the hypothesis, with an (informal)
    invariant:
    - [typeof hyp = hyptype]
    - [hyptype = forall context, body]
    - [body = rel left right]
 
*)

type hypinfo =
    {
      hyp : constr;		  (** the actual constr corresponding to the hypothese  *)
      hyptype : constr; 		(** the type of the hypothesis *)
      context : EConstr.rel_context;       	(** the quantifications of the hypothese *)
      body : constr; 		(** the body of the type of the hypothesis*)
      rel : Std.Relation.t; 		(** the relation  *)
      left : constr;		(** left hand side *)
      right : constr;		(** right hand side  *)
      l2r : bool; 			(** rewriting from left to right  *)
    }

let get_hypinfo c ~l2r ?check_type  (k : hypinfo -> Proof_type.tactic) :    Proof_type.tactic = fun goal ->
  let ctype =  Tacmach.pf_unsafe_type_of goal c in 
  let evar_map = Tacmach.project goal in
  let (rel_context, body_type) = decompose_prod_assum evar_map ctype in
  let rec check f e =
    match decomp_term evar_map e with
      | Term.Rel i -> f (get_type (Context.Rel.lookup i rel_context))
      | _ -> fold evar_map (fun acc x -> acc && check f x) true e
  in
  begin match check_type with
    | None -> ()
    | Some f ->
	if not (check f body_type)
	then user_error @@ Pp.strbrk "Unable to deal with higher-order or heterogeneous patterns";
  end;
  begin
    match match_as_equation ~context:rel_context goal body_type with
      | None -> 
	user_error @@ Pp.strbrk "The hypothesis is not an applied relation"
      |  Some (hleft,hright,hrlt) ->
	k {
    	  hyp = c;
    	  hyptype = ctype;
	  body =  body_type;
	  l2r = l2r;
    	  context = rel_context;
    	  rel = hrlt ;
    	  left =hleft;
    	  right = hright;
	}
	goal
  end
   

(* The problem : Given a term to rewrite of type [H :forall xn ... x1,
   t], we have to instanciate the subset of [xi] of type
   [carrier]. [subst : (int * constr)] is the mapping the debruijn
   indices in [t] to the [constrs]. We need to handle the rest of the
   indexes. Two ways :

   - either using fresh evars and rewriting [H tn ?1 tn-2 ?2 ]
   - either building a term like [fun 1 2 => H tn 1 tn-2 2]

   Both these terms have the same type.
*)


(* Fresh evars for everyone (should be the good way to do this
   recompose in Coq v8.4) *)
let recompose_prod 
    (context : rel_context)
    (subst : (int * constr) list)
    env
    em
    : Evd.evar_map * constr list =
  (* the last index of rel relevant for the rewriting *)
  let min_n = List.fold_left
    (fun acc (x,_) -> min acc x)
    (List.length context) subst in 
  let rec aux context acc em n =
    let _ = Printf.printf "%i\n%!" n in
    match context with
      | [] ->
	env, em, acc
      | t::q ->
	let env, em, acc = aux q acc em (n+1) in
	if n >= min_n
	then
	  let em,x =
	    try em, List.assoc n subst
	    with | Not_found ->
	      let (em, r) = Evarutil.new_evar env em (Vars.substl acc (get_type t)) in
              (em, r)
	  in
	  (EConstr.push_rel t env), em,x::acc
	else
	  env,em,acc
  in
  let _,em,acc = aux context [] em 1 in
  em, acc

(* no fresh evars : instead, use a lambda abstraction around an
   application to handle non-instantiated variables. *)
   
let recompose_prod'
    (context : rel_context)
    (subst : (int *constr) list)
    c
    =
  let rec popn pop n l =
    if n <= 0 then l
    else match l with
      | [] -> []
      | t::q -> pop t :: (popn pop (n-1) q)
  in
  let pop_rel_decl = map_type Termops.pop in
  let rec aux sign n next app ctxt =
    match sign with
      | [] -> List.rev app, List.rev ctxt
      | decl::sign ->
	try let term =  (List.assoc n subst) in
	    aux sign (n+1) next (term::app) (None :: ctxt)
	with
	  | Not_found ->
	    let term = mkRel next in
	    aux sign (n+1) (next+1) (term::app) (Some decl :: ctxt)
  in
  let app,ctxt = aux context 1 1 [] [] in
  (* substitutes in the context *)
  let rec update ctxt app =
    match ctxt,app with
      | [],_ -> []
      | _,[] -> []
      | None :: sign, _ :: app ->
	None ::	update sign (List.map (Termops.pop) app)
      | Some decl :: sign, _ :: app ->
	Some (Vars.substl_decl app decl)::update sign (List.map (Termops.pop) app) 
  in
  let ctxt = update ctxt app in
  (* updates the rel accordingly, taking some care not to go to far
     beyond: it is important not to lift indexes homogeneously, we
     have to update *)
  let rec update ctxt res n =
    match ctxt with
      | [] -> List.rev res
      | None :: sign ->
  	(update (sign) (popn pop_rel_decl n res) 0)
      | Some decl :: sign ->
  	update sign (decl :: res) (n+1)
  in
  let ctxt = update ctxt [] 0 in
  let c = applist (c,List.rev app) in
  let c = it_mkLambda_or_LetIn c ctxt in
  c

(* Version de Matthieu
let subst_rel_context k cstr ctx =
  let (_, ctx') =
    List.fold_left (fun (k, ctx') (id, b, t) -> (succ k, (id, Option.map
      (Term.substnl [cstr] k) b, Term.substnl [cstr] k t) :: ctx')) (k, [])
      ctx in List.rev ctx'

let recompose_prod' context subst c =
  let len = List.length context in
  let rec aux sign n next app ctxt =
    match sign with
    | [] -> List.rev app, List.rev ctxt
    | decl::sign ->
	try let term = (List.assoc n subst) in
	  aux (subst_rel_context 0 term sign) (pred n) (succ next)
	    (term::List.map (Term.lift (-1)) app) ctxt
	with Not_found ->
	  let term = Term.mkRel (len - next) in
	    aux sign (pred n) (succ next) (term::app) (decl :: ctxt)
  in
  let app,ctxt = aux (List.rev context) len 0 [] [] in
    Term.it_mkLambda_or_LetIn (Term.applistc c(app)) (List.rev ctxt)
*)

let build
    (h : hypinfo)
    (subst : (int *constr) list)
    (k :constr -> Proof_type.tactic)
    : Proof_type.tactic = fun goal ->
      let c = recompose_prod' h.context subst h.hyp in
      Tacticals.tclTHENLIST [k c] goal

let build_with_evar
    (h : hypinfo)
    (subst : (int *constr) list)
    (k :constr -> Proof_type.tactic)
    : Proof_type.tactic
    = fun goal ->
      Tacmach.pf_apply
	(fun env em ->
	  let evar_map,  acc = recompose_prod h.context subst env em in
	  let c = applist (h.hyp,List.rev acc) in
	  Tacticals.tclTHENLIST [Refiner.tclEVARS evar_map; k c] goal
	) goal


let rewrite ?(abort=false)hypinfo subst k =
  build hypinfo subst
    (fun rew ->
      let tac =
	if not abort then
          Proofview.V82.of_tactic begin
	  Equality.general_rewrite_bindings
	    hypinfo.l2r
	    Locus.AllOccurrences
	    true (* tell if existing evars must be frozen for instantiation *)
	    false
	    (rew,Misctypes.NoBindings)
	    true
          end
	else
	  Tacticals.tclIDTAC
      in k tac
    )


end

include Std
