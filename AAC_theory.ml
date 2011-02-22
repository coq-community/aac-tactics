(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Constr from the theory of this particular development

    The inner-working of this module is highly correlated with the
    particular structure of {b AAC.v}, therefore, it should
    be of little interest to most readers.
*)
open Term

module Control = struct
  let printing = true
  let debug = false
  let time = false
end

module Debug = AAC_helper.Debug (Control)
open Debug

(** {1 HMap :     Specialized Hashtables based on constr} *)


module Hashed_constr =
struct
  type t = constr
  let equal = (=)
  let hash = Hashtbl.hash
end

  (* TODO module HMap = Hashtbl, du coup ? *)
module HMap = Hashtbl.Make(Hashed_constr)

let ac_theory_path = ["AAC_tactics"; "AAC"]

module Stubs = struct
  let path = ac_theory_path@["Internal"]

  (** The constants from the inductive type *)
  let _Tty = lazy (AAC_coq.init_constant path "T")
  let vTty = lazy (AAC_coq.init_constant path "vT")
 
  let rsum = lazy (AAC_coq.init_constant path "sum")
  let rprd = lazy (AAC_coq.init_constant path "prd")
  let rsym = lazy (AAC_coq.init_constant path "sym")
  let runit = lazy (AAC_coq.init_constant path "unit")

  let vnil = lazy (AAC_coq.init_constant path "vnil")
  let vcons = lazy (AAC_coq.init_constant path "vcons")
  let eval = lazy (AAC_coq.init_constant path "eval")


  let decide_thm = lazy (AAC_coq.init_constant path "decide")
  let lift_normalise_thm = lazy (AAC_coq.init_constant path "lift_normalise")

  let lift = 
    lazy (AAC_coq.init_constant ac_theory_path "AAC_lift")
  let lift_proj_equivalence= 
    lazy (AAC_coq.init_constant ac_theory_path "aac_lift_equivalence")
  let lift_transitivity_left =
    lazy(AAC_coq.init_constant ac_theory_path "lift_transitivity_left")
  let lift_transitivity_right =
    lazy(AAC_coq.init_constant ac_theory_path "lift_transitivity_right")
  let lift_reflexivity =
    lazy(AAC_coq.init_constant ac_theory_path "lift_reflexivity")
end

module Classes = struct 
  module Associative = struct
    let path = ac_theory_path
    let typ = lazy (AAC_coq.init_constant path "Associative")
    let ty (rlt : AAC_coq.Relation.t) (value : Term.constr) =
      mkApp (Lazy.force typ, [| rlt.AAC_coq.Relation.carrier;
				rlt.AAC_coq.Relation.r;
				value
			     |] )
    let infer goal  rlt value =
      let ty = ty rlt value in
	AAC_coq.resolve_one_typeclass  goal ty
  end
   
  module Commutative = struct
    let path = ac_theory_path
    let typ = lazy (AAC_coq.init_constant path "Commutative")
    let ty (rlt : AAC_coq.Relation.t) (value : Term.constr) =
      mkApp (Lazy.force typ, [| rlt.AAC_coq.Relation.carrier;
				rlt.AAC_coq.Relation.r;
				value
			     |] )
	
  end
   
  module Proper = struct
    let path = ac_theory_path @ ["Internal";"Sym"]
    let typeof = lazy (AAC_coq.init_constant path "type_of")
    let relof = lazy (AAC_coq.init_constant path "rel_of")
    let mk_typeof :  AAC_coq.Relation.t -> int -> constr = fun rlt n ->
      let x = rlt.AAC_coq.Relation.carrier in
	mkApp (Lazy.force typeof, [| x ; AAC_coq.Nat.of_int n |])
    let mk_relof :  AAC_coq.Relation.t -> int -> constr = fun rlt n ->
      let (x,r) = AAC_coq.Relation.split rlt in      
      mkApp (Lazy.force relof, [| x;r ; AAC_coq.Nat.of_int n |])

    let ty rlt op ar  =
      let typeof = mk_typeof rlt ar in
      let relof = mk_relof rlt ar in
	AAC_coq.Classes.mk_morphism  typeof relof op
    let infer goal rlt op ar =
      let ty = ty rlt op ar in
	AAC_coq.resolve_one_typeclass goal ty
  end
    
  module Unit = struct
    let path = ac_theory_path
    let typ = lazy (AAC_coq.init_constant path "Unit")
    let ty (rlt : AAC_coq.Relation.t) (value : Term.constr) (unit : Term.constr)=
      mkApp (Lazy.force typ, [| rlt.AAC_coq.Relation.carrier;
 				rlt.AAC_coq.Relation.r;
 				value;
 				unit
 			     |] )
  end

end

(* Non empty lists *)
module NEList = struct
  let path = ac_theory_path @ ["Internal"]
  let typ = lazy (AAC_coq.init_constant path "list")
  let nil = lazy (AAC_coq.init_constant path "nil")
  let cons = lazy (AAC_coq.init_constant path "cons")
  let cons ty h t =
    mkApp (Lazy.force cons, [|  ty; h ; t |])
  let nil ty x =
    (mkApp (Lazy.force nil, [|  ty ; x|]))
  let rec of_list ty = function
    | [] -> invalid_arg "NELIST"
    | [x] -> nil ty x
    | t::q -> cons ty t (of_list  ty q)

  let type_of_list ty =
    mkApp (Lazy.force typ, [|ty|])
end

(** a [mset] is a ('a * pos) list *)
let mk_mset ty (l : (constr * int) list) =
  let pos = Lazy.force AAC_coq.Pos.typ in
  let pair (x : constr) (ar : int) =
    AAC_coq.Pair.of_pair ty pos (x, AAC_coq.Pos.of_int ar)
  in
  let pair_ty = AAC_coq.lapp AAC_coq.Pair.typ [| ty ; pos|] in
  let rec aux = function
    | [ ] -> assert false
    | [x,ar] -> NEList.nil pair_ty (pair x ar)
    | (t,ar)::q -> NEList.cons pair_ty (pair t ar) (aux q)  
  in
    aux l

module Sigma = struct
  let sigma = lazy (AAC_coq.init_constant ac_theory_path "sigma")
  let sigma_empty = lazy (AAC_coq.init_constant ac_theory_path "sigma_empty")
  let sigma_add = lazy (AAC_coq.init_constant ac_theory_path "sigma_add")
  let sigma_get = lazy (AAC_coq.init_constant ac_theory_path "sigma_get")
   
  let add ty n x map =
    mkApp (Lazy.force sigma_add,[|ty; n; x ;  map|])
  let empty ty =
    mkApp (Lazy.force sigma_empty,[|ty |])
  let typ ty =
    mkApp (Lazy.force sigma, [|ty|])

  let to_fun ty null map =
    mkApp (Lazy.force sigma_get, [|ty;null;map|])

  let of_list ty null l =
    match l with
      | (_,t)::q ->
	  let map =
	    List.fold_left
	      (fun acc (i,t) ->
		 assert (i > 0);
		 add ty (AAC_coq.Pos.of_int i) ( t) acc)
	      (empty ty)
	      q
	  in to_fun ty (t) map
      | [] -> debug "of_list empty" ; to_fun ty (null) (empty ty)
 
   
end


module Sym = struct
  type pack = {ar: Term.constr; value: Term.constr ; morph: Term.constr}
  let path = ac_theory_path @ ["Internal";"Sym"]
  let typ = lazy (AAC_coq.init_constant path "pack")
  let mkPack = lazy (AAC_coq.init_constant path "mkPack")
  let value = lazy (AAC_coq.init_constant path "value")
  let null = lazy (AAC_coq.init_constant path "null")
  let mk_pack (rlt: AAC_coq.Relation.t) s =
    let (x,r) = AAC_coq.Relation.split rlt in
      mkApp (Lazy.force mkPack, [|x;r; s.ar;s.value;s.morph|])
  let null  rlt =
    let x = rlt.AAC_coq.Relation.carrier in
    let r = rlt.AAC_coq.Relation.r in
      mkApp (Lazy.force null, [| x;r;|])

  let mk_ty : AAC_coq.Relation.t -> constr = fun rlt ->
    let (x,r) = AAC_coq.Relation.split rlt in
      mkApp (Lazy.force typ, [| x; r|] )
end

module Bin =struct
  type pack = {value : Term.constr;
	       compat : Term.constr;
	       assoc : Term.constr;
	       comm : Term.constr option;
	      }

  let path = ac_theory_path @ ["Internal";"Bin"]
  let typ = lazy (AAC_coq.init_constant path "pack")
  let mkPack = lazy (AAC_coq.init_constant path "mk_pack")
   
  let mk_pack: AAC_coq.Relation.t -> pack -> Term.constr = fun (rlt) s ->
    let (x,r) = AAC_coq.Relation.split rlt in
    let comm_ty = Classes.Commutative.ty rlt s.value in
    mkApp (Lazy.force mkPack , [| x ; r;
				  s.value;
				  s.compat ;
				  s.assoc;
				  AAC_coq.Option.of_option comm_ty s.comm
			       |])
  let mk_ty : AAC_coq.Relation.t -> constr = fun rlt ->
   let (x,r) = AAC_coq.Relation.split rlt in
      mkApp (Lazy.force typ, [| x; r|] )
end
 
module Unit = struct
  let path = ac_theory_path @ ["Internal"]
  let unit_of_ty = lazy (AAC_coq.init_constant path "unit_of")
  let unit_pack_ty = lazy (AAC_coq.init_constant path "unit_pack")
  let mk_unit_of = lazy (AAC_coq.init_constant path "mk_unit_for")
  let mk_unit_pack = lazy (AAC_coq.init_constant path "mk_unit_pack")
 
  type unit_of =
      {
	uf_u : Term.constr; 		(* u *)
	uf_idx : Term.constr;
	uf_desc : Term.constr; (* Unit R (e_bin uf_idx) u *)
      }
	
  type pack = {
    u_value : Term.constr;	(* X *)
    u_desc : (unit_of) list (* unit_of u_value *)
  }

  let ty_unit_of rlt  e_bin u =
    let (x,r) = AAC_coq.Relation.split rlt in
      mkApp ( Lazy.force unit_of_ty, [| x; r; e_bin; u |])
	
  let ty_unit_pack rlt e_bin =
    let (x,r) = AAC_coq.Relation.split rlt in
      mkApp (Lazy.force unit_pack_ty, [| x; r; e_bin |])
   
  let mk_unit_of rlt e_bin u unit_of =
    let (x,r) = AAC_coq.Relation.split rlt in  
    mkApp (Lazy.force mk_unit_of , [| x;
				      r;
				      e_bin ;
				      u;
				      unit_of.uf_idx;
				      unit_of.uf_desc
				   |])
   
  let mk_pack rlt e_bin pack : Term.constr =
    let (x,r) = AAC_coq.Relation.split rlt in
    let ty = ty_unit_of rlt e_bin pack.u_value in
    let mk_unit_of = mk_unit_of rlt e_bin pack.u_value in
    let u_desc =AAC_coq.List.of_list ( ty ) (List.map mk_unit_of pack.u_desc) in
      mkApp (Lazy.force mk_unit_pack, [|x;r;
			       e_bin ;
			       pack.u_value;
			       u_desc
			     |])

  let default x : pack =
    { u_value = x;
      u_desc = []
    }

end

let anomaly msg =
  Util.anomaly ("aac_tactics: " ^ msg)

let user_error msg =
  Util.error ("aac_tactics: " ^ msg)

module Trans = struct
 
  (** {1 From Coq to Abstract Syntax Trees (AST)}
     
      This module provides facilities to interpret a Coq term with
      arbitrary operators as an abstract syntax tree. Considering an
      application, we try to infer instances of our classes.
     
      We consider that [A] operators are coarser than [AC] operators,
      which in turn are coarser than raw morphisms. That means that
      [List.append], of type [(A : Type) -> list A -> list A -> list
      A] can be understood as an [A] operator.
     
      During this reification, we gather some informations that will
      be used to rebuild Coq terms from AST ( type {!envs})

      We use a main hash-table from [constr] to [pack], in order to
      discriminate the various constructors. All these are mixed in
      order to improve on the number of comparisons in the tables *)

  (* 'a * (unit, op_unit) option *)
  type 'a with_unit = 'a * (Unit.unit_of) option
  type pack =
    (*  used to infer the AC/A structure in the first pass {!Gather} *)
    | Bin of Bin.pack with_unit
    (* will only be used in the second pass : {!Parse}*)
    | Sym of Sym.pack 		
    | Unit of constr  			(* to avoid confusion in bloom *)

  (** discr is a map from {!Term.constr} to {!pack}.
     
      [None] means that it is not possible to instantiate this partial
      application to an interesting class.

      [Some x] means that we found something in the past. This means
      in particular that a single [constr] cannot be two things at the
      same time.
     
      The field [bloom] allows to give a unique number to each class we
      found.  *)	
  type envs =
      {
	discr : (pack option) HMap.t ;
	bloom : (pack, int ) Hashtbl.t;
	bloom_back  : (int, pack ) Hashtbl.t;
	bloom_next : int ref;
      }

  let empty_envs () =
    {
      discr = HMap.create 17;
      bloom  =  Hashtbl.create 17;
      bloom_back  =  Hashtbl.create 17; 
      bloom_next = ref 1;
    }

          

  let add_bloom envs pack =
    if Hashtbl.mem envs.bloom pack
    then ()
    else
      let x = ! (envs.bloom_next) in
	Hashtbl.add envs.bloom pack x;
	Hashtbl.add envs.bloom_back x pack;
	incr (envs.bloom_next)

  let find_bloom envs pack =
    try Hashtbl.find envs.bloom pack
    with Not_found -> assert false

  	    (********************************************)
	    (* (\* Gather the occuring AC/A symbols *\) *)
	    (********************************************)

  (** This modules exhibit a function that memoize in the environment
      all the AC/A operators as well as the morphism that occur. This
      staging process allows us to prefer AC/A operators over raw
      morphisms. Moreover, for each AC/A operators, we need to try to
      infer units. Otherwise, we do not have [x * y * x <= a * a] since 1
      does not occur.
     
      But, do  we also need to check whether constants are
      units. Otherwise, we do not have the ability to rewrite [0 = a +
      a] in [a = ...]*)
  module Gather : sig
    val gather : AAC_coq.goal_sigma -> AAC_coq.Relation.t -> envs -> Term.constr -> AAC_coq.goal_sigma
  end
    = struct   

      let memoize  envs t pack : unit =
	begin
	  HMap.add envs.discr t (Some pack);
	  add_bloom envs pack;
	  match pack with
	    | Bin (_, None) | Sym _ -> ()
	    | Bin (_, Some (unit_of)) ->
	      let unit = unit_of.Unit.uf_u in
	      HMap.add envs.discr unit (Some (Unit unit));
	      add_bloom envs (Unit unit);
	    | Unit _ -> assert false
	end


      let get_unit (rlt : AAC_coq.Relation.t) op goal :
	  (AAC_coq.goal_sigma * constr * constr ) option=
	let x = (rlt.AAC_coq.Relation.carrier)  in
	let unit, goal = AAC_coq.evar_unit goal x  in
	let ty =Classes.Unit.ty rlt  op  unit in
	let result =
	  try
	    let t,goal = AAC_coq.resolve_one_typeclass goal ty in
	    Some (goal,t,unit)
	  with Not_found -> None
	in
	match result with
	  | None -> None
	  | Some (goal,s,unit) ->
	    let unit = AAC_coq.nf_evar goal unit  in
	    Some (goal, unit, s)
		


      (** gives back the class and the operator *)
      let is_bin  (rlt: AAC_coq.Relation.t) (op: constr) ( goal: AAC_coq.goal_sigma)
	  : (AAC_coq.goal_sigma * Bin.pack) option =
	let assoc_ty = Classes.Associative.ty rlt op in
	let comm_ty = Classes.Commutative.ty rlt op in
	let proper_ty  = Classes.Proper.ty rlt op 2 in
	try
	  let proper , goal = AAC_coq.resolve_one_typeclass goal proper_ty in
	  let assoc, goal = AAC_coq.resolve_one_typeclass goal assoc_ty in
	  let comm , goal =
	    try
	      let comm, goal = AAC_coq.resolve_one_typeclass goal comm_ty in
	      Some comm, goal
	    with Not_found ->
	      None, goal
	  in
	  let bin =
	    {Bin.value = op;
	     Bin.compat = proper;
	     Bin.assoc = assoc;
	     Bin.comm = comm }
	  in
	  Some (goal,bin)
	with |Not_found -> None
	 
      let is_bin (rlt : AAC_coq.Relation.t) (op : constr) (goal : AAC_coq.goal_sigma)=
	match is_bin rlt op goal with
	  | None -> None
	  | Some (goal, bin_pack) ->
	    match get_unit rlt op goal with
	      | None -> Some (goal, Bin (bin_pack, None))
	      | Some (gl, unit,s) ->
		let unit_of =
		  {
		    Unit.uf_u = unit;
		  (* TRICK : this term is not well-typed by itself,
		     but it is okay the way we use it in the other
		     functions *)
		    Unit.uf_idx = op;
		    Unit.uf_desc = s;
		  }
		in Some (gl,Bin (bin_pack, Some (unit_of)))
		

    (** {is_morphism} try to infer the kind of operator we are
	dealing with *)
    let is_morphism goal (rlt : AAC_coq.Relation.t) (papp : Term.constr) (ar : int) : (AAC_coq.goal_sigma * pack ) option      =
      let typeof = Classes.Proper.mk_typeof rlt ar in
      let relof = Classes.Proper.mk_relof rlt ar in
      let m = AAC_coq.Classes.mk_morphism  typeof relof  papp in
	try
	  let m,goal = AAC_coq.resolve_one_typeclass goal m in
	  let pack = {Sym.ar = (AAC_coq.Nat.of_int ar); Sym.value= papp; Sym.morph= m} in
	    Some (goal, Sym pack)
	with
	  | Not_found -> None
	     
	     
    (* [crop_app f [| a_0 ; ... ; a_n |]]
       returns Some (f a_0 ... a_(n-2), [|a_(n-1); a_n |] ) 
    *)
    let crop_app t ca : (constr * constr array) option=
      let n = Array.length ca in
	if n <= 1
	then None
	else
	  let papp = Term.mkApp (t, Array.sub ca 0 (n-2) ) in
	  let args = Array.sub ca (n-2) 2 in
	  Some (papp, args )
	     
    let fold goal (rlt : AAC_coq.Relation.t) envs t ca cont =
      let fold_morphism t ca  =
	let nb_params = Array.length ca in
	let rec aux n =
	  assert (n < nb_params && 0 < nb_params );
	  let papp = Term.mkApp (t, Array.sub ca 0 n) in 	   
	    match is_morphism goal rlt papp (nb_params - n) with
	      | None ->
		  (* here we have to memoize the failures *)
		  HMap.add envs.discr papp None;
		  if n < nb_params - 1 then aux (n+1) else goal
	      | Some (goal, pack) ->
		  let args = Array.sub ca (n) (nb_params -n)in
		  let goal = Array.fold_left cont goal args in
		    memoize envs papp pack;
		    goal
	in
	  if nb_params = 0 then goal else aux 0
      in
      let is_aac t = is_bin rlt t  in
	match crop_app t ca with
	  | None ->
		fold_morphism t ca
	  | Some (papp, args) ->
	      begin match is_aac papp goal with
		| None -> fold_morphism t ca
		| Some (goal, pack) ->
		    memoize envs papp pack;
		    Array.fold_left cont goal args 	     
	      end
	  	
    (* update in place the envs of known stuff, using memoization. We
       have to memoize failures, here. *)
    let gather goal (rlt : AAC_coq.Relation.t ) envs t : AAC_coq.goal_sigma =
      let rec aux goal x = 
	match AAC_coq.decomp_term x  with
	  | App (t,ca) ->
	      fold goal rlt envs t ca (aux )
	  | _ ->  goal
      in
	aux goal t
    end

  (** We build a term out of a constr, updating in place the
      environment if needed (the only kind of such updates are the
      constants).  *)
  module Parse :
  sig
    val  t_of_constr : AAC_coq.goal_sigma -> AAC_coq.Relation.t -> envs  -> constr -> AAC_matcher.Terms.t * AAC_coq.goal_sigma
  end
    = struct
     
      (** [discriminates goal envs rlt t ca] infer :

	  - its {! pack } (is it an AC operator, or an A operator, or a
	  Symbol ?),

	  - the relevant partial application,

	  - the vector of the remaining arguments

	  We use an expansion to handle the special case of units,
	  before going back to the general discrimination
	  procedure. That means that a unit is more coarse than a raw
	  morphism

	  This functions is prevented to go through [ar < 0] by the fact
	  that a constant is a morphism. But not an eva. *)

      let is_morphism goal (rlt : AAC_coq.Relation.t) (papp : Term.constr) (ar : int) : (AAC_coq.goal_sigma * pack ) option      =
	let typeof = Classes.Proper.mk_typeof rlt ar in
	let relof = Classes.Proper.mk_relof rlt ar in
	let m = AAC_coq.Classes.mk_morphism  typeof relof  papp in
	try
	  let m,goal = AAC_coq.resolve_one_typeclass goal m in
	  let pack = {Sym.ar = (AAC_coq.Nat.of_int ar); Sym.value= papp; Sym.morph= m} in
	  Some (goal, Sym pack)
	with
	  | e ->  None
	
      exception NotReflexive	
      let discriminate goal envs (rlt : AAC_coq.Relation.t) t ca : AAC_coq.goal_sigma * pack * constr * constr array =  
	let nb_params = Array.length ca in
	let rec fold goal ar :AAC_coq.goal_sigma  * pack * constr * constr array =
	  begin
	    assert (0 <= ar && ar <= nb_params);
	    let p_app = mkApp (t, Array.sub ca 0 (nb_params - ar)) in
	    begin	
	      try
		begin match HMap.find envs.discr p_app with
		  | None -> 
		    fold goal (ar-1)
		  | Some pack ->
		    (goal, pack, p_app,  Array.sub ca (nb_params -ar ) ar)
		end
	      with
		  Not_found -> (* Could not find this constr *)	
		    memoize (is_morphism goal rlt p_app ar) p_app ar
	    end
	  end
	and memoize (x) p_app ar =
	  assert (0 <= ar && ar <= nb_params);
	  match x with
	    | Some (goal, pack) ->
	      HMap.add envs.discr p_app (Some pack);
	      add_bloom envs pack;
	      (goal, pack, p_app, Array.sub ca (nb_params-ar) ar)
	    | None ->
	     
	      if ar = 0 then raise NotReflexive;
	      begin
		(* to memoise the failures *)
		HMap.add envs.discr p_app None;
		(* will terminate, since [const] is capped, and it is
		   easy to find an instance of a constant *)
		fold goal (ar-1)
	      end
	in
	try match HMap.find envs.discr (mkApp (t,ca))with
	  | None -> fold goal (nb_params)
	  | Some pack -> goal, pack, (mkApp (t,ca)), [| |]
	with Not_found -> fold goal (nb_params)
	 
      let discriminate goal envs rlt  x =
	try
	  match AAC_coq.decomp_term x with
	    | App (t,ca) ->
	      discriminate goal envs rlt   t ca
	    | _ -> discriminate goal envs rlt x [| |]
	with
	  | NotReflexive -> user_error "The relation to which the goal was lifted is not Reflexive"
	    (* TODO: is it the only source of invalid use that fall
	       into this catch_all ? *)
	  |  e -> 
	    user_error "Cannot handle this kind of hypotheses (variables occuring under a function symbol which is not a proper morphism)."

      (** [t_of_constr goal rlt envs cstr] builds the abstract syntax tree
	  of the term [cstr]. Doing so, it modifies the environment of
	  known stuff [envs], and eventually creates fresh
	  evars. Therefore, we give back the goal updated accordingly *)
      let t_of_constr goal (rlt: AAC_coq.Relation.t ) envs  : constr -> AAC_matcher.Terms.t * AAC_coq.goal_sigma =
	let r_goal = ref (goal) in
	let rec aux x =
	  match AAC_coq.decomp_term x with
	    | Rel i -> AAC_matcher.Terms.Var i
	    | _ ->
		let goal, pack , p_app, ca = discriminate (!r_goal) envs rlt   x in
		  r_goal := goal;
		  let k = find_bloom envs pack
		  in
		    match pack with
		      | Bin (pack,_) ->
			  begin match pack.Bin.comm with
			    | Some _ ->
				assert (Array.length ca = 2);
				AAC_matcher.Terms.Plus ( k, aux ca.(0), aux ca.(1))
			    | None  ->
				assert (Array.length ca = 2);
				AAC_matcher.Terms.Dot ( k, aux ca.(0), aux ca.(1))
			  end
		      | Unit _ ->
			  assert (Array.length ca = 0);
			  AAC_matcher.Terms.Unit ( k)
		      | Sym _  ->
			  AAC_matcher.Terms.Sym ( k, Array.map aux ca)		
	in
	  (
	    fun x -> let r = aux x in r,  !r_goal
	  )
	   
    end (* Parse *)

  let add_symbol goal rlt envs l =
    let goal = Gather.gather goal rlt envs (Term.mkApp (l, [| Term.mkRel 0;Term.mkRel 0|])) in
    goal
   
  (* [t_of_constr] buils a the abstract syntax tree of a constr,
     updating in place the environment. Doing so, we infer all the
     morphisms and the AC/A operators. It is mandatory to do so both
     for the pattern and the term, since AC symbols can occur in one
     and not the other *)
  let t_of_constr goal rlt envs (l,r) =
    let goal = Gather.gather goal rlt envs l in
    let goal = Gather.gather goal rlt envs r in
    let l,goal = Parse.t_of_constr goal rlt envs l in
    let r, goal = Parse.t_of_constr goal rlt envs r in
    l, r, goal
	
  (* An intermediate representation of the environment, with association lists for AC/A operators, and also the raw [packer] information *)
	
  type ir =
      {
	packer : (int, pack) Hashtbl.t; (* = bloom_back *)
	bin  : (int * Bin.pack) list	;
	units : (int * Unit.pack) list;
	sym : (int * Term.constr) list  ;
	matcher_units : AAC_matcher.ext_units
      }
	
  let ir_to_units ir = ir.matcher_units
   
  let ir_of_envs goal (rlt : AAC_coq.Relation.t) envs =
    let add x y l = (x,y)::l in
    let  nil = [] in
    let sym ,
      (bin   : (int * Bin.pack with_unit) list),
      (units : (int * constr) list) =
      Hashtbl.fold
	(fun int pack (sym,bin,units) ->
	  match pack with
	    | Bin s ->
	      sym, add (int) s bin, units
	    | Sym s ->
	      add (int) s sym, bin, units
	    | Unit s ->
	      sym, bin, add int s units
	) 
	envs.bloom_back 
	(nil,nil,nil)
    in
    let matcher_units =
      let unit_for , is_ac =
	List.fold_left
	  (fun ((unit_for,is_ac) as acc) (n,(bp,wu)) ->
	    match wu with
	      | None -> acc
	      | Some (unit_of) ->
		let unit_n = Hashtbl.find envs.bloom
		  (Unit unit_of.Unit.uf_u)
		in
		( n,  unit_n)::unit_for,
		(n, bp.Bin.comm <> None )::is_ac
		 
	  )
	  ([],[]) bin
      in
      {AAC_matcher.unit_for = unit_for; AAC_matcher.is_ac = is_ac}

    in
    let units : (int * Unit.pack) list =
      List.fold_left
	(fun acc (n,u) ->
	    (* first, gather all bins with this unit *)
	  let all_bin =
	    List.fold_left
	      ( fun acc (nop,(bp,wu)) ->
		match wu with
		  | None -> acc
		  | Some unit_of ->
		    if unit_of.Unit.uf_u = u
		    then
		      {unit_of with
			Unit.uf_idx = (AAC_coq.Pos.of_int nop)} :: acc
		    else
		      acc
	      )
	      [] bin
	  in
	  (n,{
	    Unit.u_value = u;
	    Unit.u_desc = all_bin
	  })::acc			    
	)
	[] units
	
    in
    goal, {
      packer = envs.bloom_back; 	
      bin =  (List.map (fun (n,(s,_)) -> n, s) bin);	
      units = units;
      sym = (List.map (fun (n,s) -> n,(Sym.mk_pack rlt s)) sym);
      matcher_units = matcher_units
    }

 

  (** {1 From AST back to Coq }
     
      The next functions allow one to map OCaml abstract syntax trees
      to Coq terms *)

 (** {2 Building raw, natural, terms} *)

  (** [raw_constr_of_t_debruijn] rebuilds a term in the raw
      representation, without products on top, and maybe escaping free
      debruijn indices (in the case of a pattern for example).  *)
  let raw_constr_of_t_debruijn ir  (t : AAC_matcher.Terms.t) : Term.constr * int list =
    let add_set,get =
      let r = ref [] in
      let rec add x = function
	  [ ] -> [x]
	| t::q when t = x -> t::q
	| t::q -> t:: (add x q)
      in
	(fun x -> r := add x !r),(fun () -> !r)
    in
      (* Here, we rely on the invariant that the maps are well formed:
	 it is meanigless to fail to find a symbol in the maps, or to
	 find the wrong kind of pack in the maps *)
    let rec aux t =
      match t with
	| AAC_matcher.Terms.Plus (s,l,r) ->
	    begin match Hashtbl.find ir.packer s with
	      | Bin (s,_) ->
		  mkApp (s.Bin.value ,  [|(aux l);(aux r)|])
	      | _ -> 	    Printf.printf "erreur:%i\n%!"s;
		  assert false
	    end
	| AAC_matcher.Terms.Dot (s,l,r) ->
	    begin match Hashtbl.find ir.packer s with
	      | Bin (s,_) ->
		  mkApp (s.Bin.value,  [|(aux l);(aux r)|])
	      | _ -> assert false
	    end
	| AAC_matcher.Terms.Sym (s,t) ->
	    begin match Hashtbl.find ir.packer s with
	      | Sym s ->
		  mkApp (s.Sym.value, Array.map aux t)
	      | _ -> assert false
	    end
	| AAC_matcher.Terms.Unit  x ->
	    begin match Hashtbl.find ir.packer x with
	      | Unit s -> s
	      | _ -> assert false
	    end
	| AAC_matcher.Terms.Var i -> add_set i;
	      mkRel (i)
    in
    let t = aux t in
      t , get ( )

  (** [raw_constr_of_t] rebuilds a term in the raw representation *)
  let raw_constr_of_t ir rlt (context:rel_context) t =
      (** cap rebuilds the products in front of the constr *)
    let rec cap c = function [] -> c
      | t::q -> 
	  let i = Term.lookup_rel t context in
	  cap (mkProd_or_LetIn i c) q
    in
    let t,indices = raw_constr_of_t_debruijn ir t in
      cap t (List.sort (Pervasives.compare) indices)

   
  (** {2 Building reified terms} *)
	
  (* Some informations to be able to build the maps  *)
  type reif_params =
      {
	bin_null : Bin.pack; 		(* the default A operator *)
	sym_null : constr;            
	unit_null : Unit.pack;
	sym_ty : constr;                (* the type, as it appears in e_sym *)
	bin_ty : constr
      }

    
  (** A record containing the environments that will be needed by the
      decision procedure, as a Coq constr. Contains the functions
      from the symbols (as ints) to indexes (as constr) *)

  type sigmas = {
    env_sym : Term.constr;
    env_bin : Term.constr;
    env_units : Term.constr; 		(* the [idx -> X:constr] *)
  }
    

  type sigma_maps = {
    sym_to_pos : int -> Term.constr;
    bin_to_pos : int -> Term.constr;
    units_to_pos : int -> Term.constr;
  }


  (** infers some stuff that will be required when we will build
      environments (our environments need a default case, so we need
      an Op_AC, an Op_A, and a symbol) *)
  (* Note : this function can fail if the user is using the wrong
     relation, like proving a = b, while the classes are defined with
     another relation (==) *)
  let build_reif_params goal (rlt : AAC_coq.Relation.t) (zero) :
      reif_params * AAC_coq.goal_sigma =
    let carrier = rlt.AAC_coq.Relation.carrier in
    let bin_null =
      try
	let op,goal = AAC_coq.evar_binary goal carrier in
	let assoc,goal = Classes.Associative.infer goal rlt op in
	let compat,goal = Classes.Proper.infer goal rlt op 2 in
	let op = AAC_coq.nf_evar goal op in
	  {
	    Bin.value = op;
	    Bin.compat = compat;
	    Bin.assoc = assoc;
	    Bin.comm = None
	  }
      with Not_found -> user_error "Cannot infer a default A operator (required at least to be Proper and Associative)"
    in
    let zero, goal =
      try
	let evar_op,goal = AAC_coq.evar_binary goal carrier in
	let evar_unit, goal = AAC_coq.evar_unit goal carrier in
	let query = Classes.Unit.ty rlt evar_op evar_unit in
	let _, goal = AAC_coq.resolve_one_typeclass goal query in
	  AAC_coq.nf_evar goal evar_unit, goal
      with _ -> 	zero, goal in 		
    let sym_null = Sym.null rlt in
    let unit_null = Unit.default zero in
    let record =
      {
	bin_null = bin_null;
	sym_null = sym_null;            
	unit_null = unit_null;
	sym_ty = Sym.mk_ty rlt ;
	bin_ty = Bin.mk_ty rlt
      }
    in
      record,     goal

  (* We want to lift down the indexes of symbols. *)
  let renumber (l: (int * 'a) list ) =
    let _, l = List.fold_left (fun (next,acc) (glob,x) ->
				 (next+1, (next,glob,x)::acc)
			      ) (1,[]) l
    in
    let rec to_global loc = function
      | [] -> assert false
      | (local, global,x)::q when  local = loc -> global
      | _::q -> to_global loc q
    in
    let rec to_local glob = function
      | [] -> assert false
      | (local, global,x)::q when  global = glob -> local
      | _::q -> to_local glob q
    in
    let locals = List.map (fun (local,global,x) -> local,x) l in
      locals, (fun x -> to_local x l) , (fun x -> to_global x l)

  (** [build_sigma_maps] given a envs and some reif_params, we are
      able to build the sigmas *)
  let build_sigma_maps  (rlt : AAC_coq.Relation.t) zero ir (k : sigmas * sigma_maps -> Proof_type.tactic ) : Proof_type.tactic = fun goal ->
    let rp,goal = build_reif_params goal rlt zero  in
    let renumbered_sym, to_local, to_global = renumber ir.sym  in
    let env_sym = Sigma.of_list
      rp.sym_ty
      (rp.sym_null)
      renumbered_sym
    in
      AAC_coq.cps_mk_letin "env_sym" env_sym
	(fun env_sym ->
	   let bin = (List.map ( fun (n,s) -> n, Bin.mk_pack rlt s) ir.bin) in
	   let env_bin =
	     Sigma.of_list
	       rp.bin_ty
	       (Bin.mk_pack rlt rp.bin_null)
	       bin
	   in
	     AAC_coq.cps_mk_letin "env_bin" env_bin
	       (fun env_bin ->
		  let units = (List.map (fun (n,s) -> n, Unit.mk_pack rlt env_bin s)ir.units) in 	     		   
		  let env_units =
		    Sigma.of_list
		      (Unit.ty_unit_pack rlt env_bin)
		      (Unit.mk_pack rlt env_bin rp.unit_null )
		      units
		  in

		    AAC_coq.cps_mk_letin "env_units" env_units
		      (fun env_units -> 		   
			 let sigmas =
			   {
			     env_sym =   env_sym ;
			     env_bin =   env_bin ;
			     env_units  = env_units;
			   } in
			 let f = List.map (fun (x,_) -> (x,AAC_coq.Pos.of_int x)) in
			 let sigma_maps =
			   {
			     sym_to_pos = (let sym = f renumbered_sym in fun x ->  (List.assoc (to_local x) sym));
			     bin_to_pos = (let bin = f bin in fun x ->  (List.assoc  x bin));
			     units_to_pos = (let units = f units in fun x ->  (List.assoc  x units));
			   }
			 in
			   k (sigmas, sigma_maps )
		      )
	       )
	) goal	

  (** builders for the reification *)
  type reif_builders =
      {
	rsum: constr -> constr -> constr -> constr;
	rprd: constr -> constr -> constr -> constr;
	rsym: constr -> constr array -> constr;
	runit : constr -> constr			
      }

  (* donne moi une tactique, je rajoute ma part.  Potentiellement, il
     est possible d'utiliser la notation 'do' a la Haskell:
     http://www.cas.mcmaster.ca/~carette/pa_monad/ *)
  let (>>) : 'a * Proof_type.tactic -> ('a -> 'b * Proof_type.tactic) -> 'b * Proof_type.tactic =
    fun (x,t) f ->
      let b,t' = f x in
	b, Tacticals.tclTHEN t t'
	 
  let return x = x, Tacticals.tclIDTAC
   
  let mk_vect vnil vcons v =
    let ar = Array.length v in
    let rec aux = function
      | 0 ->  vnil
      | n  -> let n = n-1 in
	  mkApp( vcons,
 		 [|
		   (AAC_coq.Nat.of_int n);
		   v.(ar - 1 - n);
		   (aux (n))
		 |]	
	       )
    in aux ar
	
  (* TODO: use a do notation *)
  let mk_reif_builders  (rlt: AAC_coq.Relation.t)   (env_sym:constr)  (k: reif_builders -> Proof_type.tactic) =
    let x = (rlt.AAC_coq.Relation.carrier) in
    let r = (rlt.AAC_coq.Relation.r) in

    let x_r_env = [|x;r;env_sym|] in
    let tty =  mkApp (Lazy.force Stubs._Tty, x_r_env) in
    let rsum = mkApp (Lazy.force Stubs.rsum, x_r_env) in
    let rprd = mkApp (Lazy.force Stubs.rprd, x_r_env) in
    let rsym = mkApp (Lazy.force Stubs.rsym, x_r_env) in
    let vnil = mkApp (Lazy.force Stubs.vnil, x_r_env) in
    let vcons = mkApp (Lazy.force Stubs.vcons, x_r_env) in
      AAC_coq.cps_mk_letin "tty" tty
      (fun tty ->
      AAC_coq.cps_mk_letin "rsum" rsum
      (fun rsum ->
      AAC_coq.cps_mk_letin "rprd" rprd
      (fun rprd ->
      AAC_coq.cps_mk_letin "rsym" rsym
      (fun rsym ->
      AAC_coq.cps_mk_letin "vnil" vnil
      (fun vnil ->
      AAC_coq.cps_mk_letin "vcons" vcons
      (fun vcons ->
	 let r ={
	   rsum =
	     begin fun idx l r ->
	       mkApp (rsum, [|  idx ; mk_mset tty [l,1 ; r,1]|])
	     end;
	   rprd =
	     begin fun idx l r ->
	       let lst = NEList.of_list tty [l;r] in
		 mkApp (rprd, [| idx; lst|])
	     end;
	   rsym =
	     begin fun idx v ->
	       let vect = mk_vect vnil vcons  v in
		 mkApp (rsym, [| idx; vect|])
	     end;
	   runit = fun idx -> 	(* could benefit of a letin *)
	     mkApp (Lazy.force Stubs.runit , [|x;r;env_sym;idx; |])
	 }
	 in k r
      ))))))
     


  type reifier = sigma_maps * reif_builders
    
     
  let  mk_reifier rlt zero envs (k : sigmas *reifier -> Proof_type.tactic) =
    build_sigma_maps rlt zero envs
      (fun (s,sm) ->
	   mk_reif_builders rlt s.env_sym
	     (fun rb ->k (s,(sm,rb)) )
	    
      )
      	
  (** [reif_constr_of_t reifier t] rebuilds the term [t] in the
      reified form. We use the [reifier] to minimise the size of the
      terms (we make as much lets as possible)*)
  let reif_constr_of_t (sm,rb) (t:AAC_matcher.Terms.t) : constr =
    let rec aux = function
      | AAC_matcher.Terms.Plus (s,l,r) ->
	  let idx = sm.bin_to_pos s  in
	    rb.rsum idx (aux l) (aux r)
      | AAC_matcher.Terms.Dot (s,l,r) ->
	  let idx = sm.bin_to_pos s in
	    rb.rprd idx (aux l) (aux r)
      | AAC_matcher.Terms.Sym (s,t) ->
	  let idx =  sm.sym_to_pos  s in
	    rb.rsym idx (Array.map aux t)
      | AAC_matcher.Terms.Unit s ->
	  let idx = sm.units_to_pos s in
	    rb.runit idx
      | AAC_matcher.Terms.Var i ->
	  anomaly "call to reif_constr_of_t on a term with variables."
    in aux t
end



