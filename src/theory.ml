(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Constr from the theory of this particular development

    The inner-working of this module is highly correlated with the
    particular structure of {b AAC_rewrite.v}, therefore, it should
    be of little interest to most readers.
*)
open EConstr

module Control = struct
  let printing = true
  let debug = false
  let time = false
end

module Debug = Helper.Debug (Control)
open Debug

(** {1 HMap :     Specialized Hashtables based on constr} *)


  (* TODO module HMap = Hashtbl, du coup ? *)
module HMap = Hashtbl.Make(Constr)

module Stubs = struct

  (** The constants from the inductive type *)
  let _Tty = Coq.find_global "internal.T"

  let rsum = Coq.find_global "internal.sum"
  let rprd = Coq.find_global "internal.prd"
  let rsym = Coq.find_global "internal.sym"
  let runit = Coq.find_global "internal.unit"

  let vnil = Coq.find_global "internal.vnil"
  let vcons = Coq.find_global "internal.vcons"
  let eval = Coq.find_global "internal.eval"


  let decide_thm = Coq.find_global "internal.decide"
  let lift_normalise_thm = Coq.find_global "internal.lift_normalise"

  let lift = Coq.find_global "internal.AAC_lift"
  let lift_proj_equivalence= Coq.find_global "internal.aac_lift_equivalence"
  let lift_transitivity_left = Coq.find_global "internal.lift_transitivity_left"
  let lift_transitivity_right = Coq.find_global "internal.lift_transitivity_right"
  let lift_reflexivity = Coq.find_global "internal.lift_reflexivity"
end

module Classes = struct
  module Associative = struct
    let typ = Coq.find_global "classes.Associative"
    let ty (rlt : Coq.Relation.t) (value : constr) =
      mkApp (Coq.get_efresh typ, [| rlt.Coq.Relation.carrier;
				rlt.Coq.Relation.r;
				value
			     |] )
    let infer env sigma rlt value =
      let ty = ty rlt value in
      Typeclasses.resolve_one_typeclass env sigma ty
  end

  module Commutative = struct
    let typ = Coq.find_global "classes.Commutative"
    let ty (rlt : Coq.Relation.t) (value : constr) =
      mkApp (Coq.get_efresh typ, [| rlt.Coq.Relation.carrier;
				rlt.Coq.Relation.r;
				value
			     |] )

  end

  module Idempotent = struct
    let typ = Coq.find_global "classes.Idempotent"
    let ty (rlt : Coq.Relation.t) (value : constr) =
      mkApp (Coq.get_efresh typ, [| rlt.Coq.Relation.carrier;
				rlt.Coq.Relation.r;
				value
			     |] )

  end

  module Proper = struct
    let typeof =  Coq.find_global "internal.sym.type_of"
    let relof = Coq.find_global "internal.sym.rel_of"
    let mk_typeof :  Coq.Relation.t -> int -> constr = fun rlt n ->
      let x = rlt.Coq.Relation.carrier in
	mkApp (Coq.get_efresh typeof, [| x ; of_constr (Coq.Nat.of_int n) |])
    let mk_relof :  Coq.Relation.t -> int -> constr = fun rlt n ->
      let (x,r) = Coq.Relation.split rlt in
      mkApp (Coq.get_efresh relof, [| x;r ; of_constr (Coq.Nat.of_int n) |])

    let ty rlt op ar  =
      let typeof = mk_typeof rlt ar in
      let relof = mk_relof rlt ar in
	Coq.Classes.mk_morphism  typeof relof op
    let infer env sigma rlt op ar =
      let ty = ty rlt op ar in
	Typeclasses.resolve_one_typeclass env sigma ty
  end

  module Unit = struct
    let typ = Coq.find_global "classes.Unit"
    let ty (rlt : Coq.Relation.t) (value : constr) (unit : constr)=
      mkApp (Coq.get_efresh typ, [| rlt.Coq.Relation.carrier;
 				rlt.Coq.Relation.r;
 				value;
 				unit
 			     |] )
  end

end

(* Non empty lists *)
module NEList = struct
  let nil = Coq.find_global "nelist.nil"
  let cons = Coq.find_global "nelist.cons"
  let cons ty h t =
    mkApp (Coq.get_efresh cons, [|  ty; h ; t |])
  let nil ty x =
    (mkApp (Coq.get_efresh nil, [|  ty ; x|]))
  let rec of_list ty = function
    | [] -> invalid_arg "NELIST"
    | [x] -> nil ty x
    | t::q -> cons ty t (of_list  ty q)

end

(** a [mset] is a ('a * pos) list *)
let mk_mset ty (l : (constr * int) list) =
  let pos = Coq.get_efresh Coq.Pos.typ in
  let pair (x : constr) (ar : int) =
    Coq.Pair.of_pair ty pos (x, Coq.Pos.of_int ar)
  in
  let pair_ty = mkApp (Coq.get_efresh Coq.Pair.typ,[| ty ; pos|]) in
  let rec aux = function
    | [ ] -> assert false
    | [x,ar] -> NEList.nil pair_ty (pair x ar)
    | (t,ar)::q -> NEList.cons pair_ty (pair t ar) (aux q)
  in
    aux l

module Sigma = struct
  let sigma_empty = Coq.find_global "sigma.empty"
  let sigma_add = Coq.find_global "sigma.add"
  let sigma_get = Coq.find_global "sigma.get"

  let add ty n x map =
    mkApp (Coq.get_efresh sigma_add,[|ty; n; x ;  map|])
  let empty ty =
    mkApp (Coq.get_efresh sigma_empty,[|ty |])

  let to_fun ty null map =
    mkApp (Coq.get_efresh sigma_get, [|ty;null;map|])

  let of_list ty null l =
    match l with
      | (_,t)::q ->
	  let map =
	    List.fold_left
	      (fun acc (i,t) ->
		 assert (i > 0);
		 add ty (Coq.Pos.of_int i) ( t) acc)
	      (empty ty)
	      q
	  in to_fun ty (t) map
      | [] -> debug "of_list empty" ; to_fun ty (null) (empty ty)


end


module Sym = struct
  type pack = {ar: Constr.t; value: Constr.t ; morph: Constr.t}
  let typ = Coq.find_global "sym.pack"
  let mkPack = Coq.find_global "sym.mkPack"
  let null = Coq.find_global "sym.null"
  let mk_pack (rlt: Coq.Relation.t) s =
    let (x,r) = Coq.Relation.split rlt in
      mkApp (Coq.get_efresh mkPack, [|x;r; EConstr.of_constr s.ar;EConstr.of_constr s.value;EConstr.of_constr s.morph|])
  let null  rlt =
    let x = rlt.Coq.Relation.carrier in
    let r = rlt.Coq.Relation.r in
      mkApp (Coq.get_efresh null, [| x;r;|])

  let mk_ty : Coq.Relation.t -> constr = fun rlt ->
    let (x,r) = Coq.Relation.split rlt in
      mkApp (Coq.get_efresh typ, [| x; r|] )
end

module Bin =struct
  type pack = {value : Constr.t;
	       compat : Constr.t;
	       assoc : Constr.t;
	       comm : Constr.t option;
	       idem : Constr.t option;
	      }

  let typ = Coq.find_global "bin.pack"
  let mkPack = Coq.find_global "bin.mkPack"

  let mk_pack: Coq.Relation.t -> pack -> constr = fun (rlt) s ->
    let (x,r) = Coq.Relation.split rlt in
    let comm_ty = Classes.Commutative.ty rlt (EConstr.of_constr s.value) in
    let idem_ty = Classes.Idempotent.ty rlt (EConstr.of_constr s.value) in
    mkApp (Coq.get_efresh mkPack , [| x ; r;
				  EConstr.of_constr s.value;
				  EConstr.of_constr s.compat ;
				  EConstr.of_constr s.assoc;
				  Coq.Option.of_option comm_ty (Option.map EConstr.of_constr s.comm);
				  Coq.Option.of_option idem_ty (Option.map EConstr.of_constr s.idem)
			       |])
  let mk_ty : Coq.Relation.t -> constr = fun rlt ->
   let (x,r) = Coq.Relation.split rlt in
      mkApp (Coq.get_efresh typ, [| x; r|] )
end

module Unit = struct
  let unit_of_ty = Coq.find_global "internal.unit_of"
  let unit_pack_ty = Coq.find_global "internal.unit_pack"
  let mk_unit_of = Coq.find_global "internal.mk_unit_for"
  let mk_unit_pack = Coq.find_global "internal.mk_unit_pack"

  type unit_of =
      {
	uf_u : Constr.t; 		(* u *)
	uf_idx : Constr.t;
	uf_desc : Constr.t; (* Unit R (e_bin uf_idx) u *)
      }

  type pack = {
    u_value : constr;	(* X *)
    u_desc : (unit_of) list (* unit_of u_value *)
  }

  let ty_unit_of rlt  e_bin u =
    let (x,r) = Coq.Relation.split rlt in
      mkApp ( Coq.get_efresh unit_of_ty, [| x; r; e_bin; u |])

  let ty_unit_pack rlt e_bin =
    let (x,r) = Coq.Relation.split rlt in
      mkApp (Coq.get_efresh unit_pack_ty, [| x; r; e_bin |])

  let mk_unit_of rlt e_bin u unit_of =
    let (x,r) = Coq.Relation.split rlt in
    mkApp (Coq.get_efresh mk_unit_of , [| x;
				      r;
				      e_bin ;
				      u;
				      EConstr.of_constr unit_of.uf_idx;
				      EConstr.of_constr unit_of.uf_desc
				   |])

  let mk_pack rlt e_bin pack : constr =
    let (x,r) = Coq.Relation.split rlt in
    let ty = ty_unit_of rlt e_bin pack.u_value in
    let mk_unit_of = mk_unit_of rlt e_bin pack.u_value in
    let u_desc =Coq.List.of_list ( ty ) (List.map mk_unit_of pack.u_desc) in
      mkApp (Coq.get_efresh mk_unit_pack, [|x;r;
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
  CErrors.anomaly ~label:"aac_tactics" (Pp.str msg)

let user_error msg =
  CErrors.user_err Pp.(strbrk "aac_tactics: " ++ msg)

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
    | Unit of Constr.t  			(* to avoid confusion in bloom *)

  module PackHash =
  struct
    open Hashset.Combine

    type t = pack

    let eq_sym_pack p1 p2 =
      let open Sym in
      Constr.equal p1.ar p2.ar &&
      Constr.equal p1.value p2.value &&
      Constr.equal p1.morph p2.morph

    let hash_sym_pack p =
      let open Sym in
      combine3 (Constr.hash p.ar) (Constr.hash p.value) (Constr.hash p.morph)

    let eq_bin_pack p1 p2 =
      let open Bin in
      Constr.equal p1.value p2.value &&
      Constr.equal p1.compat p2.compat &&
      Constr.equal p1.assoc p2.assoc &&
      Option.equal Constr.equal p1.comm p2.comm &&
      Option.equal Constr.equal p1.idem p2.idem


    let hash_bin_pack p =
      let open Bin in
      combine5 (Constr.hash p.value) (Constr.hash p.compat)
        (Constr.hash p.assoc) (Option.hash Constr.hash p.comm) (Option.hash Constr.hash p.idem)

    let eq_unit_of u1 u2 =
      let open Unit in
      Constr.equal u1.uf_u u2.uf_u &&
      Constr.equal u1.uf_idx u2.uf_idx &&
      Constr.equal u1.uf_desc u2.uf_desc

    let hash_unit_of u =
      let open Unit in
      combine3 (Constr.hash u.uf_u) (Constr.hash u.uf_idx)
        (Constr.hash u.uf_desc)

    let equal p1 p2 = match p1, p2 with
    | Bin (p1, o1), Bin (p2, o2) ->
      eq_bin_pack p1 p2 && Option.equal eq_unit_of o1 o2
    | Sym p1, Sym p2 -> eq_sym_pack p1 p2
    | Unit c1, Unit c2 -> Constr.equal c1 c2
    | _ -> false

    let hash p = match p with
    | Bin (p, o) ->
      combinesmall 1 (combine (hash_bin_pack p) (Option.hash hash_unit_of o))
    | Sym p ->
      combinesmall 2 (hash_sym_pack p)
    | Unit c ->
      combinesmall 3 (Constr.hash c)

  end

  module PackTable = Hashtbl.Make(PackHash)

  (** discr is a map from {!constr} to {!pack}.

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
	bloom : int PackTable.t;
	bloom_back  : (int, pack ) Hashtbl.t;
	bloom_next : int ref;
      }

  let empty_envs () =
    {
      discr = HMap.create 17;
      bloom  =  PackTable.create 17;
      bloom_back  =  Hashtbl.create 17;
      bloom_next = ref 1;
    }



  let add_bloom envs pack =
    if PackTable.mem envs.bloom pack
    then ()
    else
      let x = ! (envs.bloom_next) in
	PackTable.add envs.bloom pack x;
	Hashtbl.add envs.bloom_back x pack;
	incr (envs.bloom_next)

  let find_bloom envs pack =
    try PackTable.find envs.bloom pack
    with Not_found -> assert false

  	    (*********************************************)
	    (* (\* Gather the occurring AC/A symbols *\) *)
	    (*********************************************)

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
    val gather : Environ.env -> Evd.evar_map -> Coq.Relation.t -> envs -> constr -> Evd.evar_map
  end
    = struct

      let memoize envs t pack : unit =
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


      let get_unit (rlt : Coq.Relation.t) op env sigma :
	    (Evd.evar_map * constr * constr ) option=
	let x = (rlt.Coq.Relation.carrier)  in
	let sigma,unit = Evarutil.new_evar env sigma x in
	let ty =Classes.Unit.ty rlt  op  unit in
	let result =
	  try
	    let sigma,t = Typeclasses.resolve_one_typeclass env sigma ty in
	    Some (sigma,t,unit)
	  with Not_found -> None
	in
	match result with
	  | None -> None
	  | Some (sigma,s,unit) ->
	     let unit = Evarutil.nf_evar sigma unit in
	    Some (sigma, unit, s)



      (** gives back the class and the operator *)
      let is_bin  (rlt: Coq.Relation.t) (op: constr) env (sigma : Evd.evar_map)
	  : (Evd.evar_map * Bin.pack) option =
	let assoc_ty = Classes.Associative.ty rlt op in
	let comm_ty = Classes.Commutative.ty rlt op in
	let idem_ty = Classes.Idempotent.ty rlt op in
	let proper_ty  = Classes.Proper.ty rlt op 2 in
	try
	  let sigma, proper = Typeclasses.resolve_one_typeclass env sigma proper_ty in
	  let sigma, assoc = Typeclasses.resolve_one_typeclass env sigma assoc_ty in
	  let sigma, comm  =
	    try
	      let sigma,comm = Typeclasses.resolve_one_typeclass env sigma comm_ty in
	      sigma, Some comm
	    with Not_found ->
	      sigma, None
	  in
	  let sigma, idem  =
	    try
	      let sigma,idem = Typeclasses.resolve_one_typeclass env sigma idem_ty in
	      sigma, Some idem
	    with Not_found ->
	      sigma, None
	  in
	  let bin =
	    {Bin.value = EConstr.to_constr sigma op;
	     Bin.compat = EConstr.to_constr sigma proper;
	     Bin.assoc = EConstr.to_constr sigma assoc;
	     Bin.comm = Option.map (EConstr.to_constr sigma) comm;
	     Bin.idem = Option.map (EConstr.to_constr sigma) idem }
	  in
	  Some (sigma,bin)
	with |Not_found -> None

      let is_bin (rlt : Coq.Relation.t) (op : constr) env (sigma : Evd.evar_map)=
	match is_bin rlt op env sigma with
	  | None -> None
	  | Some (sigma, bin_pack) ->
	    match get_unit rlt op env sigma with
	      | None -> Some (sigma, Bin (bin_pack, None))
	      | Some (gl, unit,s) ->
		let unit_of =
		  {
		    Unit.uf_u = EConstr.to_constr sigma unit;
		  (* TRICK : this term is not well-typed by itself,
		     but it is okay the way we use it in the other
		     functions *)
		    Unit.uf_idx = EConstr.to_constr sigma op;
		    Unit.uf_desc = EConstr.to_constr sigma s;
		  }
		in Some (gl,Bin (bin_pack, Some (unit_of)))


    (** {is_morphism} try to infer the kind of operator we are
	dealing with *)
      let is_morphism env sigma (rlt : Coq.Relation.t) (papp : constr) (ar : int) : (Evd.evar_map * pack ) option      =
      let typeof = Classes.Proper.mk_typeof rlt ar in
      let relof = Classes.Proper.mk_relof rlt ar in
      let m = Coq.Classes.mk_morphism  typeof relof  papp in
	try
	  let sigma,m= Typeclasses.resolve_one_typeclass env sigma m in
	  let pack = {Sym.ar = Coq.Nat.of_int ar;
                      Sym.value= EConstr.to_constr sigma papp;
                      Sym.morph= EConstr.to_constr sigma m} in
	    Some (sigma, Sym pack)
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
	  let papp = mkApp (t, Array.sub ca 0 (n-2) ) in
	  let args = Array.sub ca (n-2) 2 in
	  Some (papp, args )

    let fold env sigma (rlt : Coq.Relation.t) envs t ca cont =
      let fold_morphism t ca  =
	let nb_params = Array.length ca in
	let rec aux n =
	  assert (n < nb_params && 0 < nb_params );
	  let papp = mkApp (t, Array.sub ca 0 n) in
	    match is_morphism env sigma rlt papp (nb_params - n) with
	      | None ->
		  (* here we have to memoize the failures *)
		  HMap.add envs.discr (EConstr.to_constr sigma papp) None;
		  if n < nb_params - 1 then aux (n+1) else sigma
	      | Some (sigma, pack) ->
		  let args = Array.sub ca (n) (nb_params -n)in
		  let sigma = Array.fold_left cont sigma args in
		    memoize envs (EConstr.to_constr sigma papp) pack;
		    sigma
	in
	  if nb_params = 0 then sigma else aux 0
      in
      let is_aac t = is_bin rlt t  in
	match crop_app t ca with
	  | None ->
		fold_morphism t ca
	  | Some (papp, args) ->
	      begin match is_aac papp env sigma with
		| None -> fold_morphism t ca
		| Some (sigma, pack) ->
		    memoize envs (EConstr.to_constr sigma papp) pack;
		    Array.fold_left cont sigma args
	      end

    (* update in place the envs of known stuff, using memoization. We
       have to memoize failures, here. *)
    let gather env sigma (rlt : Coq.Relation.t ) envs t : Evd.evar_map =
      let rec aux sigma x =
	match Coq.decomp_term sigma x with
	  | Constr.App (t,ca) ->
	      fold env sigma rlt envs t ca (aux )
	  | _ ->  sigma
      in
	aux sigma t
    end

  (** We build a term out of a constr, updating in place the
      environment if needed (the only kind of such updates are the
      constants).  *)
  module Parse :
  sig
    val  t_of_constr : Environ.env -> Evd.evar_map -> Coq.Relation.t -> envs  -> constr -> Matcher.Terms.t * Evd.evar_map
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

      let is_morphism env sigma (rlt : Coq.Relation.t) (papp : constr) (ar : int) : (Evd.evar_map * pack ) option      =
	let typeof = Classes.Proper.mk_typeof rlt ar in
	let relof = Classes.Proper.mk_relof rlt ar in
	let m = Coq.Classes.mk_morphism  typeof relof  papp in
	try
	  let sigma,m = Typeclasses.resolve_one_typeclass env sigma m in
	  let pack = {Sym.ar = Coq.Nat.of_int ar;
                      Sym.value= EConstr.to_constr ~abort_on_undefined_evars:(false) sigma papp;
                      Sym.morph= EConstr.to_constr ~abort_on_undefined_evars:(false) sigma m} in
	  Some (sigma, Sym pack)
	with
	  | e ->  None

      exception NotReflexive
      let discriminate env sigma envs (rlt : Coq.Relation.t) t ca : Evd.evar_map * pack * constr * constr array =
	let nb_params = Array.length ca in
	let rec fold sigma ar :Evd.evar_map  * pack * constr * constr array =
	  begin
	    assert (0 <= ar && ar <= nb_params);
	    let p_app = mkApp (t, Array.sub ca 0 (nb_params - ar)) in
	    begin
	      try
		begin match HMap.find envs.discr (EConstr.to_constr ~abort_on_undefined_evars:(false) sigma p_app) with
		  | None ->
		    fold sigma (ar-1)
		  | Some pack ->
		    (sigma, pack, p_app,  Array.sub ca (nb_params -ar ) ar)
		end
	      with
		  Not_found -> (* Could not find this constr *)
		    memoize (is_morphism env sigma rlt p_app ar) p_app ar
	    end
	  end
	and memoize (x) p_app ar =
	  assert (0 <= ar && ar <= nb_params);
	  match x with
	    | Some (sigma, pack) ->
	      HMap.add envs.discr (EConstr.to_constr ~abort_on_undefined_evars:(false) sigma p_app) (Some pack);
	      add_bloom envs pack;
	      (sigma, pack, p_app, Array.sub ca (nb_params-ar) ar)
	    | None ->

	      if ar = 0 then raise NotReflexive;
	      begin
		(* to memoise the failures *)
		HMap.add envs.discr (EConstr.to_constr ~abort_on_undefined_evars:(false) sigma p_app) None;
		(* will terminate, since [const] is capped, and it is
		   easy to find an instance of a constant *)
		fold sigma (ar-1)
	      end
	in
	try match HMap.find envs.discr (EConstr.to_constr ~abort_on_undefined_evars:(false) sigma (mkApp (t,ca))) with
	  | None -> fold sigma (nb_params)
	  | Some pack -> sigma, pack, (mkApp (t,ca)), [| |]
	with Not_found -> fold sigma (nb_params)

      let discriminate env sigma envs rlt  x =
	try
	  match Coq.decomp_term sigma x with
	    | Constr.App (t,ca) ->
	      discriminate env sigma envs rlt   t ca
	    | _ -> discriminate env sigma envs rlt x [| |]
	with
	  | NotReflexive -> user_error @@ Pp.strbrk "The relation to which the goal was lifted is not Reflexive"
	    (* TODO: is it the only source of invalid use that fall
	       into this catch_all ? *)
	  |  e ->
	    user_error @@ Pp.strbrk "Cannot handle this kind of hypotheses (variables occurring under a function symbol which is not a proper morphism)."

      (** [t_of_constr env sigma rlt envs cstr] builds the abstract syntax tree
	  of the term [cstr]. Doing so, it modifies the environment of
	  known stuff [envs], and eventually creates fresh
	  evars. Therefore, we give back the evar map updated accordingly *)
      let t_of_constr env sigma (rlt: Coq.Relation.t ) envs  : constr -> Matcher.Terms.t * Evd.evar_map =
	let r_sigma = ref (sigma) in
	let rec aux x =
	  match Coq.decomp_term sigma x with
	    | Constr.Rel i -> Matcher.Terms.Var i
	    | _ ->
		let sigma, pack , p_app, ca = discriminate env (!r_sigma) envs rlt   x in
		  r_sigma := sigma;
		  let k = find_bloom envs pack
		  in
		    match pack with
		      | Bin (pack,_) ->
			  begin match pack.Bin.comm with
			    | Some _ ->
				assert (Array.length ca = 2);
				Matcher.Terms.Plus ( k, aux ca.(0), aux ca.(1))
			    | None  ->
				assert (Array.length ca = 2);
				Matcher.Terms.Dot ( k, aux ca.(0), aux ca.(1))
			  end
		      | Unit _ ->
			  assert (Array.length ca = 0);
			  Matcher.Terms.Unit ( k)
		      | Sym _  ->
			  Matcher.Terms.Sym ( k, Array.map aux ca)
	in
	  (
	    fun x -> let r = aux x in r,  !r_sigma
	  )

    end (* Parse *)

  let add_symbol env sigma rlt envs l =
    let sigma = Gather.gather env sigma rlt envs (EConstr.of_constr (Constr.mkApp (l, [| Constr.mkRel 0;Constr.mkRel 0|]))) in
    sigma

  (* reorder the environment to make it (more) canonical *)
  let reorder envs =
    let rec insert k v = function
      | [] -> [k,v]
      | ((h,_)::_) as l when Constr.compare k h = -1 -> (k,v)::l
      | y::q -> y::insert k v q
    in
    let insert k v l =
      match v with Some v -> insert k v l | None -> l
    in
    let l = HMap.fold insert envs.discr [] in
    let old = Hashtbl.copy envs.bloom_back in
    PackTable.clear envs.bloom;
    Hashtbl.clear envs.bloom_back;
    envs.bloom_next := 1;
    List.iter (fun (c,pack) -> add_bloom envs pack) l;
    (fun s -> PackTable.find envs.bloom (Hashtbl.find old s))
  
  (* [t_of_constr] buils a the abstract syntax tree of a constr,
     updating in place the environment. Doing so, we infer all the
     morphisms and the AC/A operators. It is mandatory to do so both
     for the pattern and the term, since AC symbols can occur in one
     and not the other *)
  let t_of_constr env sigma rlt envs (l,r) =
    let sigma = Gather.gather env sigma rlt envs l in
    let sigma = Gather.gather env sigma rlt envs r in
    let l,sigma = Parse.t_of_constr env sigma rlt envs l in
    let r, sigma = Parse.t_of_constr env sigma rlt envs r in
    let p = reorder envs in
    Matcher.Terms.map_syms p l, Matcher.Terms.map_syms p r, sigma

  (* An intermediate representation of the environment, with association lists for AC/A operators, and also the raw [packer] information *)

  type ir =
      {
	packer : (int, pack) Hashtbl.t; (* = bloom_back *)
	bin  : (int * Bin.pack) list	;
	units : (int * Unit.pack) list;
	sym : (int * constr) list  ;
	matcher_units : Matcher.ext_units
      }

  let ir_to_units ir = ir.matcher_units

  let ir_of_envs env sigma (rlt : Coq.Relation.t) envs =
    let add x y l = (x,y)::l in
    let  nil = [] in
    let sym ,
      (bin   : (int * Bin.pack with_unit) list),
      (units : (int * Constr.t) list) =
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
		let unit_n = PackTable.find envs.bloom
		  (Unit unit_of.Unit.uf_u)
		in
		( n,  unit_n)::unit_for,
		(n, bp.Bin.comm <> None )::is_ac

	  )
	  ([],[]) bin
      in
      {Matcher.unit_for = unit_for; Matcher.is_ac = is_ac}

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
		    if Constr.equal (unit_of.Unit.uf_u) u
		    then
		      {unit_of with
			Unit.uf_idx = EConstr.to_constr sigma (Coq.Pos.of_int nop)} :: acc
		    else
		      acc
	      )
	      [] bin
	  in
	  (n,{
	    Unit.u_value = EConstr.of_constr u;
	    Unit.u_desc = all_bin
	  })::acc
	)
	[] units

    in
    sigma, {
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
  let raw_constr_of_t_debruijn ir  (t : Matcher.Terms.t) : constr * int list =
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
	| Matcher.Terms.Plus (s,l,r) ->
	    begin match Hashtbl.find ir.packer s with
	      | Bin (s,_) ->
		  mkApp (EConstr.of_constr s.Bin.value ,  [|(aux l);(aux r)|])
	      | _ -> 	    Printf.printf "erreur:%i\n%!"s;
		  assert false
	    end
	| Matcher.Terms.Dot (s,l,r) ->
	    begin match Hashtbl.find ir.packer s with
	      | Bin (s,_) ->
		  mkApp (EConstr.of_constr s.Bin.value,  [|(aux l);(aux r)|])
	      | _ -> assert false
	    end
	| Matcher.Terms.Sym (s,t) ->
	    begin match Hashtbl.find ir.packer s with
	      | Sym s ->
		  mkApp (EConstr.of_constr s.Sym.value, Array.map aux t)
	      | _ -> assert false
	    end
	| Matcher.Terms.Unit  x ->
	    begin match Hashtbl.find ir.packer x with
	      | Unit s -> EConstr.of_constr s
	      | _ -> assert false
	    end
	| Matcher.Terms.Var i -> add_set i;
	      mkRel (i)
    in
    let t = aux t in
      t , get ( )

  (** [raw_constr_of_t] rebuilds a term in the raw representation *)
  let raw_constr_of_t ir rlt (context:rel_context) t =

    (* cap rebuilds the products in front of the constr *)
    let rec cap c = function [] -> c
      | t::q ->
	  let i = Context.Rel.lookup t context in
	  cap (mkProd_or_LetIn i c) q
    in
    let t,indices = raw_constr_of_t_debruijn ir t in
      cap t (List.sort (Stdlib.compare) indices)


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
    env_sym : constr;
    env_bin : constr;
    env_units : constr; 		(* the [idx -> X:constr] *)
  }


  type sigma_maps = {
    sym_to_pos : int -> constr;
    bin_to_pos : int -> constr;
    units_to_pos : int -> constr;
  }

  (** infers some stuff that will be required when we will build
      environments (our environments need a default case, so we need
      an Op_AC, an Op_A, and a symbol) *)
  (* Note : this function can fail if the user is using the wrong
     relation, like proving a = b, while the classes are defined with
     another relation (==) *)
  let build_reif_params env sigma (rlt : Coq.Relation.t) (zero) :
        Evd.evar_map * reif_params =
    let carrier = rlt.Coq.Relation.carrier in
    let sigma,bin_null =
      try
        let sigma, op = Coq.evar_binary env sigma carrier in
	let sigma, assoc = Classes.Associative.infer env sigma rlt op in
	let sigma, compat = Classes.Proper.infer env sigma rlt op 2 in
	let op = Evarutil.nf_evar sigma op in
	  sigma,{
	    Bin.value = EConstr.to_constr sigma op;
	    Bin.compat = EConstr.to_constr sigma compat;
	    Bin.assoc = EConstr.to_constr sigma assoc;
	    Bin.comm = None;
	    Bin.idem = None
	  }
      with Not_found -> user_error @@ Pp.strbrk "Cannot infer a default A operator (required at least to be Proper and Associative)"
    in
    let sigma,zero =
      try
        let sigma, evar_op = Coq.evar_binary env sigma carrier in
	let sigma,evar_unit = Evarutil.new_evar env sigma carrier in
	let query = Classes.Unit.ty rlt evar_op evar_unit in
	let sigma, _ = Typeclasses.resolve_one_typeclass env sigma query in
	sigma,Evarutil.nf_evar sigma evar_unit
      with _ -> sigma,zero in
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
      sigma,record

  (** [build_sigma_maps] given a envs and some reif_params, we are
      able to build the sigmas *)
  let build_sigma_maps (rlt : Coq.Relation.t) zero ir : (sigmas * sigma_maps) Proofview.tactic =
    let open Proofview.Notations in
    Proofview.Goal.enter_one (fun goal ->
        let env = Proofview.Goal.env goal in
        let sigma = Proofview.Goal.sigma goal in
        let sigma,rp = build_reif_params env sigma rlt zero in
        Proofview.Unsafe.tclEVARS sigma
        <*> let env_sym = Sigma.of_list
                            rp.sym_ty
                            (rp.sym_null)
                            ir.sym
            in 
            Coq.mk_letin "env_sym" env_sym >>= fun env_sym ->
            let bin = (List.map ( fun (n,s) -> n, Bin.mk_pack rlt s) ir.bin) in
            let env_bin =
              Sigma.of_list
	        rp.bin_ty
	        (Bin.mk_pack rlt rp.bin_null)
	        bin
            in
            (* let goalE = Proofview.Goal.goal goal in *)
            Coq.mk_letin "env_bin" env_bin >>= fun env_bin ->
            let units = (List.map (fun (n,s) -> n, Unit.mk_pack rlt env_bin s)ir.units) in
            let env_units =
              Sigma.of_list
	        (Unit.ty_unit_pack rlt env_bin)
	        (Unit.mk_pack rlt env_bin rp.unit_null )
	        units
            in
            Coq.mk_letin "env_units" env_units >>= fun env_units ->
            let sigmas =
              {
	        env_sym =  env_sym ;
	        env_bin =  env_bin ;
	        env_units  = env_units;
              } in
            let f = List.map (fun (x,_) -> (x,Coq.Pos.of_int x)) in
            let sigma_maps =
              {
	        sym_to_pos = (let sym = f ir.sym in fun x ->  (List.assoc x sym));
	        bin_to_pos = (let bin = f bin in fun x ->  (List.assoc x bin));
	        units_to_pos = (let units = f units in fun x ->  (List.assoc  x units));
              }
            in
            Proofview.tclUNIT (sigmas, sigma_maps))

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

  let mk_vect vnil vcons v =
    let ar = Array.length v in
    let rec aux = function
      | 0 ->  vnil
      | n  -> let n = n-1 in
	  mkApp( vcons,
 		 [|
		   of_constr (Coq.Nat.of_int n);
		   v.(ar - 1 - n);
		   (aux (n))
		 |]
	       )
    in aux ar

  (* TODO: use a do notation *)
  let mk_reif_builders  (rlt: Coq.Relation.t)   (env_sym:constr) : (reif_builders Proofview.tactic) =
    let x = (rlt.Coq.Relation.carrier) in
    let r = (rlt.Coq.Relation.r) in

    let x_r_env = [|x;r;env_sym|] in
    let tty =  mkApp (Coq.get_efresh Stubs._Tty, x_r_env) in
    let rsum = mkApp (Coq.get_efresh Stubs.rsum, x_r_env) in
    let rprd = mkApp (Coq.get_efresh Stubs.rprd, x_r_env) in
    let rsym = mkApp (Coq.get_efresh Stubs.rsym, x_r_env) in
    let vnil = mkApp (Coq.get_efresh Stubs.vnil, x_r_env) in
    let vcons = mkApp (Coq.get_efresh Stubs.vcons, x_r_env) in
    let open Proofview.Notations in
    Coq.mk_letin "tty" tty >>= fun tty ->
    Coq.mk_letin "rsum" rsum >>= fun rsum ->
    Coq.mk_letin "rprd" rprd >>= fun rprd ->
    Coq.mk_letin "rsym" rsym >>= fun rsym ->
    Coq.mk_letin "vnil" vnil >>= fun vnil ->
    Coq.mk_letin "vcons" vcons >>= fun vcons ->
    Proofview.tclUNIT {
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
	        mkApp (Coq.get_efresh Stubs.runit , [|x;r;env_sym;idx; |])
      }



  type reifier = sigma_maps * reif_builders


  let  mk_reifier rlt zero envs : (sigmas *reifier) Proofview.tactic =
    let open Proofview.Notations in
    build_sigma_maps rlt zero envs >>= fun (s,sm) ->
    mk_reif_builders rlt s.env_sym >>= fun rb ->
      Proofview.tclUNIT (s,(sm,rb))


  (** [reif_constr_of_t reifier t] rebuilds the term [t] in the
      reified form. We use the [reifier] to minimise the size of the
      terms (we make as much lets as possible)*)
  let reif_constr_of_t (sm,rb) (t:Matcher.Terms.t) : constr =
    let rec aux = function
      | Matcher.Terms.Plus (s,l,r) ->
	  let idx = sm.bin_to_pos s  in
	    rb.rsum idx (aux l) (aux r)
      | Matcher.Terms.Dot (s,l,r) ->
	  let idx = sm.bin_to_pos s in
	    rb.rprd idx (aux l) (aux r)
      | Matcher.Terms.Sym (s,t) ->
	  let idx =  sm.sym_to_pos  s in
	    rb.rsym idx (Array.map aux t)
      | Matcher.Terms.Unit s ->
	  let idx = sm.units_to_pos s in
	    rb.runit idx
      | Matcher.Terms.Var i ->
	  anomaly "call to reif_constr_of_t on a term with variables."
    in aux t
end
