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

let ac_theory_path = ["AAC"]

module Sigma = struct
  let sigma = lazy (Coq.init_constant ac_theory_path "sigma")
  let sigma_empty = lazy (Coq.init_constant ac_theory_path "sigma_empty")
  let sigma_add = lazy (Coq.init_constant ac_theory_path "sigma_add")
  let sigma_get = lazy (Coq.init_constant ac_theory_path "sigma_get")
    
  let add ty n x map = 
    mkApp (Lazy.force sigma_add,[|ty; n; x ;  map|])
  let empty ty =
    mkApp (Lazy.force sigma_empty,[|ty |])
  let typ ty = 
    mkApp (Lazy.force sigma, [|ty|])

  let to_fun ty null map = 
    mkApp (Lazy.force sigma_get, [|ty;null;map|])

  let of_list ty null l =
    let map =
      List.fold_left 
	(fun acc (i,t) -> assert (i > 0); add ty (Coq.Pos.of_int i) t acc) 
	(empty ty)
	l
    in to_fun ty null map 
end


module Sym = struct
  type pack = {ar: Term.constr; value: Term.constr ; morph: Term.constr}
  
  let path = ac_theory_path @ ["Sym"]
  let typ = lazy (Coq.init_constant path "pack")
  let mkPack = lazy (Coq.init_constant path "mkPack")
  let typeof = lazy (Coq.init_constant path "type_of") 
  let relof = lazy (Coq.init_constant path "rel_of") 
  let value = lazy (Coq.init_constant path "value")
  let null = lazy (Coq.init_constant path "null")
  let mk_typeof :  Coq.reltype -> int -> constr = fun (x,r) n ->
    mkApp (Lazy.force typeof, [| x ; Coq.Nat.of_int n |]) 
  let mk_relof :  Coq.reltype -> int -> constr = fun (x,r) n ->
    mkApp (Lazy.force relof, [| x;r ; Coq.Nat.of_int n |]) 
  let mk_pack ((x,r): Coq.reltype) s = 
    mkApp (Lazy.force mkPack, [|x;r; s.ar;s.value;s.morph|])
  let null eqt witness = 
    let (x,r),e = eqt in 
      mkApp (Lazy.force null, [| x;r;e;witness |])
	
end

module Sum = struct
  type pack = {plus: Term.constr; zero: Term.constr ; opac: Term.constr}

  let path = ac_theory_path @ ["Sum"]
  let typ = lazy (Coq.init_constant path "pack")
  let mkPack = lazy (Coq.init_constant path "mkPack")
  let cstr_zero = lazy (Coq.init_constant path "zero")
  let cstr_plus = lazy (Coq.init_constant path "plus")
    
  let mk_pack: Coq.reltype -> pack -> Term.constr = fun (x,r) s ->
    mkApp (Lazy.force mkPack , [| x ; r; s.plus; s.zero; s.opac|])
      
  let zero: Coq.reltype -> constr -> constr = fun (x,r) pack ->
    mkApp (Lazy.force cstr_zero, [| x;r;pack|])
  let plus: Coq.reltype -> constr -> constr = fun (x,r) pack ->
    mkApp (Lazy.force cstr_plus, [| x;r;pack|])


end

module Prd = struct
  type pack = {dot: Term.constr; one: Term.constr ; opa: Term.constr}

  let path = ac_theory_path @ ["Prd"]
  let typ = lazy (Coq.init_constant path "pack")
  let mkPack = lazy (Coq.init_constant path "mkPack")
  let cstr_one = lazy (Coq.init_constant path "one")
  let cstr_dot = lazy (Coq.init_constant path "dot")
    
  let mk_pack: Coq.reltype -> pack -> Term.constr = fun (x,r) s ->
    mkApp (Lazy.force mkPack , [| x ; r; s.dot; s.one; s.opa|])
  let one: Coq.reltype -> constr -> constr = fun (x,r) pack ->
    mkApp (Lazy.force cstr_one, [| x;r;pack|])
  let dot: Coq.reltype -> constr -> constr = fun (x,r) pack ->
    mkApp (Lazy.force cstr_dot, [| x;r;pack|])


end

  
let op_ac = lazy (Coq.init_constant ac_theory_path "Op_AC")
let op_a = lazy (Coq.init_constant ac_theory_path "Op_A")
  
(** The constants from the inductive type *)
let _Tty = lazy (Coq.init_constant ac_theory_path "T") 
let vTty = lazy (Coq.init_constant ac_theory_path "vT") 
  
let rsum = lazy (Coq.init_constant ac_theory_path "sum") 
let rprd = lazy (Coq.init_constant ac_theory_path "prd") 
let rsym = lazy (Coq.init_constant ac_theory_path "sym") 
let vnil = lazy (Coq.init_constant ac_theory_path "vnil") 
let vcons = lazy (Coq.init_constant ac_theory_path "vcons") 
let eval = lazy (Coq.init_constant ac_theory_path "eval")
let decide_thm = lazy (Coq.init_constant ac_theory_path "decide")

(** Rebuild an equality   *)
let mk_equal = fun (x,r) left right ->
  mkApp (r, [| left; right|]) 


let anomaly msg = 
  Util.anomaly ("aac_tactics: " ^ msg)

let user_error msg = 
  Util.error ("aac_tactics: " ^ msg)


module Trans = struct
  

  (** {1 From Coq to Abstract Syntax Trees (AST)}
      
      This module provides facilities to interpret a Coq term with
      arbitrary operators as an abstract syntax tree. Considering an
      application, we try to infer instances of our classes. We
      consider that raw morphisms ([Sym]) are coarser than [A]
      operators, which in turn are coarser than [AC] operators.  We
      need to treat the units first. Indeed, considering [S] as a
      morphism is problematic because [S O] is a unit.  
      
      During this reification, we gather some informations that will
      be used to rebuild Coq terms from AST ( type {!envs}) *)

  type pack = 
    | AC of Sum.pack 		(* the opac pack *)
    | A of Prd.pack 		(* the opa pack *)
    | Sym of Sym.pack       	(* the sym pack *)

  type head =
    | Fun  
    | Plus 
    | Dot  
    | One  
    | Zero


  (* discr is a map from {!Term.constr} to
     (head * pack).
     
     [None] means that it is not possible to instantiate this partial
     application to an interesting class.

     [Some x] means that we found something in the past. This means in
     particular that a single constr cannot be two things at the same
     time.
     
     However, for the transitivity process, we do not need to remember
     if the constr was the unit or the binary operation. We will use
     the projections from the module's record.
     
     The field [bloom] allows to give a unique number to each class we
     found.  *)
  type envs = 
      {
	discr : (constr , (head * pack) option) Hashtbl.t ; 
	
	bloom : (pack, int ) Hashtbl.t; 
	bloom_back  : (int, pack ) Hashtbl.t;
	bloom_next : int ref;
      }

  let empty_envs () = 
    {
      discr = Hashtbl.create 17;

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


  (** try to infer the kind of operator we are dealing with *)
  let is_morphism  rlt papp ar goal =
    let typeof = Sym.mk_typeof rlt ar in 
    let relof = Sym.mk_relof rlt ar in 
    let env = Tacmach.pf_env goal in 
    let evar_map = Tacmach.project goal in 
    let m = Coq.Classes.mk_morphism  typeof relof  papp in
      try 
	let _ = Tacmach.pf_check_type goal papp typeof in 
	let evar_map,m = Typeclasses.resolve_one_typeclass env evar_map m in
	let pack = {Sym.ar = (Coq.Nat.of_int ar); Sym.value= papp; Sym.morph= m} in 
	  Some (Coq.goal_update goal evar_map, Fun , Sym pack) 
      with 
	| Not_found ->  None
	| _ ->  None
	    
  (** gives back the class  *)
  let is_op gl (rlt: Coq.reltype) pack op null = 
    let (x,r) = rlt in 
    let ty = mkApp (pack ,[|x;r; op; null |]) in
    let env = Tacmach.pf_env gl in 
    let evar_map = Tacmach.project gl in 
      try 
	let em,t = Typeclasses.resolve_one_typeclass env evar_map ty in
	let op = Evarutil.nf_evar em op in 
	let null = Evarutil.nf_evar em null in 
	  Some (Coq.goal_update gl em,t,op,null)
      with Not_found -> None


  let is_plus  (rlt: Coq.reltype) plus goal=
    let (zero,goal) = Coq.evar_unit goal rlt in
      match is_op goal rlt (Lazy.force op_ac) plus zero
      with
	| None -> None
	| Some (gl,s,plus,zero) -> 
	    let pack = {Sum.plus=plus;Sum.zero=zero;Sum.opac=s} in 
	      Some (gl, Plus , AC pack)

  let is_dot rlt dot goal=
    let (one,goal) = Coq.evar_unit goal rlt in
      match is_op goal rlt (Lazy.force op_a) dot one
      with
	| None -> None
	| Some (goal,s,dot,one) -> 
	    let pack = {Prd.dot=dot;Prd.one=one;Prd.opa=s} in 
	      Some (goal, Dot,  A pack)

  let is_zero rlt zero goal =
    let (plus,goal) = Coq.evar_binary goal rlt in
      match is_op goal rlt (Lazy.force op_ac) plus zero
      with
	| None -> None
	| Some (goal,s,plus,zero) -> 
	    let pack = {Sum.plus=plus;Sum.zero=zero;Sum.opac=s} in 
	      Some (goal, Zero , AC pack)

  let is_one  rlt one goal =
    let (dot,goal) = Coq.evar_binary goal rlt in
      match is_op goal rlt (Lazy.force op_a) dot one
      with 
	| None -> None 
	| Some (goal,s,dot,one)-> 
	    let pack = {Prd.dot=dot;Prd.one=one;Prd.opa=s} in 
	      Some (goal, One, A pack)


  let (>>) x y a =
    match x a with | None -> y a | x -> x

  let is_unit rlt papp =
    (is_zero rlt papp )>> (is_one rlt papp)
	
  let what_is_it rlt papp ar goal : 
      (Coq.goal_sigma * head * pack ) option =
    match ar  with 
      | 2 -> 
	  begin
	    (
	      (is_plus rlt papp)>>
		(is_dot rlt papp)>>
		(is_morphism rlt papp ar)
	    )	goal
	  end
      | _ -> 
	  is_morphism rlt papp ar goal

    

	
  (** [discriminates goal envs rlt t ca] infer :
      
      - the nature of the application [t ca] (is the head symbol a
      Plus, a Dot, so on), 

      - its {! pack } (is it an AC operator, or an A operator, or a
      Symbol ?),

      - the relevant partial application,

      - the vector of the remaining arguments

      We use an expansion to handle the special case of units, before
      going back to the general discrimination procedure *)
  let discriminate goal envs (rlt : Coq.reltype) t ca : Coq.goal_sigma * head * pack * constr * constr array =   
    let nb_params = Array.length ca in
    let f cont x p_app ar = 
      assert (0 <= ar && ar <= nb_params);
      match x with
	| Some (goal, discr, pack) -> 
	    Hashtbl.add envs.discr p_app (Some (discr, pack));
	    add_bloom envs pack;
	    (goal, discr, pack, p_app, Array.sub ca (nb_params-ar) ar)
	| None -> 
	    begin
	      (* to memoise the failures *)
	      Hashtbl.add envs.discr p_app None;
	      (* will terminate, since [const] is
		 capped, and it is easy to find an
		 instance of a constant *)
	      cont goal (ar-1)
	    end
    in
    let rec aux goal ar :Coq.goal_sigma * head * pack * constr * constr array = 
      assert (0 <= ar && ar <= nb_params);
      let p_app = mkApp (t, Array.sub ca 0 (nb_params - ar)) in 	
	begin	
	  try 
	    begin match Hashtbl.find envs.discr p_app with 
	      | None -> aux goal  (ar-1)
	      | Some (discr,sym) -> 
		  goal,
		  discr, 
		  sym, 
		  p_app, 
		  Array.sub ca (nb_params -ar ) ar
	    end
	  with
	      Not_found -> (* Could not find this constr *)		
		f aux (what_is_it rlt p_app ar goal) p_app ar
	end
    in
      match is_unit rlt (mkApp (t,ca)) goal with 
	| None -> aux goal (nb_params)
	| x ->  f (fun _ -> assert false) x (mkApp (t,ca)) 0

  let discriminate goal envs rlt  x =
    try 
      match Coq.decomp_term x with 
	| Var _ -> 
	    discriminate goal envs rlt  x [| |]		
	| App (t,ca) -> 
	    discriminate goal envs rlt   t ca
	| Construct c ->  
	    discriminate goal envs rlt  x [| |]		
	| _ -> 
	    assert false
    with 
	(* TODO: is it the only source of invalid use that fall into
	   this catch_all ? *)
	e -> user_error "cannot handle this kind of hypotheses (higher order function symbols, variables occuring under a non-morphism, etc)."


  (** [t_of_constr goal rlt envs cstr] builds the abstract syntax
      tree of the term [cstr]. Doing so, it modifies the environment
      of known stuff [envs], and eventually creates fresh
      evars. Therefore, we give back the goal updated accordingly *)
  let t_of_constr goal (rlt: Coq.reltype ) envs  : constr -> Matcher.Terms.t *Coq.goal_sigma =
    let r_evar_map = ref (goal) in 
    let rec aux x = 
      match Coq.decomp_term x with 
	| Rel i -> Matcher.Terms.Var i
	| _ -> 
	    let goal, sym, pack , p_app, ca = discriminate (!r_evar_map) envs rlt   x in 
	      r_evar_map := goal;
	      let k = find_bloom envs pack
	      in 
		match sym with 
		  | Plus ->
		      assert (Array.length ca = 2);
		      Matcher.Terms.Plus ( k, aux ca.(0), aux ca.(1))
		  | Zero  -> 
		      assert (Array.length ca = 0);
		      Matcher.Terms.Zero ( k)
		  | Dot  -> 
		      assert (Array.length ca = 2);			  
		      Matcher.Terms.Dot ( k, aux ca.(0), aux ca.(1))
		  | One  -> 
		      assert (Array.length ca = 0);
		      Matcher.Terms.One ( k)
		  | Fun  ->
		      Matcher.Terms.Sym ( k, Array.map aux ca)		
    in 
      (
	fun x -> let r = aux x in r,  !r_evar_map 
      ) 
	
  (** {1 From AST back to Coq }
      
      The next functions allow one to map OCaml abstract syntax trees
      to Coq terms *)

 (** {2 Building raw, natural, terms} *)

  (** [raw_constr_of_t] rebuilds a term in the raw representation *)
  let raw_constr_of_t envs (rlt : Coq.reltype)  (t : Matcher.Terms.t) : Term.constr =
    let add_set,get = 
      let r = ref [] in 
      let rec add x = function 
	  [ ] -> [x]
	| t::q when t = x -> t::q
	| t::q -> t:: (add x q) 
      in 
	(fun x -> r := add x !r),(fun () -> !r)
    in
    let rec aux t =
      match t with 
	| Matcher.Terms.Plus (s,l,r) ->
	    begin match Hashtbl.find envs.bloom_back s with 
	      | AC s -> 
		  mkApp (s.Sum.plus ,  [|(aux l);(aux r)|])
	      | _ -> assert false
	    end
	| Matcher.Terms.Dot (s,l,r) ->
	    begin match Hashtbl.find envs.bloom_back s with 
	      | A s -> 
		  mkApp (s.Prd.dot,  [|(aux l);(aux r)|])
	      | _ -> assert false
	    end
	| Matcher.Terms.Sym (s,t) ->
	    begin match Hashtbl.find envs.bloom_back s with 
	      | Sym s -> 
		  mkApp (s.Sym.value, Array.map aux t)
	      | _ -> assert false
	    end
	| Matcher.Terms.One x ->
	    begin match Hashtbl.find envs.bloom_back x with 
	      | A s -> 
		  s.Prd.one
	      | _ -> assert false
	    end
	| Matcher.Terms.Zero  x ->
	    begin match Hashtbl.find envs.bloom_back x with 
	      | AC s -> 
		  s.Sum.zero 
	      | _ -> assert false
	    end
	| Matcher.Terms.Var i -> add_set i;
	    let i = (Names.id_of_string (Printf.sprintf "x%i" i)) in 
	      mkVar (i)
    in 
    let x = fst rlt in 
    let rec cap c = function [] -> c
      | t::q ->  let i = (Names.id_of_string (Printf.sprintf "x%i" t)) in 
	  cap (mkNamedProd i x c) q
    in
      cap ((aux t)) (get ())
	(* aux t is possible for printing only, but I wonder what
	   would be the status of such a term*)
	

  (** {2 Building reified terms} *)
	
  (* Some informations to be able to build the maps  *)
  type reif_params = 
      {
	a_null : constr;
	ac_null : constr;	
	sym_null : constr;
	a_ty : constr;
	ac_ty : constr;	
	sym_ty : constr;
      }

 type sigmas = {
    env_sym : Term.constr;
    env_sum : Term.constr;
    env_prd : Term.constr;
  }
  (** A record containing the environments that will be needed by the
      decision procedure, as a Coq constr. Contains also the functions
      from the symbols (as ints) to indexes (as constr) *)
  type sigma_maps = {
    sym_to_pos : int -> Term.constr;
    sum_to_pos : int -> Term.constr;
    prd_to_pos : int -> Term.constr;
  }

  (* convert the [envs] into the [sigma_maps] *)
  let envs_to_list rlt envs = 
    let add x y (n,l) = (n+1, (x, ( n, y))::l) in 
    let  nil = 1,[]in 
      Hashtbl.fold 
	(fun int pack (sym,sum,prd) -> 
	   match pack with 
	     |AC s -> 
		let s = Sum.mk_pack rlt s in 
		  sym, add (int) s sum, prd
	     |A s -> 
		let s = Prd.mk_pack rlt s in 
		  sym, sum, add (int) s prd
	     | Sym s ->
		 let s = Sym.mk_pack rlt s in 
		   add (int) s sym, sum, prd
	)  
	envs.bloom_back  
	(nil,nil,nil)



  (** infers some stuff that will be required when we will build
      environments (our environments need a default case, so we need
      an Op_AC, an Op_A, and a symbol) *)

  (* Note : this function can fail if the user is using the wrong
     relation, like proving a = b, while the classes are defined with
     another relation (==) 
  *)
  let build_reif_params goal eqt = 
    let rlt = fst eqt in 
    let  plus,goal = Coq.evar_binary goal rlt in 
    let  dot ,goal =  Coq.evar_binary goal rlt in 
    let  one ,goal = Coq.evar_unit goal rlt in 
    let  zero,goal  =  Coq.evar_unit goal rlt in  

    let (x,r) = rlt in 
    let ty_ac = ( mkApp (Lazy.force op_ac, [| x;r;plus;zero|])) in
    let ty_a = ( mkApp (Lazy.force op_a, [| x;r;dot;one|])) in
    let a  ,goal= 
      try Coq.resolve_one_typeclass goal ty_a 
      with Not_found -> user_error ("Unable to infer a default A operator.") 
    in
    let ac ,goal= 
      try Coq.resolve_one_typeclass goal ty_ac 
      with Not_found ->  user_error ("Unable to infer a default AC operator.")
    in 
    let plus = Coq.nf_evar goal plus  in 
    let dot =  Coq.nf_evar goal dot  in 
    let one =  Coq.nf_evar goal one  in 
    let zero = Coq.nf_evar goal zero  in 

    let record = 
      {a_null = Prd.mk_pack rlt {Prd.dot=dot;Prd.one=one;Prd.opa=a};
       ac_null= Sum.mk_pack rlt {Sum.plus=plus;Sum.zero=zero;Sum.opac=ac}; 
       sym_null = Sym.null eqt zero;
       a_ty   = (mkApp (Lazy.force Prd.typ, [| x;r; |]));
       ac_ty = ( mkApp (Lazy.force Sum.typ, [| x;r|])); 
       sym_ty =  mkApp (Lazy.force Sym.typ, [|x;r|])
      } 
    in 
      goal,     record

  (** [build_sigma_maps] given a envs and some reif_params, we are
      able to build the sigmas *)
  let build_sigma_maps goal eqt envs : sigmas * sigma_maps *  Proof_type.goal Evd.sigma =
    let rlt = fst eqt in 
    let goal,rp = build_reif_params goal eqt in 
    let ((_,sym), (_,sum),(_,prd)) = envs_to_list rlt envs in 
    let f = List.map (fun (x,(y,z)) -> (x,Coq.Pos.of_int y)) in 
    let g = List.map (fun (x,(y,z)) -> (y,z)) in 
    let sigmas = 
      {env_sym = Sigma.of_list rp.sym_ty rp.sym_null (g sym);
       env_sum = Sigma.of_list rp.ac_ty rp.ac_null (g sum);
       env_prd = Sigma.of_list rp.a_ty rp.a_null (g prd);
      } in 
    let sigma_maps = { 
      sym_to_pos = (let sym = f sym in fun x ->  (List.assoc x sym));
      sum_to_pos = (let sum = f sum in fun x ->  (List.assoc x sum));
      prd_to_pos = (let prd = f prd in fun x ->  (List.assoc x prd));
    }
    in 
      sigmas, sigma_maps , goal 
	


  (** builders for the reification *)
  type reif_builders =
      {
	rsum: constr -> constr -> constr -> constr;
	rprd: constr -> constr -> constr -> constr;
	rzero: constr -> constr;
	rone: constr -> constr;
	rsym: constr -> constr array -> constr
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
		   (Coq.Nat.of_int n);
		   v.(ar - 1 - n);
		   (aux (n))
		 |]	
	       )
    in aux ar
	 
  (* TODO: use a do notation *)
  let mk_reif_builders  (rlt: Coq.reltype)   (env_sym:constr)  :reif_builders*Proof_type.tactic =
    let x,r = rlt in 
    let tty =  mkApp (Lazy.force _Tty, [| x ; r ; env_sym|]) in 
      (Coq.mk_letin'  "mk_rsum" (mkApp (Lazy.force rsum, [| x; r;  env_sym|]))) >>
      (fun rsum -> (Coq.mk_letin' "mk_rprd" (mkApp (Lazy.force rprd, [| x; r; env_sym|]))) 
	 >> fun rprd -> ( Coq.mk_letin' "mk_rsym" (mkApp (Lazy.force rsym, [| x;r; env_sym|]))) 
	   >> fun rsym -> (Coq.mk_letin' "mk_vnil" (mkApp (Lazy.force vnil, [| x;r; env_sym|])))
	     >> fun vnil -> Coq.mk_letin' "mk_vcons" (mkApp (Lazy.force vcons, [| x;r; env_sym|]))	
	       >> fun vcons ->     
		 return {
		   rsum = 
		     begin fun idx l r ->
		       mkApp (rsum, [|  idx ; Coq.mk_mset tty [l,1 ; r,1]|])
		     end;
		   rzero =
		     begin fun idx  ->  
		       mkApp (rsum, [|  idx ; Coq.mk_mset tty []|]) 
		     end;
		   rprd = 
		     begin fun idx l r ->
		       let lst = Coq.List.of_list tty [l;r] in
			 mkApp (rprd, [| idx; lst|]) 
		     end;
		   rone =   
		     begin fun idx ->
		       let lst = Coq.List.of_list tty [] in 
			 mkApp (rprd, [| idx; lst|]) end;
		   rsym = 
		     begin fun idx v ->
		       let vect = mk_vect vnil vcons  v in
			 mkApp (rsym, [| idx; vect|])
		     end;
		 }
      )
      


  type reifier = sigma_maps * reif_builders

  let  mk_reifier eqt envs goal :  sigmas * reifier * Proof_type.tactic = 
    let s, sm, goal = build_sigma_maps goal eqt envs in 
    let env_sym, env_sym_letin = Coq.mk_letin "env_sym_name" (s.env_sym) in 
    let env_prd, env_prd_letin = Coq.mk_letin "env_prd_name" (s.env_prd) in 
    let env_sum, env_sum_letin = Coq.mk_letin "env_sum_name" (s.env_sum) in
    let s = {env_sym = env_sym; env_prd = env_prd; env_sum = env_sum} in 
    let rb , tac = mk_reif_builders (fst eqt) (s.env_sym) in 
    let evar_map = Tacmach.project goal in
    let tac = Tacticals.tclTHENLIST (
      [		       Refiner.tclEVARS evar_map;
		       env_prd_letin ;
		       env_sum_letin ;
		       env_sym_letin ;
		       tac
      ]) in 
      s, (sm, rb), tac
	
	
  (** [reif_constr_of_t reifier t] rebuilds the term [t] in the
      reified form. We use the [reifier] to minimise the size of the
      terms (we make as much lets as possible)*)
  let reif_constr_of_t (sm,rb) (t:Matcher.Terms.t) : constr =
    let rec aux = function
      | Matcher.Terms.Plus (s,l,r) ->
	  let idx = sm.sum_to_pos s  in
	    rb.rsum idx (aux l) (aux r) 
      | Matcher.Terms.Dot (s,l,r) ->
	  let idx = sm.prd_to_pos s in 
	    rb.rprd idx (aux l) (aux r) 
      | Matcher.Terms.Sym (s,t) ->
	  let idx =  sm.sym_to_pos  s in 
	    rb.rsym idx (Array.map aux t)
      | Matcher.Terms.One s ->
	  let idx = sm.prd_to_pos s in 
	    rb.rone idx
      | Matcher.Terms.Zero s ->
	  let idx = sm.sum_to_pos s in 
	    rb.rzero idx
      | Matcher.Terms.Var i -> 
	  anomaly "call to reif_constr_of_t on a term with variables."
    in aux t


end



