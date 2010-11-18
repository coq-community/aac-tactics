(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** Interface with Coq *)

type constr = Term.constr 

open Term
open Names
open Coqlib


(* The contrib name is used to locate errors when loading constrs *)
let contrib_name = "aac_tactics" 

(* Getting constrs (primitive Coq terms) from exisiting Coq
   libraries. *)
let find_constant contrib dir s =
  Libnames.constr_of_global (Coqlib.find_reference contrib dir s)

let init_constant dir s = find_constant contrib_name dir s

(* A clause specifying that the [let] should not try to fold anything
   in the goal *)
let nowhere = 
  { Tacexpr.onhyps = Some []; 
    Tacexpr.concl_occs = Rawterm.no_occurrences_expr 
  }


let mk_letin (name: string) (constr: constr) : constr * Proof_type.tactic =
  let name = (Names.id_of_string name) in
  let letin =
    (Tactics.letin_tac
       None
       (Name name)
       constr
       None 				(* or Some ty *)
       nowhere
    )  in
    mkVar name, letin

let mk_letin' (name: string) (constr: constr) : constr * Proof_type.tactic
   =
  constr, Tacticals.tclIDTAC



(** {2 General functions}  *)

type goal_sigma =  Proof_type.goal Tacmach.sigma 
let goal_update (goal : goal_sigma) evar_map : goal_sigma=
  let it = Tacmach.sig_it goal in 
    Tacmach.re_sig it evar_map 

let resolve_one_typeclass goal ty : constr*goal_sigma=
  let env = Tacmach.pf_env goal in 
  let evar_map = Tacmach.project goal in 
  let em,c = Typeclasses.resolve_one_typeclass env evar_map ty in 
    c, (goal_update goal em)

let nf_evar goal c : Term.constr= 
  let evar_map = Tacmach.project goal in 
    Evarutil.nf_evar evar_map c

let evar_unit (gl : goal_sigma) (rlt : constr * constr) : constr * goal_sigma = 
  let env = Tacmach.pf_env gl in 
  let evar_map = Tacmach.project gl in 
  let (em,x) = Evarutil.new_evar evar_map env (fst rlt) in 
    x,(goal_update gl em)
      
let evar_binary (gl: goal_sigma) (rlt: constr * constr) = 
  let env = Tacmach.pf_env gl in 
  let evar_map = Tacmach.project gl in 
  let x = fst rlt in 
  let ty = mkArrow x (mkArrow x x) in 
  let (em,x) = Evarutil.new_evar evar_map env  ty in 
    x,( goal_update gl em)

(* decomp_term :  constr -> (constr, types) kind_of_term *)
let decomp_term c = kind_of_term (strip_outer_cast c)
    

(** {2 Bindings with Coq' Standard Library}  *)
  
module Pair = struct
  
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "prod")
  let pair = lazy (init_constant path "pair")
end
    
module Pos = struct
    
    let path = ["Coq" ; "PArith"; "BinPos"]
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
  let path = ["Coq"; "Lists"; "List"]
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

  (** build the constr [Proper rel t] *)
  let mk_morphism ty rel t =
    mkApp (Lazy.force morphism, [| ty; rel; t|])

  let equivalence = lazy (init_constant (classes_path@ ["RelationClasses"]) "Equivalence")

  (** build the constr [Equivalence ty rel]  *)
  let mk_equivalence ty rel =
    mkApp (Lazy.force equivalence, [| ty; rel|])
end

(** a [mset] is a ('a * pos) list *)
let mk_mset ty (l : (constr * int) list) = 
  let pos = Lazy.force Pos.typ in 
  let pair_ty = mkApp (Lazy.force Pair.typ , [| ty; pos|]) in 
  let pair (x : constr) (ar : int) =
    mkApp (Lazy.force Pair.pair, [| ty ; pos ; x ; Pos.of_int ar|]) in 
  let rec aux = function 
    | [] -> List.nil pair_ty
    | (t,ar)::q -> List.cons pair_ty (pair t ar) (aux q)   
  in
    aux l

(** x r  *)
type reltype = Term.constr * Term.constr
(** x r e *)
type eqtype = reltype * Term.constr


(** {1 Tacticals}  *)

let tclTIME msg tac = fun gl ->
  let u = Sys.time () in 
  let r = tac gl in 
  let _ = Pp.msgnl (Pp.str (Printf.sprintf "%s:%fs" msg (Sys.time ()-.  u))) in 
    r

let tclDEBUG msg tac = fun gl ->
  let _ = Pp.msgnl (Pp.str msg) in 
    tac gl

let tclPRINT  tac = fun gl ->
  let _ = Pp.msgnl (Printer.pr_constr (Tacmach.pf_concl gl)) in
    tac gl

