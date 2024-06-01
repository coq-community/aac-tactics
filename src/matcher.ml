(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

(** This module defines our matching functions, modulo associativity
    and commutativity (AAC).
   
    The basic idea is to find a substitution [env] such that the
    pattern [p] instantiated by [env] is equal to [t] modulo AAC.

    We proceed by structural decomposition of the pattern, and try all
    possible non-deterministic split of the subject when needed. The
    function {!matcher} is limited to top-level matching, that is, the
    subject must make a perfect match against the pattern ([x+x] do
    not match [a+a+b] ).  We use a search monad {!Search} to perform
    non-deterministic splits in an almost transparent way.  We also
    provide a function {!subterm} for finding a match that is a
    subterm modulo AAC of the subject. Therefore, we are able to solve
    the aforementioned case [x+x] against [a+b+a].

    This file is structured as follows. First, we define the search
    monad. Then,we define the two representations of terms (one
    representing the AST, and one in normal form ), and environments
    from variables to terms. Then, we use these parts to solve
    matching problem. Finally, we wrap this function {!matcher} into
    {!subterm}
*)


module Control =
struct
  let debug = false
  let time = false
  let printing = false
end

module Debug = Helper.Debug (Control)
open Debug

module Search = Search_monad 	(* a handle *)

type symbol = int
type var = int
type units = (symbol * symbol) list (* from AC/A symbols to the unit *)
type ext_units =
    {
      unit_for : units;
      is_ac : (symbol * bool) list
    } 	

exception NoUnit

let get_unit units op =
  try List.assoc op units
  with
    | Not_found -> raise NoUnit

let is_unit units op unit  = List.mem (op,unit) units


open Search

type 'a mset = ('a * int) list
let linear p =
  let rec ncons t l = function
    | 0 -> l
    | n -> t::ncons t l (n-1)
  in
  let rec aux = function
      [ ] -> []
    | (t,n)::q -> let q = aux q in
	ncons t q n
  in aux p

      

(** The module {!Terms} defines  two different types for expressions.
   
    - a public type {!Terms.t} that represent abstract syntax trees of
    expressions with binary associative (and commutative) operators

    - a private type {!Terms.nf_term} that represent an equivalence
    class for terms that are equal modulo AAC. The constructions
    functions on this type ensure the property that the term is in
    normal form (that is, no sum can appear as a subterm of the same
    sum, no trailing units, etc...).

*)

module Terms : sig

  (** {1 Abstract syntax tree of terms}

      Terms represented using this datatype are representation of the
      AST of an expression.  *)

  type t =
      Dot of (symbol * t * t)
    | Plus of (symbol * t * t)
    | Sym of (symbol * t array)
    | Var of var
    | Unit of symbol
	
  val equal_aac : units -> t -> t -> bool
  val size: t -> int

  (* permute symbols according to p *)
  val map_syms: (symbol -> symbol) -> t -> t

  (** {1 Terms in normal form}
     
      A term in normal form is the canonical representative of the
      equivalence class of all the terms that are equal modulo
      Associativity and Commutativity. Outside the {!Matcher} module,
      one does not need to access the actual representation of this
      type.  *)


  type nf_term = private
		 | TAC of  symbol * nf_term mset
		 | TA of   symbol * nf_term list
		 | TSym of symbol * nf_term list
		 | TUnit of symbol
		 | TVar of var

  (** {2 Constructors: we ensure that the terms are always
      normalised
     
      braibant  - Fri 27 Aug 2010, 15:11
      Moreover, we assure that we will not build empty sums or empty
      products, leaving this task to the caller function.
      }
  *)
  val mk_TAC : units -> symbol -> nf_term mset -> nf_term
  val mk_TA : units -> symbol -> nf_term list -> nf_term
  val mk_TUnit : symbol -> nf_term

  (** {2 Comparisons} *)
  val nf_term_compare : nf_term -> nf_term -> int
  val nf_equal : nf_term -> nf_term -> bool

  (** {2 Printing function}  *)
  val sprint_nf_term : nf_term -> string

  (** {2 Conversion functions}  *)
  val term_of_t : units -> t -> nf_term
  val t_of_term  : nf_term -> t 	(* we could return the units here *)
end
  = struct

    type t =
	Dot of (symbol * t * t)
      | Plus of (symbol * t * t)
      | Sym of (symbol * t array)
      | Var of var
      | Unit of symbol

    let rec size = function
      | Dot (_,x,y)
      | Plus (_,x,y) -> size x+ size y + 1
      | Sym (_,v)-> Array.fold_left (fun acc x -> size x + acc) 1 v
      | _ -> 1

    (* permute symbols according to p *)
    let rec map_syms p = function
      | Dot(s,u,v) -> Dot(p s, map_syms p u, map_syms p v)
      | Plus(s,u,v) -> Plus(p s, map_syms p u, map_syms p v)
      | Sym(s,u) -> Sym(p s, Array.map (map_syms p) u)
      | Unit s -> Unit(p s)
      | u -> u

    type nf_term =
      | TAC of  symbol * nf_term mset
      | TA of  symbol * nf_term list
      | TSym of symbol * nf_term  list
      | TUnit of symbol
      | TVar of var

    (** {2 Constructors: we ensure that the terms are always
	normalised} *)
      	
    (** {3 Pre constructors : These constructors ensure that sums and
	products are not degenerated (no trailing units)} *)
    let mk_TAC' units (s : symbol) l =  match l with
      | [] -> TUnit (get_unit units s )
      | [_,0] -> assert false
      | [t,1] -> t
      | _ ->  TAC (s,l)       
    let mk_TA' units  (s : symbol) l =   match l with
      | [] -> TUnit (get_unit units s )
      | [t] -> t
      | _ -> TA  (s,l)
	 

    (** {2 Comparison} *)

    let nf_term_compare = Stdlib.compare
    let nf_equal a b = 
      a = b

    (** [merge_ac comp l1 l2] merges two lists of terms with coefficients
	into one. Terms that are equal modulo the comparison function
	[comp] will see their arities added. *)
	 
    (* This function could be improved by the use of sorted msets *)
    let  merge_ac (compare : 'a -> 'a -> int) (l : 'a mset) (l' : 'a mset) : 'a mset =
      let rec aux l l'=
	match l,l' with
	  | [], _ -> l'
	  | _, [] -> l
	  | (t,tar)::q, (t',tar')::q' ->
	      begin match compare t t' with
		| 0 ->  ( t,tar+tar'):: aux q q'
		| -1 -> (t, tar):: aux q l'
		| _ -> (t', tar'):: aux l q'
	      end 
      in aux l l'

     (** [merge_map f l] uses the combinator [f] to combine the head of the
	 list [l] with the merge_maped tail of [l] *)
     let rec merge_map (f : 'a -> 'b list -> 'b list) (l : 'a list) : 'b list =
       match l with
	 | [] -> []
	 | t::q -> f t (merge_map f q)


     (** This function has to deal with the arities *)
     let merge (l : nf_term mset) (l' : nf_term mset) : nf_term mset=
       merge_ac nf_term_compare l l'

     let extract_A units s t =
       match t with
	 | TA (s',l) when s' = s -> l
	 | TUnit u when is_unit units s u -> []
	 | _ -> [t]

     let extract_AC units s (t,ar) : nf_term mset =
       match t with
	 | TAC (s',l) when s' = s -> List.map (fun (x,y) -> (x,y*ar)) l
	 | TUnit u when is_unit units s u  -> []
	 | _ -> [t,ar]


     (** {3 Constructors of {!nf_term}}*)
     let mk_TAC units (s : symbol) (l : (nf_term *int) list) =
       mk_TAC' units s	   
	 (merge_map (fun u l -> merge (extract_AC units s u) l) l)
     let mk_TA units s l = 
       mk_TA' units s
	 (merge_map (fun u l -> (extract_A units s u) @ l) l)
     let mk_TSym s l = TSym (s,l)
     let mk_TVar v = TVar v
     let mk_TUnit s = TUnit s


     (** {2 Printing function}  *)
     let print_binary_list (single : 'a -> string)
	 (unit : string) 
	 (binary : string -> string -> string) (l : 'a list) =
       let rec aux l =
	 match l with
	     [] -> unit
	   | [t] -> single t
	   | t::q ->
	       let r = aux q in
		 Printf.sprintf  "%s" (binary (single t) r)
       in
	 aux l

     let sprint_ac (single : 'a -> string) (l : 'a mset) =
       (print_binary_list
     	  (fun (x,t) ->
     	     if t = 1
     	     then single x
     	     else Printf.sprintf "%i*%s" t (single x)
     	  )
     	  "0"
     	  (fun x y -> x ^ " , " ^ y)
     	  l
       )

     let print_symbol single s l =
       match l with
	   [] ->  Printf.sprintf "%i" s
	 | _  ->
	     Printf.sprintf "%i(%s)"
	       s
	       (print_binary_list single "" (fun x y -> x ^ "," ^ y) l)


     let print_ac single s l =
       Printf.sprintf "[%s:AC]{%s}"
	 (string_of_int s )
	 (sprint_ac
	    single
	    l
	 )

     let print_a single s l =
       Printf.sprintf "[%s:A]{%s}"
	 (string_of_int s)
	 (print_binary_list single "1" (fun x y -> x ^ " , " ^ y) l)       

     let rec sprint_nf_term = function
       | TSym (s,l) -> print_symbol sprint_nf_term s l
       | TAC (s,l) -> print_ac sprint_nf_term s l
       | TA (s,l) -> print_a sprint_nf_term s l
       | TVar v -> Printf.sprintf "x%i" v
       | TUnit s ->  Printf.sprintf "unit%i" s




     (** {2 Conversion functions} *)

     (* rebuilds a tree out of a list, under the assumption that the list is not empty *)
     let binary_of_list f comb l =
       let l = List.rev l in
       let rec aux =    function
       | [] -> assert false
       | [t] -> f t
       | t::q -> comb (aux q) (f t)
       in
	 aux l

     let term_of_t units : t -> nf_term =
       let rec term_of_t = function
       | Dot (s,l,r) ->
	   let l = term_of_t l in
	   let r = term_of_t r in
	     mk_TA units s [l;r]
       | Plus (s,l,r) ->
	   let l = term_of_t l in
	   let r = term_of_t r in
	     mk_TAC units s [l,1;r,1]
       | Unit x ->
	   mk_TUnit x
       | Sym (s,t) ->
	   let t = Array.to_list t in
	   let t = List.map term_of_t t in 
	     mk_TSym s t
       | Var i ->
	   mk_TVar ( i)
       in
	 term_of_t

     let rec t_of_term  : nf_term -> t =  function
       | TAC (s,l) ->
	   (binary_of_list
	      t_of_term
	      (fun l r -> Plus ( s,l,r))
	      (linear l)
	   )
       | TA (s,l) ->
	   (binary_of_list
	      t_of_term
	      (fun l r -> Dot ( s,l,r))
	      l
	   )
       | TSym (s,l) ->
	   let v = Array.of_list l in
	   let v = Array.map (t_of_term) v in
	     Sym ( s,v)
       | TVar x -> Var x
       | TUnit s -> Unit s


     let equal_aac units x y =
       nf_equal (term_of_t units x) (term_of_t units y)
   end

 (** Terms environments defined as association lists from variables to
     terms in normal form {! Terms.nf_term} *)
 module Subst : sig
   type t

   val find : t -> var -> Terms.nf_term option
   val add : t -> var -> Terms.nf_term -> t
   val empty : t
   val instantiate : t -> Terms.t -> Terms.t
   val sprint : t -> string
   val to_list : t -> (var*Terms.t) list
 end
   = 
 struct
   open Terms

   (** Terms environments, with nf_terms, to avoid costly conversions
       of {!Terms.nf_terms} to {!Terms.t}, that will be mostly discarded*)
   type t = (var * nf_term) list

   let find : t -> var -> nf_term option = fun t x ->
     try Some (List.assoc x t) with | _ -> None
   let add t x v = (x,v) :: t
   let empty = []

   let sprint (l : t) =
     match l with
       | [] -> Printf.sprintf "Empty environment\n"
       | _ ->
	   let s = List.fold_left
	     (fun acc (x,y) ->
		Printf.sprintf "%sX%i -> %s\n"
		  acc
		  x
		  (sprint_nf_term y)
	     )
	     ""
	     (List.rev l) in
	     Printf.sprintf "%s\n%!" s



   (** [instantiate] is an homomorphism except for the variables*)
   let instantiate  (t: t) (x:Terms.t) : Terms.t =
     let rec aux = function
       | Unit _ as x -> x
       | Sym (s,t) -> Sym (s,Array.map aux t)
       | Plus (s,l,r) -> Plus (s, aux l, aux r)
       | Dot (s,l,r) -> Dot (s, aux l, aux r)
       | Var i -> 
	   begin match find t i  with
	     | None -> CErrors.user_err (Pp.strbrk "aac_tactics: instantiate failure")
	     | Some x -> t_of_term  x
	   end
     in aux x

   let to_list t = List.map (fun (x,y) -> x,Terms.t_of_term y) t
 end

 (******************)
 (* MATCHING UTILS *)
 (******************)

 open Terms

 (** Since most of the folowing functions require an extra parameter,
     the units, we package them in a module. This functor will then be
     applied to a module containing the units, in the exported
     functions.  *)
 module M (X : sig
   val units : units
   val is_ac : (symbol * bool) list
   val strict : bool 			(* variables cannot be instantiated with units *)
 end) = struct
  
   open X

   let mk_TAC s l = mk_TAC units s l
   let mk_TA s l = mk_TA units s l
   let mk_TAC' s l =
     try return( mk_TAC s l)
     with _ ->     fail ()
   let mk_TA' s l =
     try return( mk_TA s l)
     with _ -> fail ()

   (** First, we need to be able to perform non-deterministic choice of
       term splitting to satisfy a pattern. Indeed, we want to show that:
       (x+a*b)*c <= a*b*c
   *)
 let a_nondet_split_raw  t : ('a list * 'a list) m =
   let rec aux l l' =
     match l' with
       | [] ->
	   return ( l,[])
       | t::q ->
	   return (  l,l' )
	   >>| aux  (l @ [t]) q   
   in
     aux [] t

 (** Same as the previous [a_nondet_split], but split the list in 3
     parts *)
 let a_nondet_middle t : ('a list * 'a list * 'a list) m =
   a_nondet_split_raw t >>
     (fun (left, right) ->
	a_nondet_split_raw left >>
	  (fun (left, middle) -> return (left, middle, right))
     )

 (** Non deterministic splits of ac lists *)
 let dispatch f n =
   let rec aux k =
     if k = 0 then return (f n 0)
     else  return (f (n-k) k) >>| aux (k-1)
   in
     aux (n )

 let add_with_arith x ar l =
   if ar = 0 then l else (x,ar) ::l

 let ac_nondet_split_raw (l : 'a mset) :  ('a mset * 'a mset) m =
   let rec aux = function
     | [] -> return ([],[])
     | (t,tar)::q ->
	 aux q
	 >>
	   (fun (left,right) ->
	      dispatch (fun arl arr ->
			  add_with_arith t arl left,
			  add_with_arith t arr right
		       )
		tar
	   )
   in
     aux l
      
 let a_nondet_split  current t : (nf_term * nf_term list) m=
   a_nondet_split_raw t
   >>
     (fun (l,r) ->
	if strict && (l=[])
	then fail()
	else
	  mk_TA' current l >>
	    fun t -> return (t, r)
     )
    
 let ac_nondet_split  current t : (nf_term * nf_term mset) m=
   ac_nondet_split_raw t
   >>
     (fun (l,r) ->
	if strict && (l=[])
	then fail()
	else
	  mk_TAC' current l >>
	    fun t -> return (t, r)
     )

  
 (** Try to affect the variable [x] to each left factor of [t]*)
 let var_a_nondet_split  env current  x  t =
    a_nondet_split current t
   >>
     (fun (t,res) ->
	return ((Subst.add env x t), res)
     )

 (** Try to affect variable [x] to _each_ subset of t. *)
 let var_ac_nondet_split  (current: symbol) env (x : var) (t : nf_term mset) : (Subst.t * (nf_term mset)) m =
   ac_nondet_split  current t
   >>
     (fun (t,res) ->
	return ((Subst.add env x t), res)
     )

 (** See the term t as a given AC symbol. Unwrap the first constructor
     if necessary *)
 let get_AC (s : symbol) (t : nf_term) : (nf_term *int) list =
   match t with
     | TAC (s',l) when s' = s ->  l
     | TUnit u when is_unit units s u  -> []
     | _ ->  [t,1]

 (** See the term t as a given A symbol. Unwrap the first constructor
     if necessary *)
 let get_A (s : symbol) (t : nf_term) : nf_term list =
   match t with
     | TA (s',l) when s' = s ->  l
     | TUnit u when is_unit units s u -> []
     | _ -> [t]

 (** See the term [t] as an symbol [s]. Fail if it is not such
     symbol. *)
 let get_Sym s t =
   match t with
     | TSym (s',l) when s' = s -> return l
     | _ -> fail ()

 (*************)
 (* A Removal *)
 (*************)

 (** We remove the left factor v in a term list. This function runs
     linearly with respect to the size of the first pattern symbol *)

 let left_factor current (v : nf_term) (t : nf_term list) =
   let rec aux a b =
     match a,b with
       | t::q , t' :: q' when nf_equal t t' -> aux q q'
       | [], q -> return q
       | _, _ -> fail ()
   in
     match v with
       | TA (s,l) when s = current -> aux l t
       | TUnit u when is_unit units current u -> return t
       | _ ->
	   begin match t with
	     | [] -> fail ()
	     | t::q ->
		 if nf_equal v t
		 then return q
		 else  fail ()
	   end


 (**************)
 (* AC Removal *)
 (**************)

 (** {!pick_sym} gather all elements of a list that satisfies a
     predicate, and combine them with the residual of the list.  That
     is, each element of the residual contains exactly one element less
     than the original term.

     TODO : This function not as efficient as it could be, using a
     proper data-structure *)

 let pick_sym (s : symbol) (t : nf_term mset ) =
   let rec aux front back =
     match back with
       | [] -> fail ()
       | (t,tar)::q ->
	   begin match t with
	     | TSym (s',v') when s = s' ->
		 let back =
		   if tar > 1
		   then (t,tar -1) ::q
		   else q
		 in
		   return (v' , List.rev_append front back )
		   >>| aux ((t,tar)::front) q
	     | _ ->  aux ((t,tar)::front) q
	   end
   in
     aux [] t



 (** We have to check if we are trying to remove a unit from a term. Could also be located in Terms*)
 let  is_unit_AC s t =
   try nf_equal t (mk_TAC  s [])
   with | NoUnit -> false

 let is_same_AC s t : nf_term mset option=
   match t with
       TAC (s',l) when s = s' -> Some l
     | _ -> None

 (** We want to remove the term [v] from the term list [t] under an AC
     symbol *)
 let single_AC_factor (s : symbol) (v : nf_term) v_ar (t : nf_term mset) : (nf_term mset) m =
   let rec aux front back =
     match back with
       | [] -> fail ()
       | (t,tar)::q ->
	   begin
	     if nf_equal v t
	     then
	       match () with
		 | _ when tar < v_ar -> fail ()
		 | _ when tar = v_ar -> return (List.rev_append front q)
		 | _ -> return (List.rev_append front ((t,tar-v_ar)::q))
	     else
	       aux ((t,tar) :: front) q
	   end
   in
     if is_unit_AC s v
     then
       return t
     else
       aux [] t

 (* Remove a constant from a mset. If this constant is also a mset for
    the same symbol, we remove every elements, one at a time (and we do
    care of the arities) *)
 let factor_AC (s : symbol) (v: nf_term) (t : nf_term mset) : ( nf_term mset ) m =
   match is_same_AC s v with
     | None -> single_AC_factor s v 1 t
     | Some l ->
	 (* We are trying to remove an AC factor *)
	List.fold_left (fun acc (v,v_ar) ->
			  acc >> (single_AC_factor s v v_ar)
		       )
	  (return t)
	  l


(** [tri_fold f l acc] folds on the list [l] and give to f the
    beginning of the list in reverse order, the considered element, and
    the last part of the list

    as an exemple, on the list [1;2;3;4], we get the trace
    f () [] 1 [2; 3; 4]
    f () [1] 2   [3; 4]
    f () [2;1] 3   [ 4]
    f () [3;2;1] 4   []

    it is the duty of the user to reverse the front if needed
*)

let tri_fold f (l : 'a list) (acc : 'b)= match l with
    [] -> acc
  | _ ->
      let _,_,acc = List.fold_left (fun acc (t : 'a) ->
				      let l,r,acc = acc in
				      let r = List.tl r in
					t::l,r,f acc l t r
				   ) ([], l,acc) l
      in acc

(* let test = tri_fold (fun acc l t r -> (l,t,r) :: acc) [1;2;3;4] [] *)



		   (*****************************)
		   (* ENUMERATION DES POSITIONS *)
		   (*****************************)


(** The pattern is a unit: we need to try to make it appear at each
    position. We do not need to go further with a real matching, since
    the match should be trivial. Hence, we proceed recursively to
    enumerate all the positions. *)

module Positions = struct

  let a (l : 'a list) : ('a list * 'a * 'a list) m =
    let rec aux left right : ('a list * 'a * 'a list) m =
      match right with
	| [] -> assert false
	| [t] -> return (left,t,[])
	| t::q ->
	  aux (left@[t]) q
	  >>| return (left,t,q)
    in
    aux [] l
end

let build_ac (current : symbol) (context : nf_term mset) (p : t)  : t m= 
  if  context = []
  then return  p
  else
    mk_TAC' current context >>
      fun t -> return (Plus (current,t_of_term t,p))

let build_a (current : symbol)
    (left : nf_term list) (right : nf_term list) (p : t) : t m=
  let right_pat p =
    if right = []
    then return p
    else
      mk_TA' current right >>
	fun t -> return (Dot (current,p,t_of_term t))
  in
  let left_pat p=
    if left = []
    then return p
    else
      mk_TA' current left >>
	fun t -> return (Dot (current,t_of_term t,p))
  in  
  right_pat p >> left_pat >> (fun p -> return p)


let conts (hole : t) (l : symbol list) p : t m =
  let p = t_of_term p in
  (* - aller chercher les symboles ac et les symboles a
     - construire pour chaque
        *      *     +
       / \    / \   / \
      1   p  p   1 p   1
  *)
  let ac,a = List.partition (fun s -> List.assoc s is_ac) l   in
  let acc =   fail () in
  let acc = List.fold_left
    (fun acc s ->
      acc >>| return (Plus (s,p,hole))
    ) acc ac in
  let acc =
    List.fold_left
      (fun acc s ->
	acc >>| return (Dot (s,p,hole)) >>| return (Dot (s,hole,p))
      ) acc a
  in acc

   
(**
    Return the same thing as subterm :
    - The size of the context
    - The context
    - A collection of substitutions (here == return Subst.empty)
*)
let unit_subterm (t : nf_term) (unit : symbol) (hole : t): (int * t * Subst.t m) m =
  let symbols = List.fold_left
    (fun acc (ac,u) -> if u = unit then ac :: acc else acc ) [] units
  in
  (* make a unit appear at each strict sub-position of the term*)
  let rec positions  (t : nf_term) : t m =
    match t with
      (* with a final unit at the end *)
      | TAC (s,l) ->
	let symbols' = List.filter (fun x -> x <> s) symbols in
	(
	  ac_nondet_split_raw l >>
	    (fun (l,r) -> if l = [] || r = [] then fail () else
		(
		  match r with
		    | [p,1] ->
		      positions p >>| conts hole symbols' p
		    | _ ->
		      mk_TAC' s r >> conts hole symbols'
		) >> build_ac s l	  ))
      | TA (s,l) ->
	let symbols' = List.filter (fun x -> x <> s) symbols in
	(
	  (* first the other symbols, and then the more simple case of
	     this particular symbol *)
	  a_nondet_middle l >>
	    (fun (l,m,r) ->
	      (* meant to break the symmetry *)
	      if  (l = [] && r = [])
	      then fail ()
	      else
		(
		  match m with
		    | [p] ->
		      positions p >>| conts hole symbols' p
		    | _ ->
		      mk_TA' s m >> conts hole symbols'
		) >> build_a s l r   ))
	>>|
	    (
	      if List.mem s symbols then
		begin match l with
		  | [a] -> assert false
		  | [a;b] -> build_a s [a] [b] (hole)
		  | _ ->
		    (* on ne construit que les elements interieurs,
		       d'ou la disymetrie *)
		    (Positions.a l >>
		       (fun (left,p,right) ->
			 if left = [] then fail () else
			   (build_a s left right (Dot (s,hole,t_of_term p)))))
		end
	      else fail ()
	    )
	     
      | TSym (s,l) ->
	tri_fold (fun acc l t r ->
	  ((positions  t) >>
	      (fun (p) ->
		let l = List.map t_of_term l in
		let r = List.map t_of_term r in
		return (Sym (s, Array.of_list (List.rev_append l (p::r))))		  ))
	  >>|
	      (
		conts hole symbols t >>
		  (fun (p) ->
	      	    let l = List.map t_of_term l in
	      	    let r = List.map t_of_term r in
	      	    return (Sym (s, Array.of_list (List.rev_append l (p::r))))		  )
	      )
	  >>|  acc
	) l (fail())
      | TVar x -> assert false
      | TUnit x  when x = unit -> return (hole)
      | TUnit x as t -> conts hole symbols t
  in
  (positions t
   >>|
       (match t with
	 | TSym _ -> conts hole symbols t
	 | TAC (s,l)  -> conts hole symbols t
	 | TA (s,l)  -> conts hole symbols t
	 | _ -> fail())
  )
  >> fun (p) -> return (Terms.size p,p,return Subst.empty)
   



			    (************)
			    (* Matching *)
			    (************)

	 

(** {!matching} is the generic matching judgement.  Each time a
    non-deterministic split is made, we have to come back to this one.

    {!matchingSym} is used to match two applications that have the
    same (free) head-symbol.

    {!matchingAC} is used to match two sums (with the subtlety that
    [x+y] matches [f a] which is a function application or [a*b] which
    is a product).

    {!matchingA} is used to match two products (with the subtlety that
    [x*y] matches [f a] which is a function application, or [a+b]
    which is a sum).


*)

let matching  :  Subst.t  -> nf_term -> nf_term -> Subst.t Search.m=  
  let rec matching env (p : nf_term) (t: nf_term) : Subst.t Search.m=    
    match p with
      | TAC (s,l) ->
	  let l = linear l in
	    matchingAC env s l (get_AC s t)
      | TA (s,l) ->
	  matchingA env s l  (get_A s t)
      | TSym (s,l) ->
	  (get_Sym s t)
	  >> (fun t -> matchingSym env  l t)
      | TVar x  ->
	  begin match Subst.find env x with
	    | None -> return (Subst.add env x t)
	    | Some v -> if nf_equal v t  then return env else fail ()
	  end
      | TUnit s ->
	  if nf_equal p t then return env else fail ()
  and
      matchingAC (env : Subst.t) (current : symbol) (l : nf_term list) (t : (nf_term *int) list) =
    match l with
      | TSym (s,v):: q ->
	  pick_sym s t
	  >>   (fun (v',t') ->
		  matchingSym env v v'
		  >> (fun env -> matchingAC env current q t'))

      | TAC (s,v)::q when s = current -> 
	  assert false
      | TVar x:: q -> 			(* This is an optimization *)
	  begin match Subst.find env x with
	    | None ->
		(var_ac_nondet_split current env x t)
		>> (fun (env,residual) -> matchingAC env current q residual)
	    | Some v ->
		(factor_AC current v t)
		>> (fun residual -> matchingAC env current q residual)		
	  end	
      | TUnit s as v :: q -> 		(* this is an optimization *)
      	  (factor_AC current v t) >>
      	    (fun residual -> matchingAC env current q residual)
      | h :: q ->(*  PAC =/= curent or PA or unit for this symbol*)
	  (ac_nondet_split current t)
	  >>
	    (fun (t,right) ->
	       matching env h t
	       >>
		 (
		   fun env ->
		     matchingAC  env current q right
		 )
	    )   
      | [] -> if t = [] then return env else fail () 
  and
      matchingA (env : Subst.t) (current : symbol) (l : nf_term list) (t : nf_term list) =
    match l with
      | TSym (s,v) :: l ->
	  begin match t with
	    | TSym (s',v') :: r when s = s' ->
		(matchingSym env  v v')
		>> (fun env -> matchingA env current l r)
	    | _ -> fail ()
	  end
      | TA (s,v) :: l when s = current ->
	  assert false
      | TVar x :: l ->
	  begin match Subst.find env x with
	    | None ->
		debug (Printf.sprintf "var %i (%s)" x
			 (let b = Buffer.create 21 in List.iter (fun t -> Buffer.add_string b ( Terms.sprint_nf_term t)) t; Buffer.contents b  ));
		var_a_nondet_split  env current x t
		>> (fun (env,residual)-> debug (Printf.sprintf "pl %i %i" x(List.length residual)); matchingA env current l residual)
	    | Some v ->
		(left_factor current v t)
		>> (fun residual -> matchingA env current l residual)
	  end
      | TUnit s as v :: q -> 		(* this is an optimization *)
      	  (left_factor current v t) >>
      	    (fun residual -> matchingA env current q residual)
      | h :: l ->
	  a_nondet_split current t
	  >> (fun (t,r) ->
		matching env h t
		>> (fun env -> matchingA env current l r)
	     )
      | [] -> if t = [] then return env else fail ()
  and
      matchingSym (env : Subst.t) (l : nf_term list) (t : nf_term list) =
    List.fold_left2
      (fun acc p t -> acc >> (fun env -> matching env p t))
      (return env)
      l
      t

  in
    fun env l r ->
      let _ = debug (Printf.sprintf "pattern :%s\nterm    :%s\n%!" (Terms.sprint_nf_term l) (Terms.sprint_nf_term r)) in
      let m = matching env l r  in
      let _ = debug (Printf.sprintf "count %i" (Search.count m)) in
	m


(** [unitifiable p : Subst.t m] *)
let unitifiable p : (symbol * Subst.t m) m = 
  let m = List.fold_left 
    (fun acc (_,unit) -> acc >>| 
	let m =  matching Subst.empty p (mk_TUnit unit) in 
	if Search.is_empty m then 
	  fail ()
	else 
	  begin 
	    return (unit,m)
	  end
    ) (fail ()) units
  in 
  m
;;

let nullifiable p =
  let nullable = not strict in
  let has_unit s =
    try let _ = get_unit units s in true
    with NoUnit -> false 
  in
  let rec aux = function
    | TA (s,l) -> has_unit s && List.for_all (aux) l
    | TAC (s,l) -> has_unit s && List.for_all (fun (x,n) -> aux x) l
    | TSym _ -> false
    | TVar _ -> nullable
    | TUnit _ -> true
  in aux p

let unit_warning p ~nullif ~unitif =
  assert ((Search.is_empty unitif) || nullif);
  if not (Search.is_empty unitif)
  then
    begin
      Feedback.msg_warning
	(Pp.str
	   "[aac_tactics] This pattern can be instantiated to match units, some solutions can be missing");
    end

;;

  

  
(***********)
(* Subterm *)
(***********)



(** [subterm] solves a sub-term pattern matching.

    This function is more high-level than {!matcher}, thus takes {!t}
    as arguments rather than terms in normal form {!nf_term}.

    We use three mutually recursive functions {!subterm},
    {!subterm_AC}, {!subterm_A} to find the matching subterm, making
    non-deterministic choices to split the term into a context and an
    intersting sub-term. Intuitively, the only case in which we have to
    go in depth is when we are left with a sub-term that is atomic.

    Indeed, rewriting [H: b = c |- a+b+a = a+a+c], we do not want to
    find recursively the sub-terms of [a+b] and [b+a], since they will
    overlap with the sub-terms of [a+b+a].

    We rebuild the context on the fly, leaving the variables in the
    pattern uninstantiated. We do so in order to allow interaction
    with the user, to choose the env.

    Strange patterms like x*y*x can be instantiated by nothing, inside
    a product. Therefore, we need to check that all the term is not
    going into the context. With proper support for interaction with
    the user, we should lift these tests. However, at the moment, they
    serve as heuristics to return "interesting" matchings
*)

  let return_non_empty raw_p m =
    if is_empty m
    then
      fail ()
    else
      return (raw_p ,m)

  let subterm  (raw_p:t) (raw_t:t): (int * t * Subst.t m) m=
    let _ = debug (String.make 40 '=') in
    let p = term_of_t units raw_p in
    let t = term_of_t units raw_t in    
    let nullif = nullifiable p in 
    let unitif = unitifiable p in 
    let _ = unit_warning p ~nullif ~unitif in
    let _ = debug (Printf.sprintf "%s" (Terms.sprint_nf_term p)) in
    let _ = debug (Printf.sprintf "%s" (Terms.sprint_nf_term t)) in
    let filter_right current right (p,m) = 
      if right = []
      then return (p,m)
      else 
	mk_TAC' current right >>
	  fun t -> return (Plus (current,p,t_of_term t),m)
    in
    let filter_middle current left right (p,m) =
      let right_pat p =
	if right = []
	then return p
	else
	  mk_TA' current right >>
	    fun t -> return (Dot (current,p,t_of_term t))
      in
      let left_pat p=
	if left = []
	then return p
	else
	  mk_TA' current left >>
	    fun t -> return (Dot (current,t_of_term t,p))
      in  
      right_pat p >> left_pat >> (fun p -> return (p,m))
    in
    let rec subterm (t:nf_term) : (t * Subst.t m) m=
      match t with
	| TAC (s,l) ->
	  ((ac_nondet_split_raw l) >>
	      (fun (left,right) ->
		(subterm_AC s left) >> (filter_right s right)
	      ))
	| TA (s,l) ->
	  (a_nondet_middle l) >>
	    (fun (left, middle, right) ->
	      (subterm_A s middle) >>
		(filter_middle s left right)
	    )
	| TSym (s, l) ->
	  let init =
	    return_non_empty raw_p (matching  Subst.empty p t)
	  in
	  tri_fold (fun acc l t r ->
	    ((subterm  t) >>
		(fun (p,m) ->
		  let l = List.map t_of_term l in
		  let r = List.map t_of_term r in
		  let p = Sym (s, Array.of_list (List.rev_append l (p::r))) in
		  return (p,m)
		)) >>| acc
	  ) l init
	| TVar x -> assert false
	(* this case is superseded by the later disjunction *)
	| TUnit s -> fail () 		
	  
    and subterm_AC s tl   =
      match tl with
	  [x,1] -> subterm  x
	| _ ->
	  mk_TAC' s tl >> fun t ->
	    return_non_empty raw_p (matching  Subst.empty p t)
    and subterm_A s  tl =
      match tl with
	  [x] -> subterm  x
	| _ ->
	  mk_TA' s tl >>
	    fun t ->
	      return_non_empty raw_p (matching  Subst.empty p t)
    in
    match p with
      | TUnit unit -> unit_subterm t unit raw_p
      | _ when not (Search.is_empty unitif) ->
	let unit_matches = 
	  Search.fold 
	    (fun (unit,inst) acc -> 
	      Search.fold 
		(fun subst acc' ->
		 let m = unit_subterm t unit (Subst.instantiate subst raw_p) 
		 in 
		 m>>| acc'
		)
		inst
		acc      
	    ) 
	    unitif 
	    (fail ())
	in
	let nullifies (t : Subst.t) = 
	  List.for_all (fun (_,x) -> 
	    List.exists (fun (_,y) -> Unit y = x ) units 
	  ) (Subst.to_list t)
	in 
	let nonunit_matches = 
	  subterm t >> 
	    (
	      fun (p,m) -> 
		let m = Search.filter (fun subst -> not( nullifies subst)) m in 
		if Search.is_empty m 
		then fail ()
	      else return (Terms.size p,p,m)
	    )
	in
	  unit_matches >>| nonunit_matches  
	     
      | _ -> (subterm t >> fun (p,m) -> return (Terms.size p,p,m))


 end


(* The functions we export, handlers for the previous ones. Some debug
   information also *)
let subterm ?(strict = false) units raw t =
  let module M = M (struct
    let is_ac = units.is_ac
    let units = units.unit_for
    let strict = strict
  end) in
  let sols = time (M.subterm raw) t "%fs spent in subterm (including matching)\n" in
    debug
      (Printf.sprintf "%i possible solution(s)\n"
	 (Search.fold (fun (_,_,envm) acc -> count envm + acc) sols 0));
    sols


let matcher ?(strict = false) units p t =
  let module M = M (struct
    let is_ac = units.is_ac
    let units = units.unit_for
    let strict = false
  end) in
  let units = units.unit_for  in
  let sols = time
    (fun (p,t) ->
      let p = (Terms.term_of_t units p) in
      let t = (Terms.term_of_t units t) in
      M.matching  Subst.empty p t) (p,t)
    "%fs spent in the matcher\n"
  in
  debug (Printf.sprintf "%i solutions\n" (count sols));
  sols

