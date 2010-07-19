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


let debug = false
let time = false   


let time f x fmt =
  if time then 
    let t = Sys.time() in
    let r = f x in
      Printf.printf fmt  (Sys.time () -. t);
      r
  else f x 



type symbol = int
type var = int


(****************)
(* Search Monad *)
(****************)


(** The {!Search} module contains a search monad that allows to
    express, in a legible maner, programs that solves combinatorial
    problems 

    @see <http://spivey.oriel.ox.ac.uk/mike/search-jfp.pdf> the
    inspiration of this module
*)
module Search  : sig
  (** A data type that represent a collection of ['a] *)
  type 'a m 
  (** bind and return *)
  val ( >> ) : 'a m -> ('a -> 'b m) -> 'b m
  val return : 'a -> 'a m
  (** non-deterministic choice *)
  val ( >>| ) : 'a m -> 'a m -> 'a m
  (** failure *)
  val fail : unit -> 'a m
  (** folding through the collection *)
  val fold : ('a -> 'b -> 'b) -> 'a m -> 'b -> 'b
  (** derived facilities  *)
  val sprint : ('a -> string) -> 'a m -> string
  val count : 'a m -> int
  val choose : 'a m -> 'a option
  val to_list : 'a m -> 'a list
  val sort :  ('a -> 'a -> int) -> 'a m -> 'a m
  val is_empty: 'a m -> bool
end
= struct 
  
  type 'a m = | F of 'a
	      | N of 'a m list
		  
  let fold (f : 'a -> 'b -> 'b) (m : 'a m) (acc : 'b) =
    let rec aux acc = function
	F x -> f x acc
      | N l -> 
	  (List.fold_left (fun acc x ->
			     match x with 
			       | (N []) -> acc
			       | x ->  aux acc x
			  ) acc l)
    in
      aux acc m



  let rec (>>) : 'a m -> ('a -> 'b m) -> 'b m = 
    fun m f ->
      match m with 
	| F x -> f x 
	| N l -> 
	    N (List.fold_left (fun acc x ->
				 match x with 
				   | (N []) -> acc
				   | x ->  (x >> f)::acc
			      ) [] l)

  let (>>|) (m : 'a m) (n :'a m) : 'a m = match (m,n) with 
    | N [],_	-> n
    | _,N []	-> m
    | F x, N l -> N (F x::l)
    | N l, F x -> N (F x::l)
    | x,y -> N [x;y]
	
  let return : 'a -> 'a m                 =  fun x -> F x
  let fail : unit -> 'a m                 =  fun () ->  N []         

  let sprint f m =
    fold (fun x acc -> Printf.sprintf "%s\n%s" acc (f x)) m ""
  let rec count = function 
    | F _ -> 1
    | N l -> List.fold_left (fun acc x -> acc+count x) 0 l
	
  let opt_comb f x y = match x with None -> f y  | _ -> x

  let rec choose = function
    | F x -> Some x
    | N l -> List.fold_left (fun acc x -> 
			       opt_comb choose acc x
			    ) None l

  let is_empty = fun x -> choose x = None

  let to_list m = (fold (fun x acc -> x::acc) m [])
    
  let sort f m =
    N (List.map (fun x -> F x) (List.sort f (to_list m)))
end

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
    | One of symbol
    | Plus of (symbol * t * t)
    | Zero of symbol
    | Sym of (symbol * t array)
    | Var of var

  val equal_aac : t -> t -> bool
  val size: t -> int
  (** {1 Terms in normal form}
      
      A term in normal form is the canonical representative of the
      equivalence class of all the terms that are equal modulo
      Associativity and Commutativity. Outside the {!Matcher} module,
      one does not need to access the actual representation of this
      type.  *)

  type nf_term = private
		 | TAC of symbol * nf_term mset
		 | TA  of symbol * nf_term list
		 | TSym of symbol *nf_term  list
		 | TVar of var

		     
  (** {2 Constructors: we ensure that the terms are always
      normalised} *)
  val mk_TAC : symbol -> nf_term mset -> nf_term
  val mk_TA : symbol -> nf_term list -> nf_term
  val mk_TSym : symbol -> nf_term list -> nf_term
  val mk_TVar : var -> nf_term
    
  (** {2 Comparisons} *)

  val nf_term_compare : nf_term -> nf_term -> int
  val nf_equal : nf_term -> nf_term -> bool

  (** {2 Printing function}  *)
  val sprint_nf_term : nf_term -> string

  (** {2 Conversion functions}  *)
  val term_of_t : t -> nf_term 
  val t_of_term  : nf_term -> t 
end
  = struct

    type t =
	Dot of (symbol * t * t)
      | One of symbol
      | Plus of (symbol * t * t)
      | Zero of symbol
      | Sym of (symbol * t array)
      | Var of var

    let rec size = function 
      | Dot (_,x,y) 
      | Plus (_,x,y) -> size x+ size y + 1
      | Sym (_,v)-> Array.fold_left (fun acc x -> size x + acc) 1 v
      | _ -> 1

	  
    type nf_term = 
      | TAC of symbol * nf_term mset
      | TA  of symbol * nf_term list
      | TSym of symbol *nf_term  list
      | TVar of var



    (** {2 Comparison} *)

    let nf_term_compare = Pervasives.compare
    let nf_equal a b =  a = b
      
    (** {2 Constructors: we ensure that the terms are always
	normalised} *)
      	
    (** {3 Pre constructors : These constructors ensure that sums and
	products are not degenerated (no trailing units)} *)
    let mk_TAC' s l =  match l with 
      | [t,0] -> TAC (s,[])
      | [t,1] -> t 
      | _ ->  TAC (s,l)        
    let mk_TA' s l =   match l with [t] -> t 
      | _ -> TA  (s,l)
	  


    (** [merge_ac comp l1 l2] merges two lists of terms with coefficients
	into one. Terms that are equal modulo the comparison function
	[comp] will see their arities added. *)
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
    let rec merge l l' =
      merge_ac nf_term_compare l l'
	
    let extract_A s t =
      match t with 
	| TA (s',l) when s' = s -> l
	| _ -> [t]
	    
    let extract_AC s (t,ar) : nf_term mset = 
      match t with 
	| TAC (s',l) when s' = s -> List.map (fun (x,y) -> (x,y*ar)) l
	| _ -> [t,ar]

	    
    (** {3 Constructors of {!nf_term}}*)

    let mk_TAC s (l : (nf_term *int) list) = 
      mk_TAC' s	    
	(merge_map (fun u l -> merge (extract_AC s u) l) l) 
    let mk_TA s l =  
      mk_TA' s 
	(merge_map (fun u l -> (extract_A s u) @ l) l) 
    let mk_TSym s l = TSym (s,l) 
    let mk_TVar v = TVar v
      
      
    (** {2 Printing function}  *)
    let print_binary_list single unit  binary l =
      let rec aux l =
	match l with 
	    [] -> unit
	  | [t] -> single t
	  | t::q ->
	      let r = aux q in 
		Printf.sprintf  "%s" (binary (single t) r)
      in 
	aux l

    let sprint_ac single (l : 'a mset) =
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
	      

    let print_ac_list single s l =
      Printf.sprintf "[%i:AC]{%s}" 
	s
	(print_binary_list 
	   single
	   "0" 
	   (fun x y -> x ^ " , " ^ y) 
	   l
	)


    let print_a single s l =
      Printf.sprintf "[%i:A]{%s}" 
	s
	(print_binary_list single "1" (fun x y -> x ^ " , " ^ y) l)        

    let rec sprint_nf_term = function
      | TSym (s,l) -> print_symbol sprint_nf_term s l 
      | TAC (s,l) -> 
	  Printf.sprintf "[%i:AC]{%s}" s
	    (sprint_ac
	       sprint_nf_term
	       l)
      | TA (s,l) -> print_a sprint_nf_term s l 
      | TVar v -> Printf.sprintf "x%i" v



    (** {2 Conversion functions} *)

    (* rebuilds a tree out of a list *)
    let rec binary_of_list f comb null l =
      let l = List.rev l in 
      let rec aux =    function 
      | [] -> null
      | [t] -> f t
      | t::q -> comb (aux q) (f t)
      in 
	aux l

    let rec term_of_t : t -> nf_term = function
      | Dot (s,l,r) -> 
	  let l = term_of_t l in 
	  let r = term_of_t r in 
	    mk_TA s [l;r]
      | Plus (s,l,r) -> 
	  let l = term_of_t l in 
	  let r = term_of_t r in 
	    mk_TAC ( s) [l,1;r,1]
      | One x -> 
	  mk_TA ( x) []
      | Zero x -> 
	  mk_TAC ( x) []
      | Sym (s,t) -> 
	  let t = Array.to_list t in 
	  let t = List.map term_of_t t in  
	    mk_TSym ( s) t
      | Var i -> 
	  mk_TVar ( i)

    let rec t_of_term  : nf_term -> t =  function 
      | TAC (s,l) ->
	  (binary_of_list 
	     t_of_term
	     (fun l r -> Plus ( s,l,r))
	     (Zero ( s))
	     (linear l) 
	  )
      | TA (s,l) ->
	  (binary_of_list 
	     t_of_term 
	     (fun l r -> Dot ( s,l,r))
	     (One ( s))
	     l
	  )
      | TSym (s,l) -> 
	  let v = Array.of_list l in 
	  let v = Array.map (t_of_term) v in 
	    Sym ( s,v)
      | TVar x -> Var x


    let equal_aac x y =
      nf_equal (term_of_t x) (term_of_t y)
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
      | One _ as x -> x
      | Zero _ as x -> x
      | Sym (s,t) -> Sym (s,Array.map aux t)
      | Plus (s,l,r) -> Plus (s, aux l, aux r)
      | Dot (s,l,r) -> Dot (s, aux l, aux r)
      | Var i ->  
	  begin match find t i  with
	    | None -> Util.error "aac_tactics: instantiate failure" 
	    | Some x -> t_of_term  x
	  end
    in aux x
	 
  let to_list t = List.map (fun (x,y) -> x,Terms.t_of_term y) t
end

(******************)
(* MATCHING UTILS *)
(******************)

open Terms

(** First, we need to be able to perform non-deterministic choice of
    term splitting to satisfy a pattern. Indeed, we want to show that:
    (x+a*b)*c <= a*b*c
*)
let a_nondet_split  t : ('a list * 'a list) m =
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
  a_nondet_split t >>
    (fun left, right -> 
       a_nondet_split left >> 
	 (fun left, middle -> return (left, middle, right))
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
    
let ac_nondet_split (l : 'a mset) :  ('a mset * 'a mset) m =
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

(** Try to affect the variable [x] to each left factor of [t]*)
let var_a_nondet_split ?(strict=false) env current  x  t =
  a_nondet_split t
  >>
    (fun (l,r) -> 
       if strict && l=[] then fail() else
       return ((Subst.add env x (mk_TA current l)), r)
    )
    
(** Try to affect variable [x] to _each_ subset of t. *)
let var_ac_nondet_split ?(strict=false) (s : symbol) env (x : var) (t : nf_term mset) : (Subst.t * (nf_term mset)) m =
  ac_nondet_split t 
  >>
    (fun (subset,compl) -> 
       if strict && subset=[] then fail() else
       return ((Subst.add env x (mk_TAC s subset)), compl)
    )
    
(** See the term t as a given AC symbol. Unwrap the first constructor
    if necessary *)
let get_AC (s : symbol) (t : nf_term) : (nf_term *int) list = 
  match t with 
    | TAC (s',l) when s' = s ->  l 
    | _ ->  [t,1]
	
(** See the term t as a given A symbol. Unwrap the first constructor
    if necessary *)
let get_A (s : symbol) (t : nf_term) : nf_term list = 
  match t with 
    | TA (s',l) when s' = s ->  l 
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
	    
(** [fold_acc] gather all elements of a list that satisfies a
    predicate, and combine them with the residual of the list.  That
    is, each element of the residual contains exactly one element less
    than the original term.
    
    TODO : This function not as efficient as it could be
*)

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
      

      
(** We have to check if we are trying to remove a unit from a term*)
let  is_unit_AC s t =
  nf_equal t (mk_TAC s [])

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
let matching ?strict = 
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
      | TVar x:: q ->
	  begin match Subst.find env x with 
	    | None -> 
		(var_ac_nondet_split ?strict current env x t) 
		>> (fun (env,residual) -> matchingAC env current q residual)
	    | Some v -> 
		(factor_AC current v t) 
		>> (fun residual -> matchingAC env current q residual)		
	  end	
      | h :: q ->(*  PAC =/= curent or PA *)
	  (ac_nondet_split t)
	  >> 
	    (fun (left,right) ->
	       matching env h (mk_TAC current left)
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
		var_a_nondet_split ?strict env current x t 
		>> (fun (env,residual)-> matchingA env current l residual) 
	    | Some v -> 
		(left_factor current v t) 
		>> (fun residual -> matchingA env current l residual)
	  end
      | h :: l ->
	  a_nondet_split t 
	  >> (fun (t,r) -> 
		matching env h (mk_TA current t)
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
    matching 



(***********)
(* Subterm *)
(***********)

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
					l,r,f acc l t r
				   ) ([], l,acc) l
      in acc


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

    Strange patterms like x*y*x can be instanciated by nothing, inside
    a product. Therefore, we need to check that all the term is not
    going into the context (hence the tests on the length of the
    lists). With proper support for interaction with the user, we
    should lift these tests. However, at the moment, they serve as
    heuristics to return "interesting" matchings
    
*)

let return_non_empty raw_p m =
  if Search.is_empty m
  then
    fail ()
  else
    return (raw_p ,m)

let subterm ?strict (raw_p:t) (raw_t:t): (int* t * Subst.t m) m=
  let p = term_of_t raw_p in 
  let t = term_of_t raw_t in     
  let rec subterm (t:nf_term) : (t * Subst.t m) m=
    match t with 
      | TAC (s,l) ->
	  (ac_nondet_split l) >>
	    (fun (left,right) ->
	       (subterm_AC s left) >>
		 (fun (p,m) -> 
		    let p = if right = [] then p else 
		      Plus (s,p,t_of_term (mk_TAC s right))
		    in 
		      return (p,m)
		 )		     
		 
	    )
      | TA (s,l) -> 
	  (a_nondet_middle l) 
	  >>
	    (fun (left, middle, right) ->
	       (subterm_A s middle) >>
		 (fun (p,m) ->
		    let p =
		      if right = [] then p else 
			Dot (s,p,t_of_term (mk_TA s right))
		    in
		    let p = 
		      if left = [] then p else
			Dot (s,t_of_term (mk_TA s left),p)
		    in
		      return (p,m)
		 )
	    )
      | TSym (s, l) -> 
	  let init = return_non_empty raw_p (matching ?strict Subst.empty p t) in 
	    tri_fold (fun acc l t r -> 
			((subterm  t) >>
			   (fun (p,m) ->
			      let l = List.map t_of_term l in 
			      let r = List.map t_of_term r in 
			      let p = Sym (s, Array.of_list (List.rev_append l (p::r))) in 
				return (p,m)
			   )) >>| acc
		     ) l init
      | _ -> assert false
  and subterm_AC s tl   =
    match tl with 
	[x,1] -> subterm  x
      | _ -> 
	  return_non_empty raw_p (matching ?strict Subst.empty p (mk_TAC s tl))
  and subterm_A s  tl =
    match tl with 
	[x] -> subterm  x
      | _ -> 
	  return_non_empty raw_p (matching ?strict Subst.empty p (mk_TA s tl))
  in 
    (subterm t >> fun (p,m) -> return (Terms.size p,p,m))

(* The functions we export, handlers for the previous ones. Some debug
   information also *)
let subterm ?strict raw t =
  let sols = time (subterm ?strict raw) t "%fs spent in subterm (including matching)\n" in
    if debug then Printf.printf "%i possible solution(s)\n" 
      (Search.fold (fun (_,_,envm) acc -> count envm + acc) sols 0); 
    sols


let matcher ?strict p t = 
  let sols = time 
    (fun (p,t) -> 
       let p = (Terms.term_of_t p) in 
       let t = (Terms.term_of_t t) in 
	 matching ?strict Subst.empty p t) (p,t) 
    "%fs spent in the matcher\n"
  in 
    if debug then Printf.printf "%i solutions\n" (count sols);
    sols

(* A very basic way to interact with the envs, to choose a possible
   solution *)
open Pp
let pp_env pt  : Subst.t -> Pp.std_ppcmds = fun env ->
  List.fold_left (fun acc (v,t) -> str (Printf.sprintf "x%i: " v) ++ pt t ++ str "; " ++ acc)  (str "") (Subst.to_list env)

let pp_envm pt : Subst.t Search.m -> Pp.std_ppcmds = fun m ->
  let _,s = Search.fold 
    (fun env (n,acc) -> 
       n+1,  h 0 (str (Printf.sprintf "%i:\t[" n) ++pp_env pt env ++ str "]") ++ fnl () :: acc
    ) m (0,[]) in 
    List.fold_left (fun acc s -> s ++ acc) (str "") (s)
    
let pp_all pt : (int * Terms.t * Subst.t Search.m) Search.m -> Pp.std_ppcmds = fun m ->
  let _,s = Search.fold 
    (fun (size,context,envm) (n,acc) ->  
       let s = str (Printf.sprintf "subterm %i\t" n) in 
       let s = s ++ (str "(context ") ++ pt context ++ (str ")\n") in 
       let s = s ++ str (Printf.sprintf "\t%i possible(s) substitutions" (Search.count envm) ) ++ fnl () in 
       let s = s ++ pp_envm pt envm in 
	 n+1, s::acc
    ) m (0,[]) in 
    List.fold_left (fun acc s -> s ++ str "\n" ++ acc) (str "") (s)

