(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

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

(* preserve the structure of the heap *)
let filter f m =
  fold (fun x acc -> (if f x then return x else fail ()) >>| acc) m (N [])
  
