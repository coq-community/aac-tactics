(***************************************************************************)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(***************************************************************************)

module type CONTROL = sig
  val debug : bool
  val time : bool
  val printing : bool
end

module Debug (X : CONTROL) = struct
  open X
  let debug x =
    if debug then
      Printf.printf "%s\n%!" x


  let time f x fmt =
    if time then
      let t = Sys.time () in
      let r = f x in
	Printf.printf fmt  (Sys.time () -. t);
	r
    else f x

  let pr_constr msg constr =
    if printing then
      (  Pp.msgnl (Pp.str (Printf.sprintf "=====%s====" msg));
	 Pp.msgnl (Printer.pr_constr constr);
      )


  let debug_exception msg e =
    debug (msg ^ (Printexc.to_string e))
     

end
