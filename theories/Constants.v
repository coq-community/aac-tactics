(* *********************************************************************** *)
(*  This is part of aac_tactics, it is distributed under the terms of the  *)
(*         GNU Lesser General Public License version 3                     *)
(*              (see file LICENSE for more details)                        *)
(*                                                                         *)
(*       Copyright 2009-2010: Thomas Braibant, Damien Pous.                *)
(* *********************************************************************** *)

Register Init.Datatypes.O as aac_tactics.nat.O.
Register Init.Datatypes.S as aac_tactics.nat.S.
Register Init.Datatypes.nat as aac_tactics.nat.type.

Register Init.Datatypes.pair as aac_tactics.pair.pair.
Register Init.Datatypes.prod as aac_tactics.pair.prod.

Register Init.Datatypes.option as aac_tactics.option.typ.
Register Init.Datatypes.Some as aac_tactics.option.Some.
Register Init.Datatypes.None as aac_tactics.option.None.

Register Init.Datatypes.list as aac_tactics.list.typ.
Register Init.Datatypes.nil as aac_tactics.list.nil.
Register Init.Datatypes.cons as aac_tactics.list.cons.

From Coq Require BinNums.
Register BinNums.positive as aac_tactics.pos.typ.
Register BinNums.xI as aac_tactics.pos.xI.
Register BinNums.xO as aac_tactics.pos.xO.
Register BinNums.xH as aac_tactics.pos.xH.

From Coq Require Classes.Morphisms.
Register Morphisms.Proper as aac_tactics.coq.classes.morphisms.Proper.
From Coq Require Classes.RelationClasses.

Register RelationClasses.Equivalence as aac_tactics.coq.RelationClasses.Equivalence.
Register RelationClasses.Reflexive as aac_tactics.coq.RelationClasses.Reflexive.
Register RelationClasses.Transitive as aac_tactics.coq.RelationClasses.Transitive.
