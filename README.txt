                
			     aac_tactics
			     ===========

		    Thomas Braibant & Damien Pous

Laboratoire d'Informatique de Grenoble (UMR 5217), INRIA, CNRS, France

Webpage of the project: http://sardes.inrialpes.fr/~braibant/aac_tactics/


FOREWORD 
======== 

This plugin provides tactics for rewriting universally quantified
equations, modulo associativity and commutativity of some operators.

INSTALL
=======

- run [./make_makefile] in the top-level directory to generate a Makefile
- run [make world] to build the plugin and the documentation

This should work with Coq v8.3 `beta' : -r 13027, -r 13060 and hopefully the
following ones.

To be able to import the plugin from anywhere, add the following to
your ~/.coqrc

Add Rec LoadPath "path_to_aac_tactics".
Add ML Path "path_to_aac_tactics".


DOCUMENTATION
=============

Please refer to Tutorial.v for a succint introduction on how to use
this plugin.

To understand the inner-working of the tactic, please refer to the
.mli files as the main source of information on each .ml
file. Alternatively, [make world] generates ocamldoc/coqdoc
documentation in directories doc/ and html/, respectively.

File Instances.v defines several instances for frequent use-cases of
this plugin, that should allow you to use it out-of-the-shelf. Namely,
we have instances for:

- Peano naturals	(Import Instances.Peano)
- Z binary numbers	(Import Instances.Z)
- Rationnal numbers	(Import Instances.Q)
- Prop			(Import Instances.Prop_ops)
- Booleans		(Import Instances.Bool)
- Relations		(Import Instances.Relations)
- All of the above	(Import Instances.All)


ACKNOWLEDGEMENTS
================

We are grateful to Evelyne Contejean, Hugo Herbelin, Assia Mahboubi
and Matthieu Sozeau for highly instructive discussions.

This plugin took inspiration from the plugin tutorial "constructors",
distributed under the LGPL 2.1, copyrighted by Matthieu Sozeau
