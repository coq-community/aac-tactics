                
			     aac_tactics
			     ===========

		    Thomas Braibant & Damien Pous

Laboratoire d'Informatique de Grenoble (UMR 5217), INRIA, CNRS, France

Webpage of the project: http://sardes.inrialpes.fr/~braibant/aac_tactics/


FOREWORD 
======== 

This plugin provides tactics for rewriting universally quantified
equations, modulo associativity and commutativity of some operators.

INSTALLATION
============

This plugin should work with Coq v8.3, as released on the 14th of
October 2010.

- run [./make_makefile] in the top-level directory to generate a Makefile
- run [make world] to build the plugin and the documentation

Option 1
--------
To install the plugin in Coq's directory, as, e.g., omega or ring.

- run [sudo make install CMXSFILES='aac_tactics.cmxs aac_tactics.cma']
  to copy the relevant files of the plugin

Option 2
--------

If you chose not to use the previous option, you will need to add the
following lines to (all) your .v files to be able to use the plugin:

Add Rec LoadPath "absolute_path_to_aac_tactics".
Add ML Path "absolute_path_to_aac_tactics".

DOCUMENTATION
=============

Please refer to Tutorial.v for a succinct introduction on how to use
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
- N binary numbers	(Import Instances.N)
- P binary numbers	(Import Instances.P)
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
