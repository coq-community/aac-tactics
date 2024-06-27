From Coq Require Import ZArith.
From AAC_tactics Require Import AAC.

Goal forall X:Prop, X->X.
Succeed (try aac_rewrite Z.gcd_mod).
Abort.

Goal forall X:Prop, X->X.
Succeed (try aac_normalise).
Abort.
