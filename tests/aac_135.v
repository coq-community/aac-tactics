From Coq Require PeanoNat ZArith List Permutation Lia.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.

(** ** Introductory example

   Here is a first example with relative numbers ([Z]): one can
   rewrite an universally quantified hypothesis modulo the
   associativity and commutativity of [Z.add]. *)

Section introduction.
  Import ZArith.
  Import Instances.Z.

  Variables a b : Z.

  Goal a + b = b + a.
    aac_reflexivity.
  Qed.

  Goal forall c: bool, a + b = b + a.
    intros c.
    destruct c.
    1,2: aac_reflexivity.
  Qed. (* The command has indeed failed with message: Some unresolved existential variables remain *)

  Goal forall c: bool, a + b = b + a.
    intros c.
    destruct c.
    - aac_reflexivity.
    - aac_reflexivity.
  Qed.
End introduction.
