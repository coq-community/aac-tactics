From Coq Require PeanoNat ZArith List Permutation Lia.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.

Section introduction.
  Import ZArith.
  Import Instances.Z.

  Variables a b d e: Z.

  Goal a + b = b + a.
    aac_reflexivity.
  Qed.

  Goal b+a+d+e = b+a+e+d.
    aac_normalise.
    (* variable ordering is fixed since v8.19.1, so that this second call should be a noop *)
    Fail progress aac_normalise. 
    reflexivity.
  Qed.

  Goal b+a+d = e+d -> d+a+b = d+e.
    intro H. aac_normalise in H.
    aac_normalise.
    (* variable ordering is fixed since v8.19.1, so expressions should be normalised consistently across calss *)
    assumption.
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
