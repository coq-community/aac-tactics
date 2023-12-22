<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# AAC Tactics

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/aac-tactics/actions/workflows/docker-action.yml/badge.svg?branch=v8.19
[docker-action-link]: https://github.com/coq-community/aac-tactics/actions/workflows/docker-action.yml

[nix-action-shield]: https://github.com/coq-community/aac-tactics/actions/workflows/nix-ci.yml/badge.svg?branch=v8.19
[nix-action-link]: https://github.com/coq-community/aac-tactics/actions/workflows/nix-ci.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://coq-community.org/aac-tactics/docs/coqdoc/toc.html

[doi-shield]: https://zenodo.org/badge/DOI/10.1007/978-3-642-25379-9_14.svg
[doi-link]: https://doi.org/10.1007/978-3-642-25379-9_14

This Coq plugin provides tactics for rewriting and proving universally
quantified equations modulo associativity and commutativity of some operator,
with idempotent commutative operators enabling additional simplifications.
The tactics can be applied for custom operators by registering the operators and
their properties as type class instances. Instances for many commonly used operators,
such as for binary integer arithmetic and booleans, are provided with the plugin.

## Meta

- Author(s):
  - Thomas Braibant (initial)
  - Damien Pous (initial)
  - Fabian Kunze
- Coq-community maintainer(s):
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [GNU Lesser General Public License v3.0 or later](LICENSE)
- Compatible Coq versions: 8.19 (use the corresponding branch or release for other Coq versions)
- Compatible OCaml versions: 4.09.0 or later
- Additional dependencies: none
- Coq namespace: `AAC_tactics`
- Related publication(s):
  - [Tactics for Reasoning modulo AC in Coq](https://arxiv.org/abs/1106.4448) doi:[10.1007/978-3-642-25379-9_14](https://doi.org/10.1007/978-3-642-25379-9_14)

## Building and installation instructions

The easiest way to install the latest released version of AAC Tactics
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-aac-tactics
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/aac-tactics.git
cd aac-tactics
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

The following example shows an application of the tactics for reasoning over Z binary numbers:
```coq
From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.
From Coq Require Import ZArith.

Section ZOpp.
  Import Instances.Z.
  Variables a b c : Z.
  Hypothesis H: forall x, x + Z.opp x = 0.

  Goal a + b + c + Z.opp (c + a) = b.
    aac_rewrite H.
    aac_reflexivity.
  Qed.

  Goal Z.max (b + c) (c + b) + a + Z.opp (c + b) = a.
    aac_normalise.
    aac_rewrite H.
    aac_reflexivity.
  Qed.
End ZOpp.
```

The file [Tutorial.v](theories/Tutorial.v) provides a succinct introduction
and more examples of how to use this plugin.

The file [Instances.v](theories/Instances.v) defines several type class instances
for frequent use-cases of this plugin, that should allow you to use it off-the-shelf.
Namely, it contains instances for:

- Peano naturals (`Import Instances.Peano.`)
- Z binary numbers (`Import Instances.Z.`)
- Lists (`Import Instances.Lists.`)
- N binary numbers (`Import Instances.N.`)
- Positive binary numbers (`Import Instances.P.`)
- Rational numbers (`Import Instances.Q.`)
- Prop (`Import Instances.Prop_ops.`)
- Booleans (`Import Instances.Bool.`)
- Relations (`Import Instances.Relations.`)
- all of the above (`Import Instances.All.`)

To understand the inner workings of the tactics, please refer to
the `.mli` files as the main source of information on each `.ml` file.

See also the [latest coqdoc
documentation](https://coq-community.org/aac-tactics/docs/coqdoc/toc.html)
and the [latest ocamldoc
documentation](https://coq-community.org/aac-tactics/docs/ocamldoc/index.html).

## Acknowledgements

The initial authors are grateful to Evelyne Contejean, Hugo Herbelin,
Assia Mahboubi, and Matthieu Sozeau for highly instructive discussions.
The plugin took inspiration from the plugin tutorial "constructors" by
Matthieu Sozeau, distributed under the LGPL 2.1.

