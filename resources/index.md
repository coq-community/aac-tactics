---
title: AAC Tactics
lang: en
header-includes:
  - |
    <style type="text/css"> body {font-family: Arial, Helvetica; margin-left: 5em; font-size: large;} </style>
    <style type="text/css"> h1 {margin-left: 0em; padding: 0px; text-align: center} </style>
    <style type="text/css"> h2 {margin-left: 0em; padding: 0px; color: #580909} </style>
    <style type="text/css"> h3 {margin-left: 1em; padding: 0px; color: #C05001;} </style>
    <style type="text/css"> body { width: 1100px; margin-left: 30px; }</style>
---

<div style="text-align:left"><img src="https://github.githubassets.com/images/modules/logos_page/Octocat.png" height="25" style="border:0px">
<a href="https://github.com/coq-community/aac-tactics">View the project on GitHub</a>
<img src="https://github.githubassets.com/images/modules/logos_page/Octocat.png" height="25" style="border:0px"></div>

## About

Welcome to the AAC Tactics project website! This project is part of [coq-community](https://github.com/coq-community/manifesto).

This Coq plugin provides tactics for rewriting and proving universally
quantified equations modulo associativity and commutativity of some operator,
with idempotent commutative operators enabling additional simplifications.
The tactics can be applied for custom operators by registering the operators and
their properties as type class instances. Instances for many commonly used operators,
such as for binary integer arithmetic and booleans, are provided with the plugin.

This is an open source project, licensed under the GNU Lesser General Public License v3.0 or later.

## Get the code

The current stable release of AAC Tactics can be [downloaded from GitHub](https://github.com/coq-community/aac-tactics/releases).

## Documentation

- [paper on initial version](https://arxiv.org/abs/1106.4448)
- [latest coqdoc documentation](https://coq-community.org/aac-tactics/docs/coqdoc/toc.html)

## Help and contact

- Report issues on [GitHub](https://github.com/coq-community/aac-tactics/issues)
- Chat with us on [Zulip](https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users)
- Discuss with us on Coq's [Discourse](https://coq.discourse.group) forum

## Authors

- Thomas Braibant
- Damien Pous
- Fabian Kunze
