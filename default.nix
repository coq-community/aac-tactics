{ pkgs ? (import <nixpkgs> {}), coq-version ? "master" }:

let
 coq =
   let coq-version-parts = builtins.match "([0-9]+).([0-9]+)" coq-version; in
   if coq-version-parts == null then
     import (fetchTarball "https://github.com/coq/coq/tarball/${coq-version}") {}
   else
     pkgs."coq_${builtins.concatStringsSep "_" coq-version-parts}";
in

pkgs.stdenv.mkDerivation {

  name = "aac_tactics";

  buildInputs = with coq.ocamlPackages;
    [ coq ocaml findlib camlp5_strict ]
    ++ pkgs.lib.optionals pkgs.lib.inNixShell [ merlin ocp-indent ocp-index ];

  src = if pkgs.lib.inNixShell then null else ./.;

  installFlags = "COQLIB=$(out)/lib/coq/";
}
