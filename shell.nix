{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, containers, doctest, doctest-discover
      , generics-sop, logict, mtl, pretty-show, show-combinators, stdenv
      , typerep-map
      }:
      mkDerivation {
        pname = "unification-sop";
        version = "0.1.0.0";
        src = ./.;
        libraryHaskellDepends = [
          base containers generics-sop logict mtl pretty-show
          show-combinators typerep-map
        ];
        testHaskellDepends = [ base doctest doctest-discover ];
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
