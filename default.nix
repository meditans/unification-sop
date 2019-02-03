{ mkDerivation, base, containers, doctest, doctest-discover
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
}
