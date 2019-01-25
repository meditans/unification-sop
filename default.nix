{ mkDerivation, base, generics-sop, pretty-show, show-combinators
, stdenv
}:
mkDerivation {
  pname = "unification-sop";
  version = "0.1.0.0";
  src = ./.;
  libraryHaskellDepends = [
    base generics-sop pretty-show show-combinators
  ];
  doHaddock = false;
  license = stdenv.lib.licenses.bsd3;
}
