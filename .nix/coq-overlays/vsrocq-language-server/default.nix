{
  metaFetch,
  coq,
  lib,
  glib,
  gnome,
  wrapGAppsHook,
  version ? null
}:

let
  ocamlPackages = coq.ocamlPackages;

  defaultVersion =
    with lib.versions;
    lib.switch coq.coq-version [
      { case = range "8.18" "8.20"; out = "2.3.4"; }
    ] null;

  location = {
    domain = "github.com";
    owner = "rocq-prover";
    repo = "vsrocq";
  };

  fetch = metaFetch {
    release."2.3.4".rev = "v2.3.4";
    release."2.3.4".sha256 =
      "sha256-v1hQjE8U1o2VYOlUjH0seIsNG+NrMNZ8ixt4bQNyGvI=";

    inherit location;
  };

  fetched =
    fetch (if version != null then version else defaultVersion);

in

ocamlPackages.buildDunePackage {
  pname = "vsrocq-language-server";

  inherit (fetched) version;

  src = "${fetched.src}/language-server";

  nativeBuildInputs = [
    coq
  ];

  buildInputs =
    [
      coq
      glib
      gnome.adwaita-icon-theme
      wrapGAppsHook4
    ]
    ++
    (with ocamlPackages; [
      findlib
      lablgtk3-sourceview3
      yojson
      zarith
      ppx_inline_test
      ppx_assert
      ppx_sexp_conv
      ppx_deriving
      ppx_import
      sexplib
      ppx_yojson_conv
      lsp
      sel
      ppx_optcomp
    ]);

  preBuild = ''
    make dune-files
  '';

  meta = with lib; {
    description = "Language server for the VsRocq VS Code/VSCodium extension";
    homepage = "https://github.com/rocq-prover/vsrocq";
    license = licenses.mit;
  };
}
