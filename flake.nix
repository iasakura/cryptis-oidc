{
  description = "Formal verification of OpenID Connect in Cryptis";

  inputs = {
    cryptis.url = "github:arthuraa/cryptis";
    # Use exactly the nixpkgs that cryptis was built against.
    nixpkgs.follows = "cryptis/nixpkgs";
    rocq-mcp.url = "github:arthuraa/rocq-mcp-flake";
    rocq-mcp.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, cryptis, rocq-mcp }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
      pkgsFor = system: overlays: import nixpkgs { inherit system overlays; };
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = pkgsFor system [ cryptis.overlays.default ];
          aiPkgs = pkgsFor system [
            cryptis.overlays.default
            rocq-mcp.overlays.default
          ];
          common = [
            pkgs.coqPackages.cryptis
            pkgs.coqPackages.coq
            pkgs.coqPackages.coq-lsp
          ];
        in
        {
          default = pkgs.mkShell { packages = common; };
          ai = pkgs.mkShell { packages = common ++ [ aiPkgs.rocq-mcp ]; };
        });
    };
}
