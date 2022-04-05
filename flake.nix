{
  description = "Wasm tools for Lean";

  inputs = {
    lean = {
      url = "github:leanprover/lean4";
    };
    nixpkgs.url = "github:nixos/nixpkgs/nixos-21.11";
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    lean-ipld = {
      url = "github:yatima-inc/lean-ipld";
      # Compile dependencies with the same lean version
      inputs.lean.follows = "lean";
    };
    parsec = {
      url = "github:yatima-inc/Parsec.lean";
      inputs.lean.follows = "lean";
    };
  };

  outputs = { self, lean, flake-utils, nixpkgs, lean-ipld, parsec }:
    let
      supportedSystems = [
        "aarch64-linux"
        "aarch64-darwin"
        "i686-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
      inherit (flake-utils) lib;
    in
    lib.eachSystem supportedSystems (system:
      let
        leanPkgs = lean.packages.${system};
        pkgs = nixpkgs.legacyPackages.${system};
        name = "Wasm";  # must match the name of the top-level .lean file
        project = leanPkgs.buildLeanPackage {
          inherit name;
          deps = with leanPkgs; [
            Init
            Lean
            parsec.project.${system}
            # lean-ipld.project.${system}
          ];
          # Where the lean files are located
          src = ./src;
        };
        cli = leanPkgs.buildLeanPackage {
          name = "Wasm.Cli";
          deps = [ project ];
          # Where the lean files are located
          src = ./src;
        };
        test = leanPkgs.buildLeanPackage {
          name = "Tests";
          deps = [ project ];
          # Where the lean files are located
          src = ./test;
        };
      in
      {
        inherit project test;
        packages = project // {
          ${name} = project.sharedLib;
          cli = cli.executable;
          test = test.executable;
        };

        defaultPackage = self.packages.${system}.cli;
        devShell = pkgs.mkShell {
          inputsFrom = [ project.executable ];
          buildInputs = with pkgs; [
            leanPkgs.lean-dev
          ];
          LEAN_PATH = "./src:./test";
          LEAN_SRC_PATH = "./src:./test";
        };
      });
}
