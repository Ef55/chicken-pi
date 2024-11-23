{
  inputs = {
   nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
   utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, utils }: utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };

      stack-wrapped = pkgs.symlinkJoin {
          name = "stack"; # will be available as the usual `stack` in terminal
          paths = [ pkgs.stack ];
          buildInputs = [ pkgs.makeWrapper ];
          postBuild = ''
            wrapProgram $out/bin/stack \
              --add-flags "\
                --no-nix \
                --system-ghc \
                --no-install-ghc \
              "
          '';
        };

      hpkgs = pkgs.haskell.packages.ghc948;
    in
    {
      devShell = pkgs.mkShell {
        buildInputs = with hpkgs; [
          stack-wrapped
          haskell-language-server
          hlint
          ormolu
        ];
      };
    }
  );
}
