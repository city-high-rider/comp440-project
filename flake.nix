{
  description = "Tools needed to work on COMP440 stuff";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        edit-report = pkgs.writeShellApplication {
          name = "edit-report";
          runtimeInputs = with pkgs; [
            pandoc
            python314Packages.weasyprint
            mupdf
            entr
          ];
          text = ''
            echo "$1" | entr -n pandoc --pdf-engine=weasyprint "$1" -o "$2" &
            echo "$2" | entr -n pkill -HUP mupdf &
            mupdf "$2" 
          '';
        };
      in {
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            idris2
            # Because Helix does not support Idris interactive edititng.
            ((vim-full.override { }).customize {
              name = "vim";
              # Install plugins
              vimrcConfig.packages.myplugins = with pkgs.vimPlugins; {
                start = [ idris2-vim nerdtree ];
                opt = [ ];
              };
              vimrcConfig.customRC = ''
                " colors
                colorscheme morning
                set relativenumber
                set number
                " your custom vimrc
                set nocompatible
                set backspace=indent,eol,start
                " Turn on syntax highlighting by default
                syntax on
                filetype on
                filetype plugin indent on
                let maplocalleader = " "
                " === Dvorak-friendly motions (Normal, Visual, Operator-pending) ===
                " Modes: n = normal, v = visual, x = operator-pending
                " h/j/k/l motions remapped
                nnoremap <silent> d h
                nnoremap <silent> h j
                nnoremap <silent> t k
                nnoremap <silent> n l
                nnoremap <silent> qq dd

                " Combine modes using a loop for conciseness
                for mode in ['n','v','x']
                  execute mode . 'noremap q d'            
                  execute mode . 'noremap <leader>q q'    
                  execute mode . 'noremap gs 0'           
                  execute mode . 'noremap gl $'           
                endfor
              '';
            })
            vscodium
            idris2Packages.idris2Lsp
            edit-report
          ];

          shellHook = "echo Entered Comp Devshell...";
        };
      });
}
