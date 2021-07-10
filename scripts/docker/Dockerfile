FROM nixos/nix

RUN nix-channel --add https://nixos.org/channels/nixpkgs-unstable nixpkgs
RUN nix-channel --update

RUN nix-env -i yosys git tmux vim gcc iverilog

RUN git clone --recursive https://github.com/ymherklotz/vericert

WORKDIR /vericert
RUN git checkout -b oopsla21
RUN nix-shell --run "make -j7"
RUN nix-shell --run "make install"
