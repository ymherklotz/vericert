FROM nixos/nix

RUN nix-channel --add https://nixos.org/channels/nixpkgs-unstable nixpkgs
RUN nix-channel --update

RUN nix-env -i yosys git tmux vim gcc iverilog verilator

RUN echo "experimental-features = nix-command flakes repl-flake" >> /etc/nix/nix.conf

COPY . /vericert

WORKDIR /vericert
RUN nix develop

RUN echo "export PATH=/vericert/bin:$PATH" >>/root/.bashrc
