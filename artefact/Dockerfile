FROM nixos/nix

RUN nix-channel --add https://nixos.org/channels/nixpkgs-unstable nixpkgs
RUN nix-channel --update

RUN nix-env -i yosys git vim gcc iverilog verilator gnumake

RUN echo "experimental-features = nix-command flakes repl-flake" >> /etc/nix/nix.conf

COPY . /vericert

WORKDIR /vericert
CMD nix develop

RUN nix develop --command make lib/COHPREDSTAMP
RUN nix develop --command make -j
RUN nix develop --command make install

RUN echo 'export PATH=/vericert/scripts:/vericert/bin:$PATH' >>/root/.bashrc
