FROM nixos/nix

RUN nix-channel --add https://nixos.org/channels/nixpkgs-unstable nixpkgs
RUN nix-channel --update

RUN nix-env -i yosys git tmux vim gcc iverilog verilator lp_solve gnumake 

RUN echo "experimental-features = nix-command flakes repl-flake" >> /etc/nix/nix.conf

COPY . /vericert

WORKDIR /vericert
CMD nix develop

RUN nix develop --command make lib/COHPREDSTAMP
RUN nix develop --command make -j
RUN nix develop --command make install

RUN mkdir -p /opt
RUN mv /vericert/squashfs-root /opt/bambu

RUN echo 'export PATH=/opt/bambu/usr/bin:/vericert/scripts:/vericert/bin:$PATH' >>/root/.bashrc
