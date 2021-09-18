FROM nixos/nix

RUN nix-channel --add https://nixos.org/channels/nixpkgs-unstable nixpkgs
RUN nix-channel --update

RUN nix-env -i yosys git tmux vim gcc iverilog

ADD legup_polybench_syn.tar.gz /data/legup-polybench-syn
ADD legup_polybench_syn_div.tar.gz /data/legup-polybench-syn-div
ADD data.tar.gz /data

RUN git clone --recursive https://github.com/ymherklotz/vericert

WORKDIR /vericert
RUN git checkout oopsla21
RUN nix-shell --run "make -j7"
RUN nix-shell --run "make install"

RUN echo "export PATH=/vericert/bin:$PATH" >>/root/.bashrc
