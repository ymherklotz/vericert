set --export --global VERICERT_ROOT (git rev-parse --show-toplevel)
set --export --global --path --prepend PATH $VERICERT_ROOT/bin
set --export --global --path --prepend PATH $VERICERT_ROOT/scripts
