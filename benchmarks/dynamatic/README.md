# Reproduce simulation and synthesis results

This requires a version of Vivado for simulation and synthesis.

## Simulation

For example, for `matvec`:

```shell
cd matvec
../../../scripts/xsim-build.sh matvec.sv
```

The line starting with `Cycle count` at the end of the output shows the number of cycles that were taken for the complete execution of the benchmark.

## Synthesis

For example, for `matvec`:

```shell
cd matvec
vivado -mode batch -source synth.tcl
```

This will produce various reports.

- `timing_post_pr.rpt` determines the maximum clock speed.
- `utilization_post_pr.rpt` determines the area.
