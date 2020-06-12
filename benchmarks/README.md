Hi,

I have collected a set of benchmarks that you may be interested in. The main idea is to run the existing HLS benchmarks to see if they work - they can only test correctness for a single set of input by a customised test bench.

* jacob_2d: a benchmark from Polybench
* sobel: a benchmark from LegUp HLS
* getTanh: a benchmark from DASS
* fft: a benchmark from MachSuite
* KMeans: a benchmark from Felix's work

Note all the benchmark set above (links included in the source code) should be all synthesisable in your case, so you may be show coverage instead of a single benchmark.

Best,
Jianyi
