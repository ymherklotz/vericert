#include <stdlib.h>
#include <stdio.h>
#include "Vmain.h"
#include "verilated.h"

int main(int argc, char **argv) {
    // Initialize Verilators variables
    Verilated::commandArgs(argc, argv);

    // Create an instance of our module under test
    Vmain *tb = new Vmain;

    tb->clk = 0;
    tb->start = 0;
    tb->reset = 0;
    tb->eval(); tb->clk = 1; tb->eval(); tb->clk = 0; tb->eval();
    tb->reset = 1;
    tb->eval(); tb->clk = 1; tb->eval(); tb->clk = 0; tb->eval();
    tb->reset = 0;
    tb->eval(); tb->clk = 1; tb->eval(); tb->clk = 0; tb->eval();

    int cycles = 1;

    // Tick the clock until we are done
    while(!tb->finish) {
        tb->clk = 1;
        tb->eval();
        tb->clk = 0;
        tb->eval();
        cycles++;
    }

    printf("cycles: %d\nfinished: %d\n", cycles, (unsigned)tb->return_val);
    exit(EXIT_SUCCESS);
}
