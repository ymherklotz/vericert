all:
	$(MAKE) -C stencils
	$(MAKE) -C medley
	$(MAKE) -C linear-algebra/blas
	$(MAKE) -C linear-algebra/kernels
	$(MAKE) -C linear-algebra/solvers
	$(MAKE) -C data-mining

clean:
	$(MAKE) clean -C stencils
	$(MAKE) clean -C medley
	$(MAKE) clean -C linear-algebra/blas
	$(MAKE) clean -C linear-algebra/kernels
	$(MAKE) clean -C linear-algebra/solvers
	$(MAKE) clean -C data-mining
