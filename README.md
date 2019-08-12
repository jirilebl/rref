# Sharp polynomial testing

See e.g. https://arxiv.org/pdf/1302.1441.pdf

# Here is the old README

To run edit rref-v3.c to source in the correct header file for the degree you
wish to run.  Then run

./runtest.sh

That will compile and do a quick check of a random place in the search space to
generate profile, then recompile and run the full test.

By default we are using degree 15, which does not take too long and so the run
for profile generation is not really useful; 15 should finish rather quickly
on current hardware.
