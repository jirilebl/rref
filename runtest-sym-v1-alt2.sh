#!/bin/sh
echo compiling with profile generate
gcc -O9 -march=native -fomit-frame-pointer -fwhole-program -ffast-math -fno-stack-protector -fno-math-errno -funroll-loops -fprofile-generate rref-sym-v1.c -lgmp  -o rref-sym-v1-alt2
echo running to generate profile
DORANDOM=true JUSTQUIT=true ./rref-sym-v1-alt2
echo compiling with profile 
gcc -O9 -march=native -fomit-frame-pointer -fwhole-program -ffast-math -fno-stack-protector -fno-math-errno -funroll-loops -fprofile-use rref-sym-v1.c -lgmp -o rref-sym-v1-alt2

#echo compiling without profile but optimized
#gcc -O9 -march=native -fomit-frame-pointer -fwhole-program -ffast-math -fno-stack-protector -fno-math-errno -funroll-loops rref-sym-v1.c -lgmp -o rref-sym-v1-alt2

#echo compiling without much optimizations
#gcc -O2 -march=native rref-sym-v1.c -lgmp -o rref-sym-v1-alt2

echo running 
./rref-sym-v1-alt2
