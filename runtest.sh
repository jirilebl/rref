#!/bin/sh
echo compiling with profile generate
gcc -O9 -march=native -fomit-frame-pointer -fwhole-program -ffast-math -fno-stack-protector -fno-math-errno -funroll-loops -fprofile-generate rref-v3.c -lgmp  -o rref-v3
echo running to generate profile
DORANDOM=true JUSTQUIT=true ./rref-v3
echo compiling with profile 
gcc -O9 -march=native -fomit-frame-pointer -fwhole-program -ffast-math -fno-stack-protector -fno-math-errno -funroll-loops -fprofile-use rref-v3.c -lgmp -o rref-v3
echo running 
./rref-v3
