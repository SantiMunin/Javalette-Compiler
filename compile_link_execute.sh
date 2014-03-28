#!/bin/sh
./jlc $1.jl
llvm-as $1.ll
llvm-link $1.bc lib/Runtime.bc | lli
