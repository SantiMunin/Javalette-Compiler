#!/bin/sh
make -C src/ clean
make -C src/ bnfc
make -C src/
cd tester/
make
./Grade $* . ..
cd ..
