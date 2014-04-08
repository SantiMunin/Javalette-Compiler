#!/bin/sh
make -C src/
cd tester/
make
./Grade $* . ..
cd ..
