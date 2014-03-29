#!/bin/sh
cd src/
make
cd ..
cd tester/
make
./Grade $* . ..
cd ..
