#!/bin/bash
make -j 10 -C src/
make -j 10 -C tools/
make install
cd tools/io_fault/
make
