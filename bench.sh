#!/bin/bash

set -ve

for n in 100 1000 10000 100000 1000000;
    do
        python3.7 electoralroll.py bench $n | tee reports/report-bench-$n.txt
    done

