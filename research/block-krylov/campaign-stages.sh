#!/usr/bin/env bash
set -u
B=/buildcache/cargo-target/zeebra-731/release/examples/block_krylov_study
export ZEEBRA_MACHINE=5995wx
st() { ZEEBRA_AFFINITY=8 timeout 600 taskset -c 8 $B --mode stages "$@"; echo "exit=$?"; }
echo "=== stages"; date -u
for n in 5 6; do st --family cyclic --variables $n --repeats 5; done
st --family dense --variables 5 --repeats 5
st --family dense --variables 6 --repeats 3
st --family powers --variables 5 --repeats 5
st --family nonradical --variables 5 --repeats 3
st --family cyclic --variables 5 --route classical --repeats 3
st --family cyclic --variables 7 --repeats 1
date -u
