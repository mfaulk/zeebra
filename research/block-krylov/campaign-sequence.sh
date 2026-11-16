#!/usr/bin/env bash
set -u
B=/buildcache/cargo-target/zeebra-731/release/examples/block_krylov_study
export ZEEBRA_MACHINE=5995wx
sq() { ZEEBRA_AFFINITY=8-15 timeout 900 taskset -c 8-15 $B --mode sequence "$@"; echo "exit=$?"; }
echo "=== sequence"; date -u
sq --family cyclic --variables 5 --repeats 5
sq --family cyclic --variables 6 --repeats 5
sq --family dense --variables 5 --repeats 5
sq --family cyclic --variables 6 --field babybear --repeats 5
sq --family cyclic --variables 6 --field goldilocks --repeats 5
date -u
