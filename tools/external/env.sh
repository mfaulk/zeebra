# shellcheck shell=bash
# Sourced, not executed: puts the M25 external comparands on PATH.
#
#   . tools/external/env.sh
#
# JULIA_DEPOT_PATH is set so Groebner.jl resolves out of the prefix rather than ~/.julia; a
# Julia invoked without it will not see the pinned package set.

ZEEBRA_EXT_PREFIX="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
export ZEEBRA_EXT_PREFIX

export PATH="$ZEEBRA_EXT_PREFIX/bin:$PATH"

# msolve has the prefix in its RPATH and runs without this; it is set for anything else linked
# against the prefix's GMP/MPFR/FLINT, and prepended so a system copy cannot shadow it.
export LD_LIBRARY_PATH="$ZEEBRA_EXT_PREFIX/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

export JULIA_DEPOT_PATH="$ZEEBRA_EXT_PREFIX/julia-depot"

# Sagebrush's F4 reads this for its thread count and otherwise takes
# available_parallelism() — all 128 hardware threads on this machine, which is not a
# comparable default. Benchmarks must set it explicitly.
# export SAGEBRUSH_THREADS=1
