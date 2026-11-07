#  Groebner.jl's own pair, matrix, row and per-stage counters on a digest-pinned Zeebra instance.
#
#    . tools/external/env.sh
#    cargo run --release --example f4_profile -- mq-instance > /tmp/mq.canonical
#    tools/benchlock.sh <tag> taskset -c 0-7 \
#        julia -t1 tools/external/groebner-jl-counts.jl /tmp/mq.canonical
#
#  Reads `Instance::canonical` — the text the identity digest is taken over — and echoes the digest
#  and the generators back, so a comparison of two engines' counters is a comparison on one ideal.
#  The ring, the ordering and the `tasks =` value mirror `src/grobner/external/groebner_jl.rs`'s
#  generated script exactly, including the two-element proxy warm-up, so what is counted here is
#  what the competitive board timed.
#
#  Groebner.jl is GPL-2.0 and an **algorithmic reference only** (`external-provenance-policy.md`
#  §3.3, §7). This script calls its public API from a separate process and copies nothing. It is a
#  measurement instrument, not part of the crate, and is not on any build path.
#
#  What it produces and why each piece is here is `docs/research/groebner-jl-gap.md` (#447).

import Groebner

using AbstractAlgebra

function read_canonical(path)
    digest = ""
    chr = 0
    vars = String[]
    gens = String[]
    for line in eachline(path)
        if startswith(line, "digest ")
            digest = String(strip(line[8:end]))
        elseif startswith(line, "characteristic ")
            chr = parse(Int, strip(line[16:end]))
        elseif startswith(line, "variables ")
            vars = String.(split(strip(line[11:end]), ","))
        elseif startswith(line, "generator ")
            push!(gens, String(strip(line[11:end])))
        end
    end
    (digest, chr, vars, gens)
end

digest, chr, vars, gens = read_canonical(ARGS[1])
println("@digest ", digest)
println("@char ", chr)
println("@nvars ", length(vars))
println("@gensize ", length(gens))

zb_F = AbstractAlgebra.GF(chr)
zb_R, zb_vars = AbstractAlgebra.polynomial_ring(zb_F, vars, internal_ordering=:degrevlex)
for (i, name) in enumerate(vars)
    @eval Main $(Symbol(name)) = $(zb_vars[i])
end
zb_sys = [Base.eval(Main, Meta.parse(g)) for g in gens]
for f in zb_sys
    println("@gen ", f)
end

ord = Groebner.DegRevLex()
ntasks = Base.Threads.nthreads()
println("@tasks ", ntasks)

# The adapter's warm-up: same ring, same ordering, result discarded.
zb_warm = [zb_vars[1]^2 + zb_vars[end] - 1, zb_vars[end]^2 - zb_vars[1]]
Groebner.groebner(zb_warm; ordering=ord, tasks=ntasks)
GC.gc()

# --- the JIT question: three successive timed calls in one process, the first being the one the
# --- board's figure is taken from.
for k in 1:3
    GC.gc()
    t0 = time_ns()
    G = Groebner.groebner(zb_sys; ordering=ord, tasks=ntasks)
    println("@solve_ns_", k, " ", time_ns() - t0, " gbsize ", length(G))
end

# --- deterministic linear algebra, which is what `groebner_learn` uses and what Zeebra does.
for k in 1:2
    GC.gc()
    t0 = time_ns()
    G = Groebner.groebner(zb_sys; ordering=ord, tasks=ntasks, linalg=:deterministic)
    println("@det_ns_", k, " ", time_ns() - t0, " gbsize ", length(G))
end

# --- the counters. `groebner_learn` runs `f4_learn!`, whose loop is `f4!`'s with a recorder
# --- attached (src/f4/learn_apply.jl:156-199 against src/f4/f4.jl:415-452).
GC.gc()
t0 = time_ns()
wrapped, G = Groebner.groebner_learn(zb_sys; ordering=ord)
println("@learn_ns ", time_ns() - t0)
println("@learn_gbsize ", length(G))
println("@trace_begin")
show(stdout, MIME("text/plain"), wrapped)
println()
println("@trace_end")

# `groebner_learn` hands back a `WrappedTrace`, which holds one specialized `Trace` per
# coefficient type (src/groebner/wrapped_trace.jl:6-15). One prime, one entry.
@assert length(wrapped.recorded_traces) == 1
trace = first(values(wrapped.recorded_traces))

# The trace's raw vectors, so the shares can be computed rather than eyeballed. The last entry of
# `matrix_infos` is `f4_reducegb_learn!`'s matrix — the final interreduction — because the main
# loop pushes one per iteration and the reduce-gb pass pushes one more
# (src/f4/learn_apply.jl:487 subtracts it to recover the iteration count).
infos = trace.matrix_infos
println("@matrix_count ", length(infos))
for (i, m) in enumerate(infos)
    println("@matrix ", i, " nup ", m.nup, " nlow ", m.nlow, " ncols ", m.ncols)
end
pairs = trace.critical_pair_sequence
println("@pair_batches ", length(pairs))
println("@pairs_total ", sum(last, pairs; init=0))
for (i, p) in enumerate(pairs)
    println("@pairbatch ", i, " degree ", p[1], " npairs ", p[2])
end
println("@nonzeroed ", sum(length, trace.matrix_nonzeroed_rows; init=0))
println("@upper_useful ", sum(length ∘ first, trace.matrix_upper_rows; init=0))
println("@lower_useful ", sum(length ∘ first, trace.matrix_lower_rows; init=0))
println("@hashtable_load ", trace.hashtable.load, " size ", trace.hashtable.size)
println("@monomtype ", trace.representation.monomtype)
println("@arithmetic ", typeof(trace.params.arithmetic))

# --- Groebner.jl's own per-stage timer, which ships disabled and is enabled here at runtime.
# TimerOutputs adds overhead to every `@timeit` site, so read the shares and not the total — the
# same caveat Zeebra's `measure_stages` carries (#349).
Groebner.TimerOutputs.reset_timer!(Groebner._TIMER)
Groebner.TimerOutputs.enable_timer!(Groebner._TIMER)
GC.gc()
t0 = time_ns()
G = Groebner.groebner(zb_sys; ordering=ord, tasks=ntasks)
elapsed = time_ns() - t0
Groebner.TimerOutputs.disable_timer!(Groebner._TIMER)
println("@timed_ns ", elapsed, " gbsize ", length(G))
println("@timer_begin")
show(stdout, Groebner._TIMER)
println()
println("@timer_end")

println("@dim ", Groebner.dimension(G))
println("@vdim ", length(Groebner.quotient_basis(G)))
println("@done 1")
