# Groebner.jl's view of tools/external/smoke/system.ms.
#
# Two orderings are in play and they are not the same thing. `internal_ordering=` is the
# AbstractAlgebra ring's term order, which is what `leading_monomial` reports; `ordering=` is
# what Groebner.jl computes with respect to. Setting only the second gives a correct basis
# whose leading monomials are reported against the wrong order — see
# docs/research/external-comparands.md. Both are degrevlex here, deliberately.
#
# Variable order is the order of the name vector: x > y > z.

using Groebner, AbstractAlgebra

const P = 1073741827

R, (x, y, z) = polynomial_ring(GF(P), ["x", "y", "z"]; internal_ordering = :degrevlex)
system = [x^2 + y^2 + z^2 - 1, x*y + y*z + z*x - 1, x*y*z - 1]

# One untimed call first: Groebner.jl is JIT-compiled, so a cold call measures the compiler.
groebner(system; ordering = DegRevLex())
elapsed = @elapsed g = groebner(system; ordering = DegRevLex())

println("#engine:               Groebner.jl $(pkgversion(Groebner))")
println("#field characteristic: $P")
println("#variable order:       x, y, z")
println("#monomial order:       degrevlex (DegRevLex(), ring internal_ordering=:degrevlex)")
println("#length of basis:      $(length(g)) elements")
println("#threads:              $(Threads.nthreads())")
println("#seconds:              $elapsed")
for p in g
    println(p)
end
println("--- leading monomials ---")
for p in g
    println(leading_monomial(p))
end
