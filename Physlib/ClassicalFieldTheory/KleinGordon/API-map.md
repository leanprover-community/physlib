# Retarded propagation for the Klein–Gordon equation

## Abstract (Alpha)

In three spatial dimensions the retarded response of a massless scalar field depends only
on source values on the past light cone of the observation point. A massive scalar field
also responds to source values inside that cone. Kirchhoff's spherical mean gives the
light-cone term in both cases, while a Bessel function determines the massive tail.

## Content (Alpha)

### The retarded field

Let $f(t,x)$ be a smooth, compactly supported complex source on Minkowski spacetime with
three spatial dimensions and $c=1$. The retarded solution of
$(\partial_t^2-\Delta+m^2)\phi=f$ is obtained by propagating the source at each earlier
time $s$ for a duration $t-s$ and integrating over $s\le t$. [1] Its support lies in
the causal future of the support of $f$. [2] The corresponding retarded and advanced
inverses are described in the Green operators API map. {1}

### The massless field on the light cone

Write $M_r g(x)$ for the average of $g(x+r n)$ over unit directions $n$, with the solid
angle measure divided by $4\pi$. [3] For $m=0$, the contribution from a source slice at
time $s$ is $(t-s)M_{t-s}f(s,\cdot)(x)$. [4][5] Hence only source values at distance
$t-s$ from $x$ enter that slice's contribution. Once the expanding sphere has passed the
support of a slice, its contribution vanishes, as the strong Huygens principle predicts. [4]

### The massive tail inside the cone

For $m>0$, each source slice contributes the same Kirchhoff term and an integral of
spherical means over smaller radii. The formula gives the retarded field at $(t,x)$
for every smooth, compactly supported source. [6] In kernel notation, write $\tau=t-s$
for the elapsed time, $r=|x-y|$ for the distance to the source point $y$, and
$\sigma=\sqrt{\tau^2-r^2}$ for the proper time inside the cone. The cone term is
$\delta(\tau-r)/(4\pi r)$. The interior term has density $-m J_1(m\sigma)/(4\pi\sigma)$
for $0\le r<\tau$, where $J_1$ is the Bessel function of the first kind of order one.
[6][7] {2}

## Lean References

1. PhyslibAlpha/ClassicalFieldTheory/KleinGordon/RetardedSolution.lean — `solution_equation_at`,
   `solution_eq_integral`
2. PhyslibAlpha/ClassicalFieldTheory/KleinGordon/FinitePropagation.lean — `tsupport_solution_subset`
3. PhyslibAlpha/ClassicalFieldTheory/WaveEquation/Kirchhoff/Setting.lean — `sphericalIntegral`, `sphericalMean`
4. PhyslibAlpha/ClassicalFieldTheory/WaveEquation/Kirchhoff/Propagator.lean —
   `wavePropagator_eq_time_sphericalMean`, `wavePropagator_eq_zero_of_near`
5. PhyslibAlpha/ClassicalFieldTheory/KleinGordon/ClosedForm/MasslessSpace.lean — `solution_zero_mass_three`
6. PhyslibAlpha/ClassicalFieldTheory/KleinGordon/ClosedForm/MassiveSpace.lean — `solution_mass_three_besselJ1`
7. PhyslibAlpha/Mathematics/SpecialFunctions/SincPropagator/Bessel.lean — `besselJ1`

## References

1. Green operators and the causal propagator API map — Physlib/ClassicalFieldTheory/GreenOperator/API-map.md
2. P. Forgács and Á. Lukács, [Charge screening in the Abelian Higgs model](https://link.springer.com/article/10.1140/epjc/s10052-021-09022-x#Equ66).
   European Physical Journal C 81, 243 (2021), Appendix B, Eq. (66).
