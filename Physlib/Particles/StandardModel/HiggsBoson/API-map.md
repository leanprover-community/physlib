# Higgs Field

## Abstract (Alpha)

A Higgs field is a smooth section of the Higgs bundle over spacetime, on which the global Standard
Model gauge group acts; for now the bundle is the trivial one, whose fibre is the two-dimensional
complex vector space of pointwise Higgs values. The pointwise values carry an orthonormal basis,
real scalar coordinates, and a gauge representation whose orbits are classified by the norm, while
fields carry constant fields, smooth components, a pointwise inner product and norm squared, the
Standard Model Higgs potential with its minimization theory, and invariant effective potentials on
pointwise values; the two Higgs doublet model builds on this area.

## Content (Alpha)

### Pointwise Higgs values

The pointwise Higgs values form a two-dimensional complex vector space, continuously and linearly
identified with pairs of complex numbers. [1] They carry an orthonormal basis, and a real mass
scale determines a Higgs vector with the expected norm. [2] They correspond to four real scalar
coordinates. [3]

The global Standard Model gauge group {1} acts on them through a representation, given explicitly as
a U(1) phase times an SU(2) matrix and compatible with the group law. [4] That representation
preserves inner products and norms. [5] Two Higgs vectors lie in the same gauge orbit exactly when
they have the same norm, and a gauge transformation can remove the phase of the second
component. [6] A nonzero Higgs vector breaks the gauge group to a subgroup SU(3) × U(1), and the
subgroup fixing every Higgs vector is SU(3) × ℤ₆. [7][TODO] Pairs of Higgs vectors, with this
gauge action, are the configurations of the two Higgs doublet model {2}.

### The Higgs bundle and Higgs fields

The Higgs bundle over spacetime {3} is a smooth vector bundle, currently the trivial bundle with
fibre the pointwise Higgs values. [8] It is the bundle associated to the gauge group, rather than
the trivial one. [TODO]

Higgs fields are smooth sections of the Higgs bundle; each has an underlying map to pointwise
Higgs values, and every Higgs vector gives a constant field. [9] The components of a Higgs field
are smooth, real and imaginary parts alike. [10] The pointwise inner product of two Higgs fields
has an explicit expansion, is conjugate symmetric and additive, and is smooth. [11] The pointwise
norm squared of a Higgs field is the real part of its inner product with itself, is nonnegative,
and is smooth. [12]

Gauge transformations act on Higgs fields pointwise; two Higgs fields lie in the same orbit
exactly when their pointwise norms squared agree, and every smooth nonnegative function on
spacetime is the norm squared of some Higgs field. [13][TODO] The pointwise inner product, the
norm squared and the potential are invariant under the global gauge action. [TODO]

### The Higgs potential

The Standard Model Higgs potential {4} has a mass parameter and a quartic coupling, and evaluates
smoothly on a Higgs field; negating both parameters negates the potential, and the potential
vanishes on the zero field. [14] Completing the square writes it as a quadratic in the norm squared,
whose discriminant is nonnegative and vanishes exactly in a characterized case. [15]

A bounded-below potential has nonnegative quartic coupling, and a positive quartic coupling makes
it bounded below. [16] The values it attains, its bounds when the discriminant vanishes, and its
minimum for positive and maximum for negative quartic coupling are all determined
explicitly. [16]

### Effective potentials

An effective potential is a function on pointwise Higgs values; when it is gauge invariant it is
constant on gauge orbits and so factors through the norm. [17] An effective potential of bounded
mass dimension is polynomial, splits into homogeneous terms of each mass dimension whose odd terms
vanish when it is invariant, and is then a sum of powers of the norm. [18] Effective potentials
determine potentials on Higgs fields, so that field-level statements follow from pointwise
invariant ones. [TODO] Higgs fields have covariant derivatives and kinetic terms, built from a
gauge connection over spacetime. [TODO]

## Lean References

1. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `HiggsVec`, `toFin2ℂ`,
   `smooth_toFin2ℂ`
2. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `orthonormBasis`, `ofReal`,
   `ofReal_normSq`
3. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `toRealScalars`,
   `toRealScalars_smul_real`, `ofReal_toRealScalars`, `ofReal_toRealScalars_norm`
4. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `repGaugeGroupI`,
   `repGaugeGroupI_apply`, `repGaugeGroupI_apply_eq_U1_mul_SU2`,
   `repGaugeGroupI_apply_eq_U1_smul_SU2`, `repGaugeGroupI_mul_apply`,
   `repGaugeGroupI_inv_apply_eq_iff`
5. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `repGaugeGroupI_inner`,
   `repGaugeGroupI_norm`
6. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `toRealGroupElem`,
   `toRealGroupElem_apply_self`, `exists_repGaugeGroupI_eq_iff_norm_eq`,
   `ofU1Subgroup_repGaugeGroupI_apply`, `repGaugeGroupI_phase_snd`
7. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `stability_group_single`,
   `stability_group`
8. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `HiggsBundle`
9. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `HiggsField`, `const`,
   `const_apply`, `toHiggsVec`, `toHiggsVec_smooth`, `const_toHiggsVec_apply`
10. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `contDiff`, `toVec_smooth`,
   `apply_smooth`, `apply_re_smooth`, `apply_im_smooth`, `toFin2ℂ_comp_toHiggsVec`
11. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `inner_apply`, `inner_eq_expand`,
   `inner_expand_conj`, `inner_symm`, `inner_add_left`, `inner_add_right`, `inner_zero_left`,
   `inner_zero_right`, `inner_neg_left`, `inner_neg_right`, `inner_smooth`
12. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `normSq`, `inner_self_eq_normSq`,
   `normSq_eq_inner_self_re`, `normSq_expand`, `normSq_nonneg`, `normSq_zero`, `normSq_smooth`,
   `const_normSq`
13. Physlib/Particles/StandardModel/HiggsBoson/Basic.lean — `gaugeAction`, `guage_orbit`,
   `gauge_orbit_surject`
14. Physlib/Particles/StandardModel/HiggsBoson/Potential.lean — `Potential`, `toFun`,
   `toFun_smooth`, `neg`, `toFun_neg`, `μ2_neg`, `𝓵_neg`, `toFun_zero`
15. Physlib/Particles/StandardModel/HiggsBoson/Potential.lean — `complete_square`, `as_quad`,
   `toFun_eq_zero_iff`, `quadDiscrim`, `quadDiscrim_nonneg`, `quadDiscrim_eq_zero_iff`,
   `quadDiscrim_eq_zero_iff_normSq`
16. Physlib/Particles/StandardModel/HiggsBoson/Potential.lean — `IsBounded`,
   `isBounded_𝓵_nonneg`, `isBounded_of_𝓵_pos`, `neg_𝓵_sol_exists_iff`, `pos_𝓵_sol_exists_iff`,
   `neg_𝓵_quadDiscrim_zero_bound`, `pos_𝓵_quadDiscrim_zero_bound`, `isMinOn_iff_field_of_𝓵_pos`,
   `isMaxOn_iff_field_of_𝓵_neg`
17. Physlib/Particles/StandardModel/HiggsBoson/EffectivePotential.lean — `EffectivePotential`,
   `IsInvariant`, `eq_on_orbits`, `eq_of_norm_eq`, `factors_through_norm`
18. Physlib/Particles/StandardModel/HiggsBoson/EffectivePotential.lean — `HasMaxMassDimLE`,
   `polynomial`, `apply_eq_polynomial`, `termOfMassDim`, `termOfMassDim_homogeneity`,
   `termOfMassDim_zero_of_odd`, `apply_eq_sum_norm_pow`

## References

1. Standard Model gauge group API map — Physlib/Particles/StandardModel/GaugeGroup/API-map.md
2. Two Higgs Doublet Model API map — Physlib/Particles/BeyondTheStandardModel/TwoHDM/API-map.md
3. Spacetime API map — Physlib/SpaceAndTime/SpaceTime/API-map.md
4. M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory*, Westview Press
   (1995), Ch. 20, on gauge theories with spontaneous symmetry breaking.
