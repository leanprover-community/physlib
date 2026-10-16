# Higgs Field

A Higgs field is a smooth section of the Higgs bundle over spacetime. The bundle is for now the
trivial one, whose fibre is the two-dimensional complex vector space of pointwise Higgs values.

On those pointwise values the API gives an orthonormal basis, real scalar coordinates, the
representation of the global Standard Model gauge group with its invariance properties, and the
characterization of gauge orbits by the norm. On fields it gives the constant fields, the
smoothness of the components, the pointwise inner product and norm squared, the Standard Model
Higgs potential with its minimization theory, and the invariant effective potentials on
pointwise values. The two Higgs doublet model builds on this API.

## Built on

- SpaceTime — `Physlib/SpaceAndTime/SpaceTime`
- Standard Model gauge group — `Physlib/Particles/StandardModel`

## Requirements

The pointwise Higgs values are defined, as a two-dimensional complex vector space, with their
continuous linear identification with pairs of complex numbers. [1]

They carry an orthonormal basis, and a vector can be built from a real mass scale with the
expected norm. [2]

They are related to four real scalar coordinates. [3]

The global Standard Model gauge group is represented on them, with the explicit form of the
representation and the lemmas governing the group law. [4]

That representation preserves inner products and norms. [5]

Gauge orbits of pointwise Higgs values are characterized by the norm, and the gauge action can
remove the phase of the second component. [6]

The stability groups of Higgs vectors will be identified. Informal statements of both results
stand in the source. [7][planned]

The Higgs bundle over spacetime is defined, as a smooth vector bundle. [8]

The Higgs bundle will be upgraded from the trivial bundle to an associated-bundle
construction. [planned]

Higgs fields are defined as smooth sections of that bundle, with the constant fields and the
underlying map to pointwise Higgs values. [9]

The components of a Higgs field are smooth, real and imaginary parts alike. [10]

The pointwise inner product of two Higgs fields is defined, with its expansion, its conjugation
symmetry, its additivity and its smoothness. [11]

The pointwise norm squared of a Higgs field is defined, with its relation to the inner product,
its nonnegativity and its smoothness. [12]

The global gauge action on Higgs fields will be defined, and the pointwise inner product, the
norm squared and the potential shown invariant under it. Informal statements stand in the
source. [13][planned]

The Standard Model Higgs potential is defined, carrying its mass and coupling parameters,
evaluated smoothly on a Higgs field, with the lemmas for negation and for the zero field. [14]

The algebraic theory of the potential is developed: completing the square, the quadratic form
in the norm squared, and the discriminant with its sign and its vanishing characterized. [15]

Boundedness of the potential is defined and its extremal theory proved: the values attained,
the bounds at vanishing discriminant, and the minimum and maximum for positive and for
negative quartic coupling. [16]

Effective potentials on pointwise Higgs values are defined, with their gauge invariance and the
proof that an invariant one factors through the norm. [17]

An effective potential of bounded mass dimension expands polynomially, with its homogeneous
terms, the vanishing of the odd ones for an invariant potential, and the expansion in powers of
the norm. [18]

Effective potentials will be connected to potentials on Higgs fields, so that field-level
statements follow from pointwise invariant ones. [planned]

Covariant derivatives and kinetic terms for Higgs fields will be defined. This waits on a
gauge-connection API, and on the spacetime API above. [planned]

## Further reading

- Peskin and Schroeder, An Introduction to Quantum Field Theory, Ch. 20 (gauge theories with spontaneous symmetry breaking)

## Lean declarations

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
