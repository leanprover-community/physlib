# Weyl Fermions

Weyl fermions are the two-component spinors carrying the fundamental representations of SL(2,
ℂ), the double cover of the restricted Lorentz group. The API is built around four types: the
left-handed and right-handed Weyl spinors, and their duals. Each is a complex vector space with
a two-element basis and a representation of SL(2, ℂ) on it.

On top of those sit the invariant contractions pairing a type with its dual, the epsilon
metrics that raise and lower spinor indices, the units realizing the duality, and the
identification of pairwise tensor products with 2 × 2 matrices. This API underlies the Dirac
fermion API and the fermionic sector of the Standard Model.

## Built on

- Lorentz Group — `Physlib/Relativity/LorentzGroup`

## Requirements

The first key data structure is defined: the left-handed Weyl spinors, with their complex
vector space structure. [1]

The second key data structure is defined: the right-handed Weyl spinors, with their complex
vector space structure. [2]

The duals of both are defined, with their complex vector space structures. [3][4]

Each of the four types carries a two-element basis, and every element expands in
it. [5][6][7][8]

Each carries a representation of SL(2, ℂ), with its matrix in that basis
identified. [9][10][11][12]

The invariant pairings between a Weyl type and its dual are defined, as bilinear maps and as
intertwining maps of representations. [13]

Those contractions are computed on basis elements, and their symmetry under exchange is
recorded. [14]

The epsilon metrics on each type are defined as intertwining maps out of the trivial
representation, and expanded in the basis. [15]

The interaction of the raw metric with SL(2, ℂ) is recorded, both directly and under the star
operation. [16]

Contracting a metric against the corresponding contraction is computed. [17]

The units realizing the duality between each type and its dual are defined, and contracting one
with a spinor returns that spinor. [18]

Each unit is symmetric under exchange of its two factors. [19]

The dual of the left-handed representation is identified with the representation on the dual
left-handed spinors. [20]

Pairwise tensor products of the Weyl types are identified with 2 × 2 complex matrices,
equivariantly for the action of SL(2, ℂ). [21]

The same equivalence will be given for the right-handed spinors and their dual, together with
its equivariance. Both are present only as informal statements. [22][planned]

The right-handed representation will be identified with the complex conjugate of the
left-handed one. [planned]

The Weyl equation will be stated for a massless spinor field. [planned]

The Majorana condition, relating a left-handed Weyl fermion to a right-handed one, will be
stated. [planned]

## Further reading

- Dreiner, Haber and Martin, Two-component spinor techniques and Feynman rules for quantum field theory and supersymmetry, Phys. Rept. 494 (2010) 1-196. https://arxiv.org/abs/0812.1594

## Lean declarations

1. Physlib/Relativity/Fermions/Weyl/LeftHanded.lean — `LeftHandedWeyl`,
   `AddCommMonoid LeftHandedWeyl`, `AddCommGroup LeftHandedWeyl`, `Module ℂ LeftHandedWeyl`,
   `toFin2ℂFun`, `toFin2ℂEquiv`, `toFin2ℂ`
2. Physlib/Relativity/Fermions/Weyl/RightHanded.lean — `RightHandedWeyl`,
   `AddCommMonoid RightHandedWeyl`, `AddCommGroup RightHandedWeyl`, `Module ℂ RightHandedWeyl`,
   `toFin2ℂFun`, `toFin2ℂEquiv`, `toFin2ℂ`
3. Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean — `DualLeftHandedWeyl`,
   `AddCommGroup DualLeftHandedWeyl`, `Module ℂ DualLeftHandedWeyl`, `toFin2ℂEquiv`
4. Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean — `DualRightHandedWeyl`,
   `AddCommGroup DualRightHandedWeyl`, `Module ℂ DualRightHandedWeyl`, `toFin2ℂEquiv`
5. Physlib/Relativity/Fermions/Weyl/LeftHanded.lean — `basis`, `basis_apply`, `basis_val`,
   `eq_sum_basis`
6. Physlib/Relativity/Fermions/Weyl/RightHanded.lean — `basis`, `basis_apply`, `basis_val`,
   `eq_sum_basis`
7. Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean — `basis`, `basis_apply`, `basis_val`,
   `eq_sum_basis`
8. Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean — `basis`, `basis_apply`, `basis_val`,
   `eq_sum_basis`
9. Physlib/Relativity/Fermions/Weyl/LeftHanded.lean — `rep`, `rep_apply`, `rep_toMatrix`,
   `rep_apply_basis`, `rep_apply_basis_repr`
10. Physlib/Relativity/Fermions/Weyl/RightHanded.lean — `rep`, `rep_apply`, `rep_toMatrix`,
   `rep_apply_basis`, `rep_apply_basis_repr`
11. Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean — `rep`, `rep_toMatrix`,
   `rep_apply_basis`, `rep_apply_basis_repr`
12. Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean — `rep`, `rep_apply`, `rep_toMatrix`,
   `rep_apply_basis`, `rep_apply_basis_repr`
13. Physlib/Relativity/Fermions/Weyl/Contraction.lean — `leftDualBi`, `dualLeftBi`,
   `rightDualBi`, `dualRightBi`, `leftDualContraction`, `dualLeftContraction`,
   `rightDualContraction`, `dualRightContraction`
14. Physlib/Relativity/Fermions/Weyl/Contraction.lean — `leftDualContraction_basis`,
   `dualLeftContraction_basis`, `rightDualContraction_basis`, `dualRightContraction_basis`,
   `leftDualContraction_tmul_symm`, `dualLeftContraction_tmul_symm`,
   `rightDualContraction_tmul_symm`, `dualRightContraction_tmul_symm`
15. Physlib/Relativity/Fermions/Weyl/Metric.lean — `metricRaw`, `leftMetric`, `dualLeftMetric`,
   `rightMetric`, `dualRightMetric`, `leftMetricVal`, `dualLeftMetricVal`, `rightMetricVal`,
   `dualRightMetricVal`, `leftMetricVal_expand_tmul`, `dualLeftMetricVal_expand_tmul`,
   `rightMetricVal_expand_tmul`, `dualRightMetricVal_expand_tmul`
16. Physlib/Relativity/Fermions/Weyl/Metric.lean — `comm_metricRaw`, `metricRaw_comm`,
   `star_comm_metricRaw`, `metricRaw_comm_star`
17. Physlib/Relativity/Fermions/Weyl/Metric.lean — `leftDualContraction_apply_metric`,
   `dualLeftContraction_apply_metric`, `rightDualContraction_apply_metric`,
   `dualRightContraction_apply_metric`
18. Physlib/Relativity/Fermions/Weyl/Unit.lean — `leftDualLeftUnit`, `dualLeftLeftUnit`,
   `rightDualRightUnit`, `dualRightRightUnit`, `contr_dualLeftLeftUnit`,
   `contr_leftDualLeftUnit`, `contr_dualRightRightUnit`, `contr_rightDualRightUnit`
19. Physlib/Relativity/Fermions/Weyl/Unit.lean — `dualLeftLeftUnit_symm`,
   `leftDualLeftUnit_symm`, `dualRightRightUnit_symm`, `rightDualRightUnit_symm`
20. Physlib/Relativity/Fermions/Weyl/Duals.lean — `LeftHandedWeyl.dual`,
   `DualLeftHandedWeyl.dual`, `LeftHandedWeyl.dualEquiv`, `LeftHandedWeyl.dual_hom_apply`,
   `DualLeftHandedWeyl.dual_hom_apply`
21. Physlib/Relativity/Fermions/Weyl/Two.lean — `leftLeftToMatrix`, `dualLeftdualLeftToMatrix`,
   `leftDualLeftToMatrix`, `dualLeftLeftToMatrix`, `rightRightToMatrix`,
   `dualRightDualRightToMatrix`, `rightDualRightToMatrix`, `dualRightRightToMatrix`,
   `dualLeftDualRightToMatrix`, `leftRightToMatrix`, `leftLeftToMatrix_ρ`,
   `dualLeftdualLeftToMatrix_ρ`, `leftDualLeftToMatrix_ρ`, `dualLeftLeftToMatrix_ρ`,
   `rightRightToMatrix_ρ`, `dualRightDualRightToMatrix_ρ`, `rightDualRightToMatrix_ρ`,
   `dualRightRightToMatrix_ρ`, `dualLeftDualRightToMatrix_ρ`, `leftRightToMatrix_ρ`
22. Physlib/Relativity/Fermions/Weyl/Duals.lean — `RightHandedWeyl.dualEquiv`,
   `RightHandedWeyl.dualEquiv_equivariant`
