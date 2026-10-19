# Weyl Fermions

## Abstract (Alpha)

Weyl fermions are the two-component spinors carrying the fundamental representations of SL(2, ℂ),
the double cover of the restricted Lorentz group. There are four of them — the left-handed and
right-handed Weyl spinors and their duals — each a complex vector space with a two-element basis and
a representation of SL(2, ℂ); on top of these sit the invariant contractions pairing each type with
its dual, the epsilon metrics that raise and lower spinor indices, the units realizing the duality,
and the identification of pairwise tensor products with 2 × 2 matrices. They underlie the Dirac
fermions and the fermionic sector of the Standard Model.

## Content (Alpha)

### The four spinor spaces

A left-handed Weyl spinor ψ_α is an element of a two-dimensional complex vector space. [1] A
right-handed Weyl spinor ψ^{α̇} is likewise an element of a two-dimensional complex vector space.
[2] Each has a dual, ψ^α and ψ_{α̇}, again a complex vector space. [3][4] Each of the four spaces
has a two-element basis, and every spinor expands in it. [5][6][7][8] Each carries a representation
of SL(2, ℂ), the double cover of the restricted Lorentz group {1}, whose matrix in that basis is the
defining matrix, its conjugate, its inverse transpose or its inverse conjugate transpose as
appropriate. [9][10][11][12] Each of these representations is irreducible, and Schur's lemma
holds for it: an endomorphism commuting with the representation is a scalar multiple of the
identity. [23][24][25][26] Weyl fermions are the building blocks of Dirac fermions {2}, and the
two-component formalism follows Dreiner, Haber and Martin {3}.

### Contractions, metrics and units

Each Weyl type pairs invariantly with its dual, giving bilinear maps that are also intertwining
maps of representations. [13] On basis elements these contractions are Kronecker deltas, and
each is symmetric under exchanging its two factors. [14]

The epsilon metrics ε_{αβ}, ε^{αβ}, ε_{α̇β̇} and ε^{α̇β̇} are invariant tensors, intertwining
maps out of the trivial representation, with explicit expansions in the basis. [15] Their
invariance rests on the raw epsilon matrix ε intertwining M ∈ SL(2, ℂ) with its inverse transpose,
Mε = ε(M⁻¹)ᵀ, and the complex conjugate of M with its inverse conjugate transpose. [16]
Contracting a metric with the metric of the dual type over one index gives the unit,
ε_{αβ}ε^{βγ} = δ_α^γ, and likewise for the other types. [17]

The units δ_α^β and δ^{α̇}_{β̇} realize the duality between each type and its dual, and
contracting a unit with a spinor returns that spinor. [18] Each unit is symmetric under exchange
of its two factors. [19]

### Duality and matrices

The dual of the left-handed representation is the representation on the dual left-handed
spinors. [20] The dual of the right-handed representation is the representation on the dual
right-handed spinors, equivariantly for SL(2, ℂ). [22][TODO] Pairwise tensor products of the
Weyl types are 2 × 2 complex matrices, equivariantly for the action of SL(2, ℂ). [21] The
right-handed representation is the complex conjugate of the left-handed one. [TODO]

### Field equations

A massless spinor field obeys the Weyl equation. [TODO] The Majorana condition relates a
left-handed Weyl fermion to a right-handed one. [TODO]

## Lean References

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
11. Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean — `rep`, `rep_apply`, `rep_toMatrix`,
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
23. Physlib/Relativity/Fermions/Weyl/LeftHanded.lean — `finrank_eq_two`, `eq_zero_of_rep_eq_smul`,
   `eq_bot_or_eq_top_of_rep_mem`, `end_eq_smul_id_of_commute_rep`
24. Physlib/Relativity/Fermions/Weyl/RightHanded.lean — `finrank_eq_two`, `eq_zero_of_rep_eq_smul`,
   `eq_bot_or_eq_top_of_rep_mem`, `end_eq_smul_id_of_commute_rep`
25. Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean — `finrank_eq_two`, `eq_zero_of_rep_eq_smul`,
   `eq_bot_or_eq_top_of_rep_mem`, `end_eq_smul_id_of_commute_rep`
26. Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean — `finrank_eq_two`, `eq_zero_of_rep_eq_smul`,
   `eq_bot_or_eq_top_of_rep_mem`, `end_eq_smul_id_of_commute_rep`

## References

1. Lorentz Group API map — Physlib/Relativity/LorentzGroup/API-map.md
2. Dirac Fermions API map — Physlib/Relativity/Fermions/Dirac/API-map.md
3. H. K. Dreiner, H. E. Haber and S. P. Martin, *Two-component spinor techniques and Feynman rules
   for quantum field theory and supersymmetry*, Phys. Rept. 494 (2010) 1–196, arXiv:0812.1594,
   https://arxiv.org/abs/0812.1594.
