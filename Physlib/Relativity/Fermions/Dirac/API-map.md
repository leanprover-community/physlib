# Dirac Fermions

A Dirac fermion is the four-component spinor built from a left-handed Weyl fermion together
with a dual right-handed one. It is a complex vector space with a four-element chiral basis,
carrying the representation of SL(2, ℂ) induced from its two Weyl factors.

The gamma endomorphisms are defined directly in the chiral basis, and satisfy the Clifford
relations for the Minkowski signature (+,−,−,−). Their chirality operator gives complementary
left and right chiral projectors. A change of coordinates derives the concrete gamma matrices
of the Dirac representation from those endomorphisms; they generate the Dirac algebra and
realize it as a quotient of the Clifford algebra of the Minkowski quadratic form.

Completing this API is what will allow the Dirac equation, the Dirac bilinears, and the
fermionic terms of the Standard Model Lagrangian to be stated.

## Built on

- Weyl Fermions — `Physlib/Relativity/Fermions/Weyl`
- Lorentz Group — `Physlib/Relativity/LorentzGroup`

## Requirements

The key data structure is defined: a Dirac fermion, a left-handed Weyl fermion together with a
dual right-handed one. [1]

A Dirac fermion is a complex vector space, inheriting the structure of its two Weyl
components. [2]

Decomposing a Dirac fermion into its Weyl components is a complex linear equivalence. [3]

The four-element chiral basis is defined, and its elements are identified with the Weyl basis
elements. [4]

Dirac fermions carry a representation of SL(2, ℂ), acting componentwise on the two Weyl
factors. [5]

That representation is equivalent to the product of the representations on the Weyl
components. [6]

The gamma matrices of the Dirac representation are derived from the gamma endomorphisms,
together with the chirality matrix and the set they form. [7]

Those gamma matrices satisfy the Clifford anticommutator against the Minkowski metric, in the
signature (+,−,−,−). [8]

The Dirac slash of a Lorentz vector is defined in the Dirac representation, contracting the
lowered vector coordinates with the gamma matrices; it is real linear, and extends to products
of slash factors. [9]

The Dirac algebra, generated over the reals by the Dirac representations of the gamma
endomorphisms, is defined, and contains each generator. [10]

The Minkowski quadratic form is defined, and the induced algebra map from its Clifford algebra
onto the Dirac algebra is surjective. [11]

That map will be shown to be an isomorphism. It is blocked on injectivity, which needs
dimension theory, and is recorded as a TODO in the source. [planned]

Clifford multiplication is a real linear map from Lorentz vectors to complex linear
endomorphisms of the Dirac fermions, using the chiral basis and the library's Pauli-matrix
conventions; the upper-index gamma components are derived from it on the Lorentz basis. [12]

Clifford multiplication satisfies the anticommutator for arbitrary Lorentz vectors and their
Minkowski product, from which the component relations, the squares and the anticommutation for
distinct indices follow in the signature (+,−,−,−). [13]

The chirality endomorphism is defined, has chiral matrix diag(−1,−1,1,1), squares to the
identity, and anticommutes with every gamma endomorphism. [14]

The left and right chiral projectors have the corresponding diagonal matrices, are idempotent
and orthogonal, and sum to the identity. [15]

The chiral projectors will be shown to be Lorentz equivariant. [planned]

An algebra equivalence converts Dirac endomorphisms into the Dirac representation, with an
explicit change-of-coordinates formula from the chiral basis. [16]

The Dirac adjoint of a Dirac fermion will be defined. [planned]

The Dirac bilinears will be defined, with their behaviour under the action of SL(2, ℂ). [planned]

The Dirac equation will be stated for a spinor field on spacetime. [planned]

The charge conjugate of a Dirac fermion, and the Majorana condition, will be defined. [planned]

## Further reading

- Dreiner, Haber and Martin, Two-component spinor techniques and Feynman rules for quantum field theory and supersymmetry, Phys. Rept. 494 (2010) 1-196. https://arxiv.org/abs/0812.1594 (Dirac fermions are treated on page 197 of the arXiv version)

## Lean declarations

1. Physlib/Relativity/Fermions/Dirac/Basic.lean — `Dirac`
2. Physlib/Relativity/Fermions/Dirac/Basic.lean — `AddCommGroup Dirac`, `Module ℂ Dirac`,
   `left_add`, `dualRight_add`, `left_smul`, `dualRight_smul`
3. Physlib/Relativity/Fermions/Dirac/Basic.lean — `decomposeEquiv`, `decomposeLinEquiv`
4. Physlib/Relativity/Fermions/Dirac/Basic.lean — `chiralBasis`, `chiralBasis_cast_add`,
   `chiralBasis_nat_add`
5. Physlib/Relativity/Fermions/Dirac/Basic.lean — `rep`, `rep_apply_mk`
6. Physlib/Relativity/Fermions/Dirac/Basic.lean — `decomposeRepEquiv`
7. Physlib/Relativity/CliffordAlgebra.lean — `γ0`, `γ1`, `γ2`, `γ3`, `γ5`,
   `γ5_eq_endEquivMatrix`, `γSet`, `γ_in_γSet`
8. Physlib/Relativity/CliffordAlgebra.lean — `γ_anticomm`
9. Physlib/Relativity/Fermions/Dirac/Slash.lean — `Slash.slash`, `notation k̸`,
   `Slash.slash_eq_sum`, `Slash.slashLinear`, `Slash.slash_zero`, `Slash.slash_add`,
   `Slash.slash_smul`, `Slash.slashMulLeft`, `Slash.slashProd`, `Slash.slashProd_nil`,
   `Slash.slashProd_cons`
10. Physlib/Relativity/CliffordAlgebra.lean — `diracAlgebra`, `γSet_subset_diracAlgebra`,
   `γ_in_diracAlgebra`
11. Physlib/Relativity/CliffordAlgebra.lean — `diracForm`, `ofCliffordAlgebra`,
   `ofCliffordAlgebra_ι_single`, `ofCliffordAlgebra_range_eq_top`,
   `ofCliffordAlgebra_surjective`
12. Physlib/Relativity/Fermions/Dirac/GammaMatrices.lean — `gammaMatrix`,
   `gammaMatrix_toMatrix`, `gammaMatrix_basis_toMatrix`, `gamma`, `gammaMatrix_basis`,
   `gammaMatrix_eq_sum`, `gamma_toMatrix`
13. Physlib/Relativity/Fermions/Dirac/GammaMatrices.lean — `gammaMatrix_basis_anticomm`,
   `gammaMatrix_anticomm`, `gammaMatrix_mul_self`, `gamma_anticomm`, `gamma_mul_self`,
   `gamma_inl_zero_mul_self`, `gamma_inr_mul_self`, `gamma_mul_gamma_of_ne`
14. Physlib/Relativity/Fermions/Dirac/GammaMatrices.lean — `gamma5`, `gamma5_toMatrix`,
   `gamma5_mul_self`, `gamma5_mul_gamma`, `gamma5_mul_gammaMatrix`
15. Physlib/Relativity/Fermions/Dirac/GammaMatrices.lean — `leftChiralProjector`,
   `rightChiralProjector`, `leftChiralProjector_toMatrix`, `rightChiralProjector_toMatrix`,
   `leftChiralProjector_mul_self`, `rightChiralProjector_mul_self`,
   `leftChiralProjector_mul_rightChiralProjector`,
   `rightChiralProjector_mul_leftChiralProjector`,
   `leftChiralProjector_add_rightChiralProjector`
16. Physlib/Relativity/Fermions/Dirac/Basic.lean — `endEquivMatrix`, `endEquivMatrix_apply`
