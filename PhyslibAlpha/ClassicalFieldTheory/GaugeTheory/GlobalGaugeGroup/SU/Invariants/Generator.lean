/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.SU.Invariants.AdjUnit
/-!
# The generator tensor of `SU(N)`

Up to scale, the generators `(Tᵃ)_i^j = (λ_a)_{ij} / 2` form the only invariant tensor with an
adjoint, a fundamental and an anti-fundamental index.

## i. Overview

An element of `ℂᴺ ⊗ ℂᴺ`, with the fundamental and the anti-fundamental representation, is a
matrix of components moved by `g` to `g X g⁻¹` (`pairMatrix`). Writing the matrix of an element
of the complexified Lie algebra in this way is an equivariant map `adjToPair` from the adjoint
representation (A).

An element `x` of `adj ⊗ U`, for any representation `U`, is a linear map `adj → U` once its first
index is contracted against the argument with the trace form (`adjContract`). This identifies
`adj ⊗ U` with the linear maps, and an invariant `x` gives an equivariant map (B).

An equivariant linear map `Φ` from the adjoint representation to the matrices is a multiple of
the matrix of the argument (C). Its trace is an invariant linear form, which by the trace form
is an invariant of the adjoint representation and so vanishes. Then `Φ` lands in the traceless
matrices, that is in the complexified Lie algebra, and commutes with the adjoint action, so it is
scalar.

The generator tensor `generatorVal N` is the unit `∑ b_a ⊗ bᵃ` of the adjoint color with its
second factor written as a matrix, in `adj ⊗ (ℂᴺ ⊗ ℂᴺ)`, and it is invariant (D). As a linear map
`adj → ℂᴺ ⊗ ℂᴺ` it is `adjToPair`. So an invariant `x` gives a map which, written as matrices, is
equivariant and hence a multiple of the matrix of the argument, and `x` is that multiple of the
generator tensor (E). The tensor `generator N`, with an adjoint, a fundamental and an
anti-fundamental index, has the components `(λ_a)_{ij} / 2` (F).

## ii. Key results

- `suTensor.pairMatrix` : the components of an element of `ℂᴺ ⊗ ℂᴺ` as a matrix.
- `suTensor.exists_eq_smul_adjMat_of_equivariant` : an equivariant map from the adjoint
  representation to the matrices is a multiple of the matrix of the argument.
- `suTensor.generatorVal` : the generator tensor.
- `suTensor.invariants_tprod_eq_span_generatorVal` : the invariants of
  `adj ⊗ (ℂᴺ ⊗ ℂᴺ)` are the line through the generator tensor.
- `suTensor.generator` : the generator tensor with an adjoint, a fundamental and an
  anti-fundamental index.
- `suTensor.invariants_adj_fund_antiFund_eq_span_generator` : the invariant tensors with these
  indices are the line through it.
- `suTensor.basis_repr_generator` : its components are the entries of `λ_a / 2`.

## iii. Table of contents

- A. A fundamental and an anti-fundamental index as a matrix
- B. Contracting an adjoint index
- C. Equivariant maps from the adjoint representation to the matrices
- D. The generator tensor
- E. The generator tensor is the unique invariant
- F. The generator tensor with three indices

## iv. References

* None.

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies Tensor SU TensorProduct

variable {N : ℕ}

/-!

## A. A fundamental and an anti-fundamental index as a matrix

-/

variable (N) in
/-- The components of an element of `ℂᴺ ⊗ ℂᴺ` as a matrix, `v ⊗ w ↦ v wᵀ`. -/
noncomputable def pairMatrix : (Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ) ≃ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  (Module.Basis.tensorProduct (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))).repr ≪≫ₗ
    Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin N × Fin N) ≪≫ₗ
    LinearEquiv.curry ℂ ℂ (Fin N) (Fin N)

@[simp]
lemma pairMatrix_tmul (v w : Fin N → ℂ) : pairMatrix N (v ⊗ₜ w) = vecMulVec v w := by
  ext i j
  change (Module.Basis.tensorProduct (Pi.basisFun ℂ (Fin N)) (Pi.basisFun ℂ (Fin N))).repr
    (v ⊗ₜ w) (i, j) = _
  simp [vecMulVec_apply, mul_comm]

/-- The fundamental and the anti-fundamental representation move the matrix of components by
  conjugation. -/
lemma pairMatrix_map (g : SU N) (x : (Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ)) :
    pairMatrix N (TensorProduct.map (fundRep N g) (antiFundRep N g) x)
      = g.1 * pairMatrix N x * (g⁻¹).1 := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    rw [TensorProduct.map_tmul, pairMatrix_tmul, pairMatrix_tmul, mul_vecMulVec, vecMulVec_mul]
    change vecMulVec (g.1 *ᵥ v) ((g⁻¹).1ᵀ *ᵥ w) = _
    rw [mulVec_transpose]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Matrix.mul_add, Matrix.add_mul]

variable (N) in
/-- The matrix of an element of the complexified Lie algebra, as an element of `ℂᴺ ⊗ ℂᴺ`. -/
noncomputable def adjToPair : SUAlgebraComplexified N →ₗ[ℂ] (Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ) :=
  (pairMatrix N).symm.toLinearMap ∘ₗ adjMat N

@[simp]
lemma pairMatrix_adjToPair (A : SUAlgebraComplexified N) :
    pairMatrix N (adjToPair N A) = adjMat N A := by
  simp [adjToPair]

/-- Writing the matrix of an element of the complexified Lie algebra in `ℂᴺ ⊗ ℂᴺ` is
  equivariant. -/
lemma adjToPair_adjRep (g : SU N) (A : SUAlgebraComplexified N) :
    adjToPair N (adjRep N g A)
      = TensorProduct.map (fundRep N g) (antiFundRep N g) (adjToPair N A) :=
  (pairMatrix N).injective (by rw [pairMatrix_map, pairMatrix_adjToPair, pairMatrix_adjToPair,
    adjMat_adjRep])

/-!

## B. Contracting an adjoint index

-/

section Contract

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

variable (N U) in
/-- An element of `adj ⊗ U` as the linear map `adj → U` contracting its first index against the
  argument with the trace form, `A₀ ⊗ u ↦ (A ↦ tr (A₀ A) u)`. -/
noncomputable def adjContract :
    SUAlgebraComplexified N ⊗[ℂ] U ≃ₗ[ℂ] (SUAlgebraComplexified N →ₗ[ℂ] U) :=
  TensorProduct.congr ((traceForm N).toDual (traceForm_nondegenerate N)) (LinearEquiv.refl ℂ U)
    ≪≫ₗ dualTensorHomEquiv ℂ _ U

@[simp]
lemma adjContract_tmul (A₀ : SUAlgebraComplexified N) (u : U) (A : SUAlgebraComplexified N) :
    adjContract N U (A₀ ⊗ₜ u) A = traceForm N A₀ A • u := by
  simp [adjContract, LinearMap.BilinForm.toDual_def]

/-- The trace form is invariant under the adjoint action. -/
lemma traceForm_adjRep (g : SU N) (A B : SUAlgebraComplexified N) :
    traceForm N (adjRep N g A) (adjRep N g B) = traceForm N A B :=
  LinearMap.congr_fun ((adjContr N).isIntertwining' g) (A ⊗ₜ B)

/-- Transforming both factors of `x` conjugates the map `adjContract x`. -/
lemma adjContract_map (σ : Representation ℂ (SU N) U) (g : SU N)
    (x : SUAlgebraComplexified N ⊗[ℂ] U) (A : SUAlgebraComplexified N) :
    adjContract N U (TensorProduct.map (adjRep N g) (σ g) x) (adjRep N g A)
      = σ g (adjContract N U x A) := by
  induction x using TensorProduct.inductionOn with
  | tmul A₀ u =>
    rw [TensorProduct.map_tmul, adjContract_tmul, adjContract_tmul, traceForm_adjRep, map_smul]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Applying a linear map to the second factor of `x` composes `adjContract x` with it. -/
lemma adjContract_lTensor {U' : Type*} [AddCommGroup U'] [Module ℂ U'] (ι : U →ₗ[ℂ] U')
    (x : SUAlgebraComplexified N ⊗[ℂ] U) (A : SUAlgebraComplexified N) :
    adjContract N U' (TensorProduct.map LinearMap.id ι x) A = ι (adjContract N U x A) := by
  induction x using TensorProduct.inductionOn with
  | tmul A₀ u => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The unit of the adjoint color, as a linear map, is the identity. -/
lemma adjContract_adjUnitVal (A : SUAlgebraComplexified N) :
    adjContract N _ (adjUnitVal N) A = A := by
  have h : ∀ x : SUAlgebraComplexified N ⊗[ℂ] SUAlgebraComplexified N,
      adjContract N _ x A = coevalMap (adjContr N) x A := fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul A₀ u =>
      rw [adjContract_tmul, coevalMap_tmul, (traceForm_isSymm N).eq]
      rfl
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  rw [h, coevalMap_adjUnitVal, LinearMap.id_apply]

end Contract

/-!

## C. Equivariant maps from the adjoint representation to the matrices

-/

/-- An invariant linear form on the complexified Lie algebra vanishes. By the trace form it is
  the pairing with an invariant element, which is zero. -/
lemma eq_zero_of_adjRep_invariant {ℓ : Module.Dual ℂ (SUAlgebraComplexified N)}
    (hℓ : ∀ (g : SU N) (A : SUAlgebraComplexified N), ℓ (adjRep N g A) = ℓ A) : ℓ = 0 := by
  obtain ⟨u, rfl⟩ := ((traceForm N).toDual (traceForm_nondegenerate N)).surjective ℓ
  simp only [LinearMap.BilinForm.toDual_def] at hℓ
  have hu : ∀ g : SU N, adjRep N g u = u := fun g =>
    sub_eq_zero.1 <| traceForm_separatingLeft N _ fun A => by
      have hA : adjRep N g (adjRep N g⁻¹ A) = A := Representation.self_inv_apply _ g A
      rw [map_sub, LinearMap.sub_apply, ← hA, traceForm_adjRep, hℓ g, sub_self]
  rw [Representation.eq_zero_of_invariants_eq_bot invariants_adjRep_eq_bot hu, map_zero]

/-- An equivariant linear map from the complexified Lie algebra to the matrices, moved by
  conjugation, is a multiple of the matrix of the argument. -/
lemma exists_eq_smul_adjMat_of_equivariant
    {Φ : SUAlgebraComplexified N →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ}
    (hΦ : ∀ (g : SU N) (A : SUAlgebraComplexified N), Φ (adjRep N g A) = g.1 * Φ A * (g⁻¹).1) :
    ∃ μ : ℂ, Φ = μ • adjMat N := by
  have htr : ∀ A, (Φ A).trace = 0 := fun A => by
    have h := eq_zero_of_adjRep_invariant (ℓ := Matrix.traceLinearMap (Fin N) ℂ ℂ ∘ₗ Φ)
      fun g A => by
        simp only [LinearMap.comp_apply, Matrix.traceLinearMap_apply, hΦ]
        rw [Matrix.trace_mul_cycle, val_inv_mul_val, Matrix.one_mul]
    exact LinearMap.congr_fun h A
  let L : SUAlgebraComplexified N →ₗ[ℂ] SUAlgebraComplexified N :=
    { toFun := fun A => ofTraceless (Φ A)
      map_add' := fun A B => adjMat_injective (by
        rw [adjMat_ofTraceless (htr (A + B)), map_add, map_add, adjMat_ofTraceless (htr A),
          adjMat_ofTraceless (htr B)])
      map_smul' := fun z A => adjMat_injective (by
        rw [adjMat_ofTraceless (htr (z • A)), map_smul, RingHom.id_apply, map_smul,
          adjMat_ofTraceless (htr A)]) }
  have hL : ∀ A, adjMat N (L A) = Φ A := fun A => adjMat_ofTraceless (htr A)
  obtain ⟨μ, hμ⟩ := eq_smul_id_of_commute_adjRep (L := L) fun g A =>
    adjMat_injective (by rw [hL, adjMat_adjRep, hL, hΦ])
  refine ⟨μ, LinearMap.ext fun A => ?_⟩
  rw [← hL, hμ, LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearMap.smul_apply]

/-!

## D. The generator tensor

-/

variable (N) in
/-- The generator tensor, the unit `∑ b_a ⊗ bᵃ` of the adjoint color with its second factor
  written as a matrix, in `adj ⊗ (ℂᴺ ⊗ ℂᴺ)`. Its components are the entries of `λ_a / 2`. -/
noncomputable def generatorVal :
    SUAlgebraComplexified N ⊗[ℂ] ((Fin N → ℂ) ⊗[ℂ] (Fin N → ℂ)) :=
  TensorProduct.map LinearMap.id (adjToPair N) (adjUnitVal N)

/-- As a linear map from the complexified Lie algebra, the generator tensor writes the matrix of
  the argument in `ℂᴺ ⊗ ℂᴺ`. -/
lemma adjContract_generatorVal (A : SUAlgebraComplexified N) :
    adjContract N _ (generatorVal N) A = adjToPair N A := by
  rw [generatorVal, adjContract_lTensor, adjContract_adjUnitVal]

/-- The generator tensor is invariant. -/
lemma generatorVal_mem_invariants :
    generatorVal N ∈ ((adjRep N).tprod ((fundRep N).tprod (antiFundRep N))).invariants := by
  intro g
  have hι : TensorProduct.map (fundRep N g) (antiFundRep N g) ∘ₗ adjToPair N
      = adjToPair N ∘ₗ adjRep N g := LinearMap.ext fun A => (adjToPair_adjRep g A).symm
  have hU := map_eq_self_of_coevalMap_eq_id (adjContr N) (adjContr_flip_injective N)
    (coevalMap_adjUnitVal N) g
  have h1 : TensorProduct.map (adjRep N g) (TensorProduct.map (fundRep N g) (antiFundRep N g))
      ∘ₗ TensorProduct.map LinearMap.id (adjToPair N)
      = TensorProduct.map LinearMap.id (adjToPair N)
        ∘ₗ TensorProduct.map (adjRep N g) (adjRep N g) := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp,
      hι]
  change TensorProduct.map (adjRep N g) (TensorProduct.map (fundRep N g) (antiFundRep N g))
    (TensorProduct.map LinearMap.id (adjToPair N) (adjUnitVal N)) = _
  rw [← LinearMap.comp_apply, h1, LinearMap.comp_apply, hU]
  rfl

/-!

## E. The generator tensor is the unique invariant

-/

/-- The invariants of `adj ⊗ (ℂᴺ ⊗ ℂᴺ)`, with the adjoint, the fundamental and the
  anti-fundamental representation, are the line through the generator tensor. -/
lemma invariants_tprod_eq_span_generatorVal :
    ((adjRep N).tprod ((fundRep N).tprod (antiFundRep N))).invariants = ℂ ∙ generatorVal N := by
  refine le_antisymm (fun x hx => ?_)
    ((Submodule.span_singleton_le_iff_mem _ _).2 generatorVal_mem_invariants)
  obtain ⟨μ, hμ⟩ := exists_eq_smul_adjMat_of_equivariant
    (Φ := (pairMatrix N).toLinearMap ∘ₗ adjContract N _ x) fun g A => by
      have h := adjContract_map ((fundRep N).tprod (antiFundRep N)) g x A
      rw [show TensorProduct.map (adjRep N g) (((fundRep N).tprod (antiFundRep N)) g) x = x
        from hx g] at h
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, h]
      exact pairMatrix_map g _
  refine Submodule.mem_span_singleton.2 ⟨μ, (adjContract N _).injective (LinearMap.ext fun A =>
    (pairMatrix N).injective ?_)⟩
  have h := LinearMap.congr_fun hμ A
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply] at h
  rw [map_smul, LinearMap.smul_apply, adjContract_generatorVal, map_smul, pairMatrix_adjToPair, h]

/-!

## F. The generator tensor with three indices

-/

variable (N) in
/-- The generator tensor `(Tᵃ)_i^j` with an adjoint, a fundamental and an anti-fundamental
  index. -/
noncomputable def generator : SuT[N, .adj, .fund, .antiFund] :=
  fromTripleT (S := suTensor N) (c1 := .adj) (c2 := .fund) (c3 := .antiFund) (generatorVal N)

/-- The generator tensor is invariant. -/
lemma generator_invariant (g : SU N) : g • generator N = generator N := by
  rw [generator, actionT_fromTripleT]
  exact congrArg _ (generatorVal_mem_invariants g)

/-- The invariant tensors with an adjoint, a fundamental and an anti-fundamental index are the
  line through the generator tensor. -/
lemma invariants_adj_fund_antiFund_eq_span_generator :
    ((suTensor N).tensorRep ![.adj, .fund, .antiFund]).invariants = ℂ ∙ generator N :=
  invariants_tensorRep_triple_eq_span invariants_tprod_eq_span_generatorVal

/-- The dual basis of the Gell-Mann basis under the trace form is half of it. -/
lemma dualBasis_adjBasis (a : GellMann.Index N) :
    (traceForm N).dualBasis (traceForm_nondegenerate N) (adjBasis N) a
      = (1 / 2 : ℂ) • adjBasis N a := by
  refine (adjBasis N).ext_elem fun c => ?_
  have h := LinearMap.BilinForm.apply_dualBasis_right (traceForm_nondegenerate N)
    (traceForm_isSymm N) (adjBasis N) c a
  rw [traceForm_apply, adjMat_adjBasis] at h
  rw [adjBasis_repr_apply, h, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul]
  by_cases hca : c = a
  · simp [hca]
  · simp [hca, Ne.symm hca]

/-- The generator tensor as a sum over the Gell-Mann basis, with the matrices `λ_a / 2` in its
  second factor. -/
lemma generatorVal_eq_sum : generatorVal N
    = ∑ a, adjBasis N a ⊗ₜ adjToPair N ((1 / 2 : ℂ) • adjBasis N a) := by
  rw [generatorVal, adjUnitVal, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, dualBasis_adjBasis]

/-- The components of the generator tensor are the entries of the generators `λ_a / 2`. -/
lemma basis_repr_generator (a : GellMann.Index N) (i j : Fin N) :
    (Tensor.basis _).repr (generator N) (fun | 0 => a | 1 => i | 2 => j)
      = GellMann.matrix a i j / 2 := by
  rw [generator, fromTripleT_basis_repr, generatorVal_eq_sum, map_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finset.sum_eq_single a]
  · rw [Module.Basis.tensorProduct_repr_tmul_apply]
    change pairMatrix N (adjToPair N _) i j * (adjBasis N).repr (adjBasis N a) a = _
    rw [pairMatrix_adjToPair, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one, map_smul,
      adjMat_adjBasis, Matrix.smul_apply, smul_eq_mul]
    ring
  · intro b _ hb
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    change _ * (adjBasis N).repr (adjBasis N b) a = 0
    rw [Module.Basis.repr_self, Finsupp.single_apply, ite_eq_right hb, mul_zero]
  · simp

end suTensor
