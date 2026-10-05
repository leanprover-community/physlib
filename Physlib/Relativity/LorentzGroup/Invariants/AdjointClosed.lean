/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import Physlib.Relativity.Tensors.Equivariant
/-!
# The colours of complex Lorentz tensors are closed under adjoints

## i. Overview

A family of vectors in a representation `repLorentz` of `SL(2,ℂ)` on `B`, carrying Lorentz
indices of colours `c`, is packaged as a linear map `f : ℂT(c) →ₗ[ℂ] B`, equivariant in the sense
`complexLorentzTensor.IsEquivariant c repLorentz f`. The invariants in the range of such a map
come from invariant tensors whenever the colours are closed under adjoints,
`TensorSpecies.IsAdjointClosed`.

For `SL(2,ℂ)` this follows from each colour being dagger compatible: in its basis, the matrix of
`g†` is the conjugate transpose of the matrix of `g`. This holds for all six colours (B), so
every list of colours is closed under adjoints, `complexLorentzTensor.isAdjointClosed`.

## ii. Key results

- `Lorentz.IsDaggerCompatible` : the matrix of `g†` is the conjugate transpose of that of `g`.
- `Lorentz.isDaggerCompatible` : every colour is dagger compatible.
- `complexLorentzTensor.isAdjointClosed` : every list of colours is closed under adjoints.

## iii. Table of contents

- A. The matrices of the colours
- B. Dagger-compatible colours

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. The matrices of the colours

-/

/-- The matrix of `g` on the left-handed Weyl colour is `g`. -/
lemma toMatrix_rep_upL (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .upL) (complexLorentzTensor.basis .upL)
      (complexLorentzTensor.rep .upL g) = g.1 :=
  Fermion.LeftHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the dual left-handed Weyl colour is `(g⁻¹)ᵀ`. -/
lemma toMatrix_rep_downL (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .downL) (complexLorentzTensor.basis .downL)
      (complexLorentzTensor.rep .downL g) = (g.1⁻¹)ᵀ :=
  Fermion.DualLeftHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the right-handed Weyl colour is the entrywise conjugate of `g`. -/
lemma toMatrix_rep_upR (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .upR) (complexLorentzTensor.basis .upR)
      (complexLorentzTensor.rep .upR g) = g.1.map star :=
  Fermion.RightHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the dual right-handed Weyl colour is `(g⁻¹)ᴴ`. -/
lemma toMatrix_rep_downR (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .downR) (complexLorentzTensor.basis .downR)
      (complexLorentzTensor.rep .downR g) = (g.1⁻¹)ᴴ :=
  Fermion.DualRightHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the contravariant vector colour is the Lorentz matrix of `g`, with
  the vector indices relabelled by `finSumFinEquiv`. -/
lemma toMatrix_rep_up_apply (g : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3) :
    LinearMap.toMatrix (complexLorentzTensor.basis .up) (complexLorentzTensor.basis .up)
      (complexLorentzTensor.rep .up g) (finSumFinEquiv μ) (finSumFinEquiv ν)
      = (((SL2C.toLorentzGroup g).1 μ ν : ℝ) : ℂ) := by
  change LinearMap.toMatrix (complexContrBasis.reindex finSumFinEquiv)
    (complexContrBasis.reindex finSumFinEquiv) (ContrℂModule.SL2CRep g) _ _ = _
  rw [LinearMap.toMatrix_apply, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← LinearMap.toMatrix_apply,
    complexContrBasis_ρ_apply]
  rfl

/-- The matrix of `g` on the covariant vector colour is the transpose of the inverse of the
  Lorentz matrix of `g`, with the vector indices relabelled by `finSumFinEquiv`. -/
lemma toMatrix_rep_down_apply (g : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3) :
    LinearMap.toMatrix (complexLorentzTensor.basis .down) (complexLorentzTensor.basis .down)
      (complexLorentzTensor.rep .down g) (finSumFinEquiv μ) (finSumFinEquiv ν)
      = (((SL2C.toLorentzGroup g)⁻¹.1 ν μ : ℝ) : ℂ) := by
  change LinearMap.toMatrix (complexCoBasis.reindex finSumFinEquiv)
    (complexCoBasis.reindex finSumFinEquiv) (CoℂModule.SL2CRep g) _ _ = _
  rw [LinearMap.toMatrix_apply, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← LinearMap.toMatrix_apply,
    complexCoBasis_ρ_apply, Matrix.transpose_apply, LorentzGroup.toComplex_inv]
  rfl

/-- The inverse of `g†` is the dagger of the inverse of `g`. -/
lemma inv_dagger (g : SL(2,ℂ)) : (dagger g)⁻¹ = dagger g⁻¹ := by
  ext1
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp only [dagger, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_conjTranspose]

/-!

## B. Dagger-compatible colours

-/

/-- A colour is dagger compatible when, in its basis, the matrix of `g†` is the conjugate
  transpose of the matrix of `g`. -/
def IsDaggerCompatible (k : complexLorentzTensor.Color) : Prop :=
  ∀ g : SL(2,ℂ),
    LinearMap.toMatrix (complexLorentzTensor.basis k) (complexLorentzTensor.basis k)
      (complexLorentzTensor.rep k (dagger g))
    = (LinearMap.toMatrix (complexLorentzTensor.basis k) (complexLorentzTensor.basis k)
      (complexLorentzTensor.rep k g))ᴴ

/-- The four Weyl colours are dagger compatible. -/
lemma isDaggerCompatible_of_weyl {k : complexLorentzTensor.Color}
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR) : IsDaggerCompatible k := by
  rcases hk with rfl | rfl | rfl | rfl <;> intro g
  · rw [toMatrix_rep_upL, toMatrix_rep_upL]
    rfl
  · rw [toMatrix_rep_downL, toMatrix_rep_downL]
    change ((g.1ᴴ)⁻¹)ᵀ = _
    rw [← Matrix.conjTranspose_nonsing_inv]
    rfl
  · rw [toMatrix_rep_upR, toMatrix_rep_upR]
    ext i j
    simp [dagger]
  · rw [toMatrix_rep_downR, toMatrix_rep_downR]
    change ((g.1ᴴ)⁻¹)ᴴ = _
    rw [← Matrix.conjTranspose_nonsing_inv]

/-- The contravariant vector colour is dagger compatible: the Lorentz matrix of `g†` is the
  transpose of that of `g`, and it is real. -/
lemma isDaggerCompatible_up : IsDaggerCompatible .up := by
  intro g
  ext i j
  obtain ⟨μ, rfl⟩ := (finSumFinEquiv (m := 1) (n := 3)).surjective i
  obtain ⟨ν, rfl⟩ := (finSumFinEquiv (m := 1) (n := 3)).surjective j
  rw [Matrix.conjTranspose_apply, toMatrix_rep_up_apply, toMatrix_rep_up_apply,
    toLorentzGroup_dagger, Matrix.transpose_apply, Complex.star_def, Complex.conj_ofReal]

/-- The covariant vector colour is dagger compatible: the inverse Lorentz matrix of `g†` is the
  transpose of that of `g`, and it is real. -/
lemma isDaggerCompatible_down : IsDaggerCompatible .down := by
  intro g
  ext i j
  obtain ⟨μ, rfl⟩ := (finSumFinEquiv (m := 1) (n := 3)).surjective i
  obtain ⟨ν, rfl⟩ := (finSumFinEquiv (m := 1) (n := 3)).surjective j
  rw [Matrix.conjTranspose_apply, toMatrix_rep_down_apply, toMatrix_rep_down_apply, ← map_inv,
    inv_dagger, toLorentzGroup_dagger, map_inv, Matrix.transpose_apply, Complex.star_def,
    Complex.conj_ofReal]

/-- Every colour of complex Lorentz tensors is dagger compatible. -/
lemma isDaggerCompatible (k : complexLorentzTensor.Color) : IsDaggerCompatible k := by
  cases k
  · exact isDaggerCompatible_of_weyl (Or.inl rfl)
  · exact isDaggerCompatible_of_weyl (Or.inr (Or.inl rfl))
  · exact isDaggerCompatible_of_weyl (Or.inr (Or.inr (Or.inl rfl)))
  · exact isDaggerCompatible_of_weyl (Or.inr (Or.inr (Or.inr rfl)))
  · exact isDaggerCompatible_up
  · exact isDaggerCompatible_down

/-- Colours that are all dagger compatible are closed under adjoints, with `g' = g†`. -/
lemma isAdjointClosed_of_isDaggerCompatible {n : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (hc : ∀ i, IsDaggerCompatible (c i)) : complexLorentzTensor.IsAdjointClosed c :=
  fun g => ⟨dagger g, fun i => hc i g⟩

end Lorentz

/-- Every list of colours of complex Lorentz tensors is closed under adjoints, with
  `g' = g†`. -/
lemma complexLorentzTensor.isAdjointClosed {n : ℕ} (c : Fin n → complexLorentzTensor.Color) :
    complexLorentzTensor.IsAdjointClosed c :=
  Lorentz.isAdjointClosed_of_isDaggerCompatible fun i => Lorentz.isDaggerCompatible (c i)
