/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Lagrangian
public import Physlib.Particles.QED.GammaMatrices
/-!
# Lorentz invariance of quantum electrodynamics

## i. Overview

The Lorentz-theoretic theorems of QED, culminating in the Lorentz invariance
of the QED Lagrangian, `lorentzAction_lagrangian`.  The chain of results:

* the covering map `Lorentz.SL2C.toLorentzGroup` intertwines the conjugation
  of the covariant Pauli matrices with the Lorentz transformation of their
  index; combined with the defining property `Λ η Λᵀ = η` of the Lorentz
  group this yields the two contraction identities of the spinor
  representation (`sum_lorentz_inv_conjTranspose_pauli_conj` and
  `sum_lorentz_inv_eta_pauli_conj`), which assemble block-diagonally into
  the contraction identity of the kinetic matrices `γ⁰ γ^μ`
  (`sum_kineticGamma_contraction`);
* the jet coordinates of QED transform as tensors and spinors
  (`lorentzAction_A_zero`, `lorentzAction_ψ_singleton`, …), and the covariant
  derivative transforms exactly like the first-order jet
  (`lorentzAction_covDψ`);
* the Maxwell term is invariant because `Λ⁻¹ η (Λ⁻¹)ᵀ = η`
  (`Photon.JetAlgebra.lorentzAction_maxwellTerm`), the mass term because the
  spinor representation preserves `γ⁰`
  (`spinorRep_conjTranspose_gammaZero_spinorRep`), and the kinetic term by
  the contraction identity;
* the Lagrangian, being built from invariant pieces, is invariant
  (`lorentzAction_lagrangian`).

This file contains no definitions, only theorems about the jet algebras of
`Physlib.Particles.QED.Basic`, the fields of `Physlib.Particles.QED.Fields` and the Lagrangian of
`Physlib.Particles.QED.Lagrangian`.

## ii. Key results

- `sum_kineticGamma_contraction` : the Lorentz contraction identity of the
  matrices `γ⁰ γ^μ` under the spinor representation.
- `spinorRep_conjTranspose_gammaZero_spinorRep` : the spinor representation
  preserves `γ⁰`.
- `JetAlgebra.lorentzAction_A_zero`, `JetAlgebra.lorentzAction_ψ_zero`,
  `JetAlgebra.lorentzAction_ψ_singleton`, … : the transformation laws of the
  jet coordinates.
- `JetAlgebra.lorentzAction_covDψ` : Lorentz covariance of the covariant
  derivative.
- `Photon.JetAlgebra.lorentzAction_maxwellTerm`,
  `JetAlgebra.lorentzAction_maxwellTerm` : Lorentz invariance of the Maxwell
  term.
- `JetAlgebra.lorentzAction_electronMassTerm`,
  `JetAlgebra.lorentzAction_diracKineticTerm` : Lorentz invariance of the
  fermionic terms.
- `JetAlgebra.lorentzAction_lagrangian` : **Lorentz invariance of the QED
  Lagrangian**.

## iii. Table of contents

- A. Contractions of the Minkowski metric with a Lorentz transformation
- B. The intertwining identities of the spinor representation
  - B.1. Conjugation of the covariant Pauli matrices
  - B.2. The two block identities
  - B.3. The contraction identity of the kinetic matrices
  - B.4. The spinor representation preserves `γ⁰`
- C. The transformation laws of the jet coordinates
- D. Lorentz invariance of the Maxwell term
- E. Lorentz covariance of the covariant derivative
- F. Lorentz invariance of the fermionic terms
- G. Lorentz invariance of the QED Lagrangian

## iv. References

The Lorentz actions are defined in `Physlib.Particles.QED.Basic`; the corresponding
machinery for the lepton–gauge sector is
`Physlib.Particles.LeptonGaugeSector.JetAlgebra.LorentzAction`.

-/

@[expose] public section

namespace QED

open Matrix MatrixGroups minkowskiMatrix TensorProduct
open scoped PauliMatrix

attribute [-simp] Fintype.sum_sum_type

/-!

## A. Contractions of the Minkowski metric with a Lorentz transformation

-/

/-- The defining property of the Lorentz group in index form: contracting two
  rows of `Λ⁻¹` with the Minkowski metric reproduces the metric. -/
lemma sum_eta_inv_inv (Λ : LorentzGroup 3) (τ τ' : Fin 1 ⊕ Fin 3) :
    ∑ μ, η μ μ * ((Λ⁻¹).1 τ μ * (Λ⁻¹).1 τ' μ) = η τ τ' := by
  have h := congrArg (fun A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ => A τ τ')
    (LorentzGroup.mul_minkowskiMatrix_mul_transpose (Λ := Λ⁻¹))
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_eq_single μ (fun a _ ha => by rw [off_diag_zero ha, mul_zero])
    (fun h => absurd (Finset.mem_univ μ) h)]
  ring

/-!

## B. The intertwining identities of the spinor representation

### B.1. Conjugation of the covariant Pauli matrices

-/

/-- The covariant Pauli matrices are `σ̄^μ = η_{μμ} σ^μ` (no sum). -/
lemma pauliSelfAdjoint'_coe (μ : Fin 1 ⊕ Fin 3) :
    (PauliMatrix.pauliSelfAdjoint' μ).1 = η μ μ • σ μ := by
  fin_cases μ <;> simp [PauliMatrix.pauliSelfAdjoint']

/-- The kinetic matrices through the covariant Pauli matrices:
  `γ⁰ γ^μ = ((σ̄^μ, 0), (0, η_{μμ} σ̄^μ))`. -/
lemma kineticGamma_eq_fromBlocks_pauliSelfAdjoint' (μ : Fin 1 ⊕ Fin 3) :
    JetAlgebra.kineticGamma μ =
      Matrix.fromBlocks (PauliMatrix.pauliSelfAdjoint' μ).1 0 0
        (η μ μ • (PauliMatrix.pauliSelfAdjoint' μ).1) := by
  rw [JetAlgebra.kineticGamma, pauliSelfAdjoint'_coe, smul_smul,
    minkowskiMatrix.η_apply_mul_η_apply_diag, one_smul]

/-- Conjugating a covariant Pauli matrix by `N : SL(2,ℂ)` transforms its
  index by the image of `N` in the Lorentz group; this is the defining
  property of the covering map. -/
lemma sl2c_conj_pauliSelfAdjoint' (N : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    N.1 * (PauliMatrix.pauliSelfAdjoint' μ).1 * N.1ᴴ =
      ∑ ν, (Lorentz.SL2C.toLorentzGroup N).1 ν μ •
        (PauliMatrix.pauliSelfAdjoint' ν).1 := by
  have h := congrArg Subtype.val (Lorentz.SL2C.toSelfAdjointMap_basis (M := N) μ)
  simpa only [Lorentz.SL2C.toSelfAdjointMap_apply_coe, PauliMatrix.pauliBasis',
    Module.Basis.coe_mk, AddSubmonoidClass.coe_finsetSum, selfAdjoint.val_smul] using h

/-- A block matrix summed over the diagonal blocks. -/
lemma sum_fromBlocks {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (D : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ i ∈ s, Matrix.fromBlocks (A i) 0 0 (D i) =
      Matrix.fromBlocks (∑ i ∈ s, A i) 0 0 (∑ i ∈ s, D i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, ih,
      Matrix.fromBlocks_add, add_zero]

/-!

### B.2. The two block identities

The left Weyl block: transporting the index of `σ̄^μ` with `Λ(M)⁻¹` cancels
the conjugation by `M`, through `Λ(M†) = Λ(M)ᵀ`.

-/

lemma sum_lorentz_inv_conjTranspose_pauli_conj (M : SL(2,ℂ)) (τ : Fin 1 ⊕ Fin 3) :
    ∑ μ, ((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ •
        (M.1ᴴ * (PauliMatrix.pauliSelfAdjoint' μ).1 * M.1) =
      (PauliMatrix.pauliSelfAdjoint' τ).1 := by
  have hdet : Matrix.det (M.1ᴴ) = 1 := by
    rw [Matrix.det_conjTranspose, Matrix.SpecialLinearGroup.det_coe]
    exact star_one ℂ
  have hswap : ∀ μ, M.1ᴴ * (PauliMatrix.pauliSelfAdjoint' μ).1 * M.1 =
      ∑ ν, (Lorentz.SL2C.toLorentzGroup M).1 μ ν •
        (PauliMatrix.pauliSelfAdjoint' ν).1 := by
    intro μ
    have h := sl2c_conj_pauliSelfAdjoint' ⟨M.1ᴴ, hdet⟩ μ
    rw [show ((⟨M.1ᴴ, hdet⟩ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = M.1 from
      Matrix.conjTranspose_conjTranspose _] at h
    rw [show ((⟨M.1ᴴ, hdet⟩ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) = M.1ᴴ from rfl] at h
    rw [h]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Lorentz.SL2C.toLorentzGroup_conjTranspose (M := M) (N := ⟨M.1ᴴ, hdet⟩) rfl,
      Matrix.transpose_apply]
  rw [Finset.sum_congr rfl fun μ _ => by rw [hswap μ, Finset.smul_sum], Finset.sum_comm]
  rw [Finset.sum_congr rfl fun ν _ => show
      (∑ μ, ((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ •
        ((Lorentz.SL2C.toLorentzGroup M).1 μ ν • (PauliMatrix.pauliSelfAdjoint' ν).1)) =
      ((1 : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) τ ν) •
        (PauliMatrix.pauliSelfAdjoint' ν).1 from by
    rw [Finset.sum_congr rfl fun μ _ => smul_smul (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ)
        ((Lorentz.SL2C.toLorentzGroup M).1 μ ν) (PauliMatrix.pauliSelfAdjoint' ν).1,
      ← Finset.sum_smul, ← Matrix.mul_apply, ← lorentzGroupIsGroup_mul_coe,
      inv_mul_cancel, lorentzGroupIsGroup_one_coe]]
  rw [Finset.sum_eq_single τ
    (fun ν _ hν => by rw [Matrix.one_apply_ne (Ne.symm hν), zero_smul])
    (fun h => absurd (Finset.mem_univ τ) h), Matrix.one_apply_eq, one_smul]

/-- The right Weyl block: transporting the index of `η_{μμ} σ̄^μ` with
  `Λ(M)⁻¹` cancels the conjugation by `(M⁻¹)†`, through `Λ⁻¹ η (Λ⁻¹)ᵀ = η`. -/
lemma sum_lorentz_inv_eta_pauli_conj (M : SL(2,ℂ)) (τ : Fin 1 ⊕ Fin 3) :
    ∑ μ, (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ * η μ μ) •
        ((M⁻¹).1 * (PauliMatrix.pauliSelfAdjoint' μ).1 * ((M⁻¹).1)ᴴ) =
      η τ τ • (PauliMatrix.pauliSelfAdjoint' τ).1 := by
  have hswap : ∀ μ, (M⁻¹).1 * (PauliMatrix.pauliSelfAdjoint' μ).1 * ((M⁻¹).1)ᴴ =
      ∑ ν, ((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 ν μ •
        (PauliMatrix.pauliSelfAdjoint' ν).1 := by
    intro μ
    rw [sl2c_conj_pauliSelfAdjoint' M⁻¹ μ]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_inv]
  rw [Finset.sum_congr rfl fun μ _ => by rw [hswap μ, Finset.smul_sum], Finset.sum_comm]
  rw [Finset.sum_congr rfl fun ν _ => show
      (∑ μ, (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ * η μ μ) •
        (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 ν μ • (PauliMatrix.pauliSelfAdjoint' ν).1)) =
      (η τ ν) • (PauliMatrix.pauliSelfAdjoint' ν).1 from by
    rw [Finset.sum_congr rfl fun μ _ =>
        smul_smul ((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ * η μ μ))
          (((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 ν μ) (PauliMatrix.pauliSelfAdjoint' ν).1,
      ← Finset.sum_smul,
      show (∑ μ, ((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ * η μ μ *
          ((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 ν μ) = η τ ν from by
        rw [← sum_eta_inv_inv (Lorentz.SL2C.toLorentzGroup M) τ ν]
        exact Finset.sum_congr rfl fun μ _ => by ring]]
  rw [Finset.sum_eq_single τ
    (fun ν _ hν => by rw [off_diag_zero (Ne.symm hν), zero_smul])
    (fun h => absurd (Finset.mem_univ τ) h)]

/-!

### B.3. The contraction identity of the kinetic matrices

-/

/-- The matrix form of the contraction identity: transporting the vector index
  of `γ⁰ γ^μ` with `Λ(M)⁻¹` cancels the conjugation by the spinor
  representation. -/
lemma sum_lorentz_inv_spinorRep_kineticGamma (M : SL(2,ℂ)) (τ : Fin 1 ⊕ Fin 3) :
    ∑ μ, ((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ •
        ((Electron.JetAlgebra.spinorRep M)ᴴ * JetAlgebra.kineticGamma μ *
          Electron.JetAlgebra.spinorRep M) =
      JetAlgebra.kineticGamma τ := by
  have hS : (Electron.JetAlgebra.spinorRep M)ᴴ =
      Matrix.fromBlocks M.1ᴴ 0 0 ((M⁻¹).1) := by
    rw [Electron.JetAlgebra.spinorRep, Matrix.fromBlocks_conjTranspose]
    simp
  have hblock : ∀ μ, (Electron.JetAlgebra.spinorRep M)ᴴ * JetAlgebra.kineticGamma μ *
      Electron.JetAlgebra.spinorRep M =
      Matrix.fromBlocks (M.1ᴴ * (PauliMatrix.pauliSelfAdjoint' μ).1 * M.1) 0 0
        (η μ μ • ((M⁻¹).1 * (PauliMatrix.pauliSelfAdjoint' μ).1 * ((M⁻¹).1)ᴴ)) := by
    intro μ
    rw [hS, Electron.JetAlgebra.spinorRep, kineticGamma_eq_fromBlocks_pauliSelfAdjoint',
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1 <;> simp
  rw [Finset.sum_congr rfl fun μ _ => by
    rw [hblock μ, Matrix.fromBlocks_smul, smul_zero, smul_smul]]
  rw [sum_fromBlocks, sum_lorentz_inv_conjTranspose_pauli_conj,
    sum_lorentz_inv_eta_pauli_conj, kineticGamma_eq_fromBlocks_pauliSelfAdjoint']

/-- **The contraction identity of the Dirac kinetic term**: the index form of
  `∑_μ (Λ⁻¹)_{τμ} S(M)† (γ⁰ γ^μ) S(M) = γ⁰ γ^τ`.  This is the identity that
  makes `i ψ̄ γ^μ D_μ ψ` a Lorentz scalar. -/
lemma sum_kineticGamma_contraction (M : SL(2,ℂ)) (τ : Fin 1 ⊕ Fin 3)
    (α' β' : Fin 2 ⊕ Fin 2) :
    ∑ μ, ∑ α, ∑ β, JetAlgebra.kineticGamma μ α β *
        (star (Electron.JetAlgebra.spinorRep M α α') *
          (((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ : ℝ) : ℂ) *
            Electron.JetAlgebra.spinorRep M β β')) =
      JetAlgebra.kineticGamma τ α' β' := by
  have h := congrArg (fun A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ => A α' β')
    (sum_lorentz_inv_spinorRep_kineticGamma M τ)
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.real_smul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-!

### B.4. The spinor representation preserves `γ⁰`

-/

/-- The spinor representation preserves `γ⁰`: `S(M)† γ⁰ S(M) = γ⁰`.  This is
  the identity that makes the Dirac mass term `m ψ̄ ψ` a Lorentz scalar. -/
lemma spinorRep_conjTranspose_gammaZero_spinorRep (M : SL(2,ℂ)) :
    (Electron.JetAlgebra.spinorRep M)ᴴ * JetAlgebra.gammaMatrix (Sum.inl 0) *
      Electron.JetAlgebra.spinorRep M = JetAlgebra.gammaMatrix (Sum.inl 0) := by
  have h1 : M.1ᴴ * ((M⁻¹).1)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.conjTranspose_one]
  have h2 : (M⁻¹).1 * M.1 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  rw [Electron.JetAlgebra.spinorRep, JetAlgebra.gammaMatrix_inl_zero,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero,
    zero_add]
  rw [h1, h2]

/-- The index form of `S(M)† γ⁰ S(M) = γ⁰`. -/
lemma sum_gammaZero_contraction (M : SL(2,ℂ)) (α' β' : Fin 2 ⊕ Fin 2) :
    ∑ α, ∑ β, JetAlgebra.gammaMatrix (Sum.inl 0) α β *
        (star (Electron.JetAlgebra.spinorRep M α α') *
          Electron.JetAlgebra.spinorRep M β β') =
      JetAlgebra.gammaMatrix (Sum.inl 0) α' β' := by
  have h := congrArg (fun A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ => A α' β')
    (spinorRep_conjTranspose_gammaZero_spinorRep M)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  rw [← h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-!

## C. The transformation laws of the jet coordinates

-/

namespace JetAlgebra

/-- The photon jet coordinate transforms as a covector. -/
theorem lorentzAction_A_zero (M : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    lorentzAction M (A 0 μ) =
      ∑ ν, ((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 ν μ : ℝ) : ℂ) • A 0 ν := by
  simp only [A]
  rw [lorentzAction_tmul, map_one, lorentzActionPhoton_tmul,
    Photon.JetAlgebra.lorentzAction_coord_zero, TensorProduct.tmul_sum, sum_tmul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_smul, real_smul_tmul]

/-- The first-order photon jet coordinate transforms as a two-tensor. -/
theorem lorentzAction_A_singleton (M : SL(2,ℂ)) (ρ μ : Fin 1 ⊕ Fin 3) :
    lorentzAction M (A {ρ} μ) =
      ∑ τ, ∑ ν, ((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ ρ *
          ((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 ν μ : ℝ) : ℂ) • A {τ} ν := by
  simp only [A]
  rw [lorentzAction_tmul, map_one, lorentzActionPhoton_tmul,
    Photon.JetAlgebra.lorentzAction_coord_singleton]
  rw [TensorProduct.tmul_sum, sum_tmul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [TensorProduct.tmul_sum, sum_tmul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_smul, real_smul_tmul]

/-- The electron jet coordinate transforms in the spinor representation. -/
theorem lorentzAction_ψ_zero (M : SL(2,ℂ)) (α : Fin 2 ⊕ Fin 2) :
    lorentzAction M (ψ 0 α) =
      ∑ β, Electron.JetAlgebra.spinorRep M α β • ψ 0 β := by
  simp only [ψ]
  rw [lorentzAction_tmul, map_one,
    Electron.JetAlgebra.lorentzAction_ofGenerator_dψ_zero, tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [tmul_smul]

/-- The conjugate electron jet coordinate transforms in the conjugate spinor
  representation. -/
theorem lorentzAction_barψ_zero (M : SL(2,ℂ)) (α : Fin 2 ⊕ Fin 2) :
    lorentzAction M (barψ 0 α) =
      ∑ β, star (Electron.JetAlgebra.spinorRep M α β) • barψ 0 β := by
  simp only [barψ]
  rw [lorentzAction_tmul, map_one,
    Electron.JetAlgebra.lorentzAction_ofGenerator_dbarψ_zero, tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [tmul_smul]

/-- The first-order electron jet coordinate transforms as a spinor with a
  covector derivative index. -/
theorem lorentzAction_ψ_singleton (M : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    lorentzAction M (ψ {ρ} α) =
      ∑ τ, ∑ β, (((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ ρ : ℝ) : ℂ) *
          Electron.JetAlgebra.spinorRep M α β) • ψ {τ} β := by
  simp only [ψ]
  rw [lorentzAction_tmul, map_one,
    Electron.JetAlgebra.lorentzAction_ofGenerator_dψ_singleton, tmul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [tmul_smul, Complex.real_smul]

theorem lorentzAction_barψ_singleton (M : SL(2,ℂ)) (ρ : Fin 1 ⊕ Fin 3)
    (α : Fin 2 ⊕ Fin 2) :
    lorentzAction M (barψ {ρ} α) =
      ∑ τ, ∑ β, (((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ ρ : ℝ) : ℂ) *
          star (Electron.JetAlgebra.spinorRep M α β)) • barψ {τ} β := by
  simp only [barψ]
  rw [lorentzAction_tmul, map_one,
    Electron.JetAlgebra.lorentzAction_ofGenerator_dbarψ_singleton, tmul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [tmul_smul, Complex.real_smul]

end JetAlgebra

/-!

## D. Lorentz invariance of the Maxwell term

-/

namespace Photon

namespace JetAlgebra

/-- The formal field strength transforms as an antisymmetric two-tensor. -/
lemma lorentzAction_fieldStrength_zero (Λ : LorentzGroup 3) (μ ν : Fin 1 ⊕ Fin 3) :
    lorentzAction Λ (fieldStrength 0 μ ν) =
      ∑ a, ∑ b, ((Λ⁻¹).1 a μ * (Λ⁻¹).1 b ν) • fieldStrength 0 a b := by
  rw [fieldStrength, zero_add, zero_add, map_sub, lorentzAction_coord_singleton,
    lorentzAction_coord_singleton,
    Finset.sum_comm (f := fun a b => ((Λ⁻¹).1 a ν * (Λ⁻¹).1 b μ) • coord {a} b),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [fieldStrength, zero_add, zero_add, smul_sub]
  congr 1
  rw [mul_comm]

set_option maxHeartbeats 4000000 in
/-- **Lorentz invariance of the Maxwell term** in the photon jet algebra:
  the two metric contractions absorb the four transformation matrices through
  `Λ⁻¹ η (Λ⁻¹)ᵀ = η`. -/
theorem lorentzAction_maxwellTerm (Λ : LorentzGroup 3) :
    lorentzAction Λ maxwellTerm = maxwellTerm := by
  have hcoef : ∀ a b c d : Fin 1 ⊕ Fin 3,
      (∑ μ, ∑ ν, (η μ μ * η ν ν) *
        ((Λ⁻¹).1 c μ * (Λ⁻¹).1 d ν * ((Λ⁻¹).1 a μ * (Λ⁻¹).1 b ν))) =
      η c a * η d b := by
    intro a b c d
    calc (∑ μ, ∑ ν, (η μ μ * η ν ν) *
          ((Λ⁻¹).1 c μ * (Λ⁻¹).1 d ν * ((Λ⁻¹).1 a μ * (Λ⁻¹).1 b ν)))
        = ∑ μ, ∑ ν, (η μ μ * ((Λ⁻¹).1 c μ * (Λ⁻¹).1 a μ)) *
            (η ν ν * ((Λ⁻¹).1 d ν * (Λ⁻¹).1 b ν)) := by
          refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
          ring
      _ = (∑ μ, η μ μ * ((Λ⁻¹).1 c μ * (Λ⁻¹).1 a μ)) *
            (∑ ν, η ν ν * ((Λ⁻¹).1 d ν * (Λ⁻¹).1 b ν)) := by
          rw [Finset.sum_mul_sum]
      _ = η c a * η d b := by rw [sum_eta_inv_inv, sum_eta_inv_inv]
  have hinner : ∀ a b c d : Fin 1 ⊕ Fin 3,
      (∑ μ, ∑ ν, ((η μ μ * η ν ν) *
        ((Λ⁻¹).1 c μ * (Λ⁻¹).1 d ν * ((Λ⁻¹).1 a μ * (Λ⁻¹).1 b ν))) •
          (fieldStrength 0 c d * fieldStrength 0 a b)) =
      (η c a * η d b) • (fieldStrength 0 c d * fieldStrength 0 a b) := by
    intro a b c d
    rw [← hcoef a b c d, Finset.sum_smul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_smul]
  rw [maxwellTerm, map_sum]
  conv_lhs => enter [2, μ]; rw [map_sum]
  conv_lhs =>
    enter [2, μ, 2, ν]
    rw [map_smul, map_mul, lorentzAction_fieldStrength_zero]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Finset.smul_sum,
    smul_smul]
  -- reorder the six sums from `μ ν a b c d` to `a b c d μ ν`
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, c]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  calc (∑ c, ∑ d, ∑ μ, ∑ ν, ((η μ μ * η ν ν) *
        ((Λ⁻¹).1 c μ * (Λ⁻¹).1 d ν * ((Λ⁻¹).1 a μ * (Λ⁻¹).1 b ν))) •
          (fieldStrength 0 c d * fieldStrength 0 a b))
      = ∑ c, ∑ d, (η c a * η d b) • (fieldStrength 0 c d * fieldStrength 0 a b) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => hinner a b c d
    _ = (η a a * η b b) • (fieldStrength 0 a b * fieldStrength 0 a b) := by
        rw [Finset.sum_eq_single a (fun c _ hc => Finset.sum_eq_zero fun d _ => by
            rw [off_diag_zero hc, zero_mul, zero_smul])
          (fun h => absurd (Finset.mem_univ a) h),
          Finset.sum_eq_single b (fun d _ hd => by
            rw [off_diag_zero hd, mul_zero, zero_smul])
          (fun h => absurd (Finset.mem_univ b) h)]

end JetAlgebra

end Photon

namespace JetAlgebra

/-- **Lorentz invariance of the Maxwell term** in the QED jet algebra,
  inherited from the photon jet algebra. -/
theorem lorentzAction_maxwellTerm (M : SL(2,ℂ)) :
    lorentzAction M maxwellTerm = maxwellTerm := by
  simp only [maxwellTerm]
  rw [lorentzAction_tmul, map_one, lorentzActionPhoton_tmul,
    Photon.JetAlgebra.lorentzAction_maxwellTerm]

/-!

## E. Lorentz covariance of the covariant derivative

-/

/-- The covariant derivative transforms exactly like the first-order jet
  coordinate: as a spinor with a covector derivative index. -/
theorem lorentzAction_covDψ (M : SL(2,ℂ)) (e : ℝ) (μ : Fin 1 ⊕ Fin 3)
    (β : Fin 2 ⊕ Fin 2) :
    lorentzAction M (covDψ e μ β) =
      ∑ τ, ∑ β', (((((Lorentz.SL2C.toLorentzGroup M)⁻¹).1 τ μ : ℝ) : ℂ) *
        Electron.JetAlgebra.spinorRep M β β') • covDψ e τ β' := by
  rw [covDψ, map_add, map_smul, map_mul, lorentzAction_ψ_singleton,
    lorentzAction_A_zero, lorentzAction_ψ_zero, Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm, Finset.smul_sum, smul_smul, smul_add,
    Finset.sum_add_distrib, covDψ]
  congr 1
  all_goals
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun β' _ => ?_
    first
    | rfl
    | exact congrArg (· • _) (by ring)

/-!

## F. Lorentz invariance of the fermionic terms

-/

set_option maxHeartbeats 2000000 in
/-- **Lorentz invariance of the Dirac mass term**: the spinor phases of the
  electron and its conjugate cancel through `S(M)† γ⁰ S(M) = γ⁰`. -/
theorem lorentzAction_electronMassTerm (M : SL(2,ℂ)) :
    lorentzAction M electronMassTerm = electronMassTerm := by
  rw [electronMassTerm, map_sum]
  conv_lhs => enter [2, α]; rw [map_sum]
  conv_lhs =>
    enter [2, α, 2, β]
    rw [map_smul, map_mul, lorentzAction_barψ_zero, lorentzAction_ψ_zero]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Finset.smul_sum,
    smul_smul]
  -- reorder the four sums from `α β β' α'` to `α' β' α β`
  conv_lhs => enter [2, α, 2, β]; rw [Finset.sum_comm]
  conv_lhs => enter [2, α]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, α', 2, α]; rw [Finset.sum_comm]
  conv_lhs => enter [2, α']; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun β' _ => ?_
  rw [← sum_gammaZero_contraction M α' β', Finset.sum_smul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_smul]

set_option maxHeartbeats 2000000 in
/-- **Lorentz invariance of the Dirac kinetic term**: the transformation of
  the two spinor slots and the derivative slot cancels through the contraction
  identity of the matrices `γ⁰ γ^μ`. -/
theorem lorentzAction_diracKineticTerm (M : SL(2,ℂ)) (e : ℝ) :
    lorentzAction M (diracKineticTerm e) = diracKineticTerm e := by
  rw [diracKineticTerm, map_smul, map_sum]
  congr 1
  conv_lhs => enter [2, μ]; rw [map_sum]
  conv_lhs => enter [2, μ, 2, α]; rw [map_sum]
  conv_lhs =>
    enter [2, μ, 2, α, 2, β]
    rw [map_smul, map_mul, lorentzAction_barψ_zero, lorentzAction_covDψ]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Finset.smul_sum,
    smul_smul]
  -- reorder the six sums from `μ α β τ β' α'` to `τ α' β' μ α β`
  conv_lhs => enter [2, μ, 2, α]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, τ, 2, μ, 2, α, 2, β]; rw [Finset.sum_comm]
  conv_lhs => enter [2, τ, 2, μ, 2, α]; rw [Finset.sum_comm]
  conv_lhs => enter [2, τ, 2, μ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, τ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, τ, 2, α', 2, μ, 2, α]; rw [Finset.sum_comm]
  conv_lhs => enter [2, τ, 2, α', 2, μ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, τ, 2, α']; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun α' _ =>
    Finset.sum_congr rfl fun β' _ => ?_
  rw [← sum_kineticGamma_contraction M τ α' β', Finset.sum_smul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_smul]

/-!

## G. Lorentz invariance of the QED Lagrangian

-/

/-- **Lorentz invariance of the QED Lagrangian.**  The Maxwell term is
  invariant through `Λ⁻¹ η (Λ⁻¹)ᵀ = η`, the kinetic term through the
  contraction identity of `γ⁰ γ^μ` under the spinor representation, and the
  mass term through `S(M)† γ⁰ S(M) = γ⁰`. -/
theorem lorentzAction_lagrangian (M : SL(2,ℂ)) (e m : ℝ) :
    lorentzAction M (lagrangian e m) = lagrangian e m := by
  rw [lagrangian, map_sub, map_add, map_smul, map_smul, lorentzAction_maxwellTerm,
    lorentzAction_diracKineticTerm, lorentzAction_electronMassTerm]

end JetAlgebra

end QED
