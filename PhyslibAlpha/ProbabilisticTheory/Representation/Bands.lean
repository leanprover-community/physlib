/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.Floquet
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.InnerProductSpace.CourantFischer
public import Mathlib.Analysis.Matrix.Spectrum

/-!

# Bloch bands

The ordered eigenvalues of a Hermitian Bloch matrix are continuous functions on the Brillouin zone,
and they exhaust the spectrum of the translation-invariant operator.

## i. Overview

The eigenvalues of a Hermitian `N × N` matrix, listed in decreasing order, are the bands
`ε₁(χ) ≥ ⋯ ≥ ε_N(χ)` of a Hermitian Bloch matrix `b(χ)`. By Weyl's inequality the `k`-th
eigenvalue moves by at most the operator norm of the change of the matrix, so each band `ε_k` is a
continuous function of the matrix and hence of the crystal momentum `χ`. If the symbol of a
translation-invariant operator is Hermitian the operator is self-adjoint, and its spectrum is
contained in the union of the ranges of the bands.

## ii. Key results

- `bandOf` : the `k`-th largest eigenvalue of a Hermitian matrix.
- `abs_bandOf_sub_le` : Weyl's inequality for bands.
- `continuous_bandOf` : bands are continuous functions of a continuous Hermitian family.
- `UnitaryRep.isSelfAdjoint_blochHom` : the operator of a Hermitian symbol is self-adjoint.
- `UnitaryRep.exists_band_eq_of_mem_spectrum` : every spectral value is a band value.

## iii. Table of contents

- A. Bands of Hermitian matrices
- B. Bands of a translation-invariant operator

## iv. References

* R. Bhatia, Matrix Analysis, Corollary III.2.6.

-/

@[expose] public section

noncomputable section

open Matrix Module

namespace ProbabilisticTheory

namespace QuantumMechanics

/-! ## A. Bands of Hermitian matrices -/

/-- The `k`-th largest eigenvalue of a Hermitian matrix: its `k`-th band. -/
def bandOf {N : ℕ} {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.IsHermitian)
    (k : Fin (Fintype.card (Fin N))) : ℝ :=
  hM.eigenvalues₀ k

/-- **Weyl's inequality for bands**: the `k`-th band of two Hermitian matrices differ by at most
the operator norm of the difference.   -/
lemma abs_bandOf_sub_le {N : ℕ} {M S : Matrix (Fin N) (Fin N) ℂ} (hM : M.IsHermitian)
    (hS : S.IsHermitian) (k : Fin (Fintype.card (Fin N))) :
    |bandOf hM k - bandOf hS k| ≤
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M - S))‖ := by
  have := LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm
    (isSymmetric_toEuclideanLin_iff.mpr hM) (isSymmetric_toEuclideanLin_iff.mpr hS)
    (finrank_euclideanSpace (ι := Fin N)) k
  simpa [bandOf, Matrix.IsHermitian.eigenvalues₀, map_sub] using this

/-- **Bands are continuous**: the `k`-th band of a continuous family of Hermitian matrices is a
continuous function. -/
lemma continuous_bandOf {X : Type*} [TopologicalSpace X] {N : ℕ}
    {b : X → Matrix (Fin N) (Fin N) ℂ} (hb : ∀ x, (b x).IsHermitian) (hc : Continuous b)
    (k : Fin (Fintype.card (Fin N))) : Continuous fun x => bandOf (hb x) k := by
  let Ψ : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin N))
      (F' := EuclideanSpace ℂ (Fin N))).toLinearMap ∘ₗ (Matrix.toEuclideanLin).toLinearMap
  have hΨ : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) (g := fun x => ‖Ψ (b x - b x₀)‖) ?_
  · have := abs_bandOf_sub_le (hb x) (hb x₀) k
    simpa [Real.norm_eq_abs, Ψ] using this
  · have hcont : Continuous fun x => ‖Ψ (b x - b x₀)‖ :=
      (hΨ.comp (hc.sub continuous_const)).norm
    have h0 : ‖Ψ (b x₀ - b x₀)‖ = 0 := by simp
    have h := hcont.tendsto x₀
    rwa [h0] at h

/-! ## B. Bands of a translation-invariant operator -/

namespace UnitaryRep

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : Multiplicative G →* unitary (H →L[ℂ] H))
variable [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]
variable {N : ℕ} (ι : Matrix (Fin N) (Fin N) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (hι : ∀ (M : Matrix (Fin N) (Fin N) ℂ) (g : Multiplicative G),
  Commute ((π g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) (ι M))

include hι

/-- The operator of a Hermitian symbol is self-adjoint. -/
lemma isSelfAdjoint_blochHom
    (b : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (hb : ∀ χ, (b χ).IsHermitian) : IsSelfAdjoint (blochHom π ι hι b) := by
  have hstar : star b = b := by
    ext χ : 1
    exact hb χ
  show star (blochHom π ι hι b) = blochHom π ι hι b
  rw [← map_star, hstar]

/-- **Every point of the spectrum of the operator of a Hermitian symbol is a band value**: it is
the `k`-th band `ε_k(χ)` of some crystal momentum `χ`. -/
lemma exists_band_eq_of_mem_spectrum
    (b : C(PontryaginDual (Multiplicative G), Matrix (Fin N) (Fin N) ℂ))
    (hb : ∀ χ, (b χ).IsHermitian) {z : ℂ} (hz : z ∈ spectrum ℂ (blochHom π ι hι b)) :
    ∃ (χ : PontryaginDual (Multiplicative G)) (k : Fin (Fintype.card (Fin N))),
      z = ((bandOf (hb χ) k : ℝ) : ℂ) := by
  obtain ⟨χ, hχ⟩ := Set.mem_iUnion.mp (spectrum_blochHom_subset π ι hι b hz)
  rw [(hb χ).spectrum_eq_image_range] at hχ
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hχ
  exact ⟨χ, (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i, rfl⟩

omit hι

end UnitaryRep

end QuantumMechanics

end ProbabilisticTheory

end
