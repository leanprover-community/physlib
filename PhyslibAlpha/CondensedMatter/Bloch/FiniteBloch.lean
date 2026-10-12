/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!

# The spectrum of a finite periodic crystal

The spectrum of a translation-invariant operator on a finite periodic crystal is the union of the
spectra of its Bloch matrices.

## i. Overview

A finite periodic crystal has a finite abelian translation group `G`, for instance `(ℤ / mℤ) ^ d`,
and `N` orbitals in each cell. A configuration is a function `ψ : G → ℂ ^ N`, and a hopping
operator `(B ψ) x = ∑_r A_r ψ (x - r)` moves amplitude by the lattice vector `r` through the
matrix `A_r`. A plane wave `x ↦ χ(x) v` of crystal momentum `χ`, a character of `G`, is mapped to
`χ(x) b(χ) v`, where `b(χ) = ∑_r χ(-r) A_r` is the Bloch matrix. So an eigenvector of `b(χ)`
gives an eigenvector of `B` with the same eigenvalue. Conversely, the Fourier transform
`ψ̂(χ) = ∑_x χ(-x) ψ(x)` of an eigenvector of `B` satisfies `b(χ) ψ̂(χ) = λ ψ̂(χ)`, and a
nonzero function has a nonzero Fourier transform at some momentum, by orthogonality of the
characters. Hence `spec B = ⋃_χ spec b(χ)`, with no analysis: the space is finite dimensional.

For the infinite lattice `ℤ ^ d` the same statement holds on `ℓ²`, where the Fourier transform is
a unitary map onto `L²` of the Brillouin zone, and is proved in `RegularRep.spectrum_blochOperator`.

## ii. Key results

- `FiniteBloch.hopping` : the hopping operator with matrices `A_r`.
- `FiniteBloch.bloch` : its Bloch matrix at a crystal momentum.
- `FiniteBloch.fourier_hopping` : the Fourier transform intertwines the operator with its Bloch
  matrix.
- `FiniteBloch.spectrum_hopping` : the spectrum is the union of the spectra of the Bloch matrices.

## iii. Table of contents

- A. The hopping operator and its Bloch matrix
- B. The spectrum

## iv. References

* F. Bloch, Über die Quantenmechanik der Elektronen in Kristallgittern, Z. Phys. 52 (1929). [ref:
  bloch_1929]
* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 8.

-/

@[expose] public section

namespace CondensedMatter

namespace FiniteBloch

open scoped Matrix

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {N : ℕ}

/-! ## A. The hopping operator and its Bloch matrix -/

/-- The hopping operator `(B ψ) x = ∑_r A_r ψ (x - r)` on configurations of a finite periodic
crystal. -/
def hopping (A : G → Matrix (Fin N) (Fin N) ℂ) :
    (G → Fin N → ℂ) →ₗ[ℂ] (G → Fin N → ℂ) where
  toFun ψ x := ∑ r, (A r).mulVec (ψ (x - r))
  map_add' ψ φ := by
    ext x i
    simp [Matrix.mulVec_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext x i
    simp [Matrix.mulVec_smul, Finset.mul_sum]

omit [DecidableEq G] in
lemma hopping_apply (A : G → Matrix (Fin N) (Fin N) ℂ) (ψ : G → Fin N → ℂ) (x : G) :
    hopping A ψ x = ∑ r, (A r).mulVec (ψ (x - r)) := rfl

/-- The Bloch matrix `b(χ) = ∑_r χ(-r) A_r` of a hopping operator. -/
def bloch (A : G → Matrix (Fin N) (Fin N) ℂ) (χ : AddChar G ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ r, χ (-r) • A r

/-- The Fourier transform `ψ̂(χ) = ∑_x χ(-x) ψ(x)` of a configuration. -/
def fourier (χ : AddChar G ℂ) (ψ : G → Fin N → ℂ) : Fin N → ℂ := ∑ x, χ (-x) • ψ x

omit [DecidableEq G] in
/-- **Bloch's theorem on a finite crystal.** The Fourier transform of `B ψ` at momentum `χ` is
the Bloch matrix applied to the Fourier transform of `ψ`. -/
lemma fourier_hopping (A : G → Matrix (Fin N) (Fin N) ℂ) (χ : AddChar G ℂ)
    (ψ : G → Fin N → ℂ) : fourier χ (hopping A ψ) = (bloch A χ).mulVec (fourier χ ψ) := by
  simp only [fourier, bloch, hopping_apply, Finset.smul_sum, Matrix.sum_mulVec, Matrix.mulVec_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Fintype.sum_equiv (Equiv.addRight r) (fun y => χ (-(y + r)) • (A r).mulVec (ψ y))
    (fun x => χ (-x) • (A r).mulVec (ψ (x - r))) (fun y => by simp)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [neg_add, AddChar.map_add_eq_mul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    mul_comm]

/-! ## B. The spectrum -/

/-- An eigenvalue of an operator on a finite-dimensional space is a point of its spectrum. -/
lemma mem_spectrum_iff_exists {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (μ : ℂ) : μ ∈ spectrum ℂ f ↔ ∃ v, v ≠ 0 ∧ f v = μ • v := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, hv.apply_eq_smul⟩
  · rintro ⟨v, hv, h⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h, hv⟩

/-- A complex number is in the spectrum of a matrix exactly when it has an eigenvector. -/
lemma mem_spectrum_matrix_iff (M : Matrix (Fin N) (Fin N) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ ∃ v : Fin N → ℂ, v ≠ 0 ∧ M.mulVec v = μ • v := by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin N)) M,
    mem_spectrum_iff_exists]
  simp [Matrix.toLinAlgEquiv'_apply]

omit [DecidableEq G] in
lemma fourier_smul (χ : AddChar G ℂ) (c : ℂ) (ψ : G → Fin N → ℂ) :
    fourier χ (c • ψ) = c • fourier χ ψ := by
  simp [fourier, Finset.smul_sum, smul_comm c]

/-- **Fourier inversion** on a finite abelian group. -/
lemma sum_character_smul_fourier (ψ : G → Fin N → ℂ) (x : G) :
    ∑ χ : AddChar G ℂ, χ x • fourier χ ψ = (Fintype.card G : ℂ) • ψ x := by
  simp only [fourier, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ y : G, ∑ χ : AddChar G ℂ, χ x * χ (-y) =
      if y = x then (Fintype.card G : ℂ) else 0 := by
    intro y
    simp_rw [← AddChar.map_add_eq_mul]
    simp_rw [← sub_eq_add_neg]
    rw [AddChar.sum_apply_eq_ite]
    simp [sub_eq_zero, eq_comm]
  simp_rw [← Finset.sum_smul, this]
  simp

/-- A configuration with vanishing Fourier transform vanishes. -/
lemma eq_zero_of_fourier_eq_zero {ψ : G → Fin N → ℂ} (h : ∀ χ, fourier χ ψ = 0) : ψ = 0 := by
  funext x
  have := sum_character_smul_fourier ψ x
  simp only [h, smul_zero, Finset.sum_const_zero] at this
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact (smul_eq_zero.1 this.symm).resolve_left hc

omit [DecidableEq G] in
/-- A plane wave of crystal momentum `χ` is mapped to a plane wave with the same momentum. -/
lemma hopping_planeWave (A : G → Matrix (Fin N) (Fin N) ℂ) (χ : AddChar G ℂ)
    (v : Fin N → ℂ) :
    hopping A (fun x => χ x • v) = fun x => χ x • (bloch A χ).mulVec v := by
  funext x
  simp only [hopping_apply, bloch, Matrix.sum_mulVec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul,
    mul_comm]

/-- **The spectrum of a translation-invariant operator on a finite periodic crystal is the union
of the spectra of its Bloch matrices.** -/
lemma spectrum_hopping (A : G → Matrix (Fin N) (Fin N) ℂ) :
    spectrum ℂ (hopping A) = ⋃ χ : AddChar G ℂ, spectrum ℂ (bloch A χ) := by
  ext μ
  simp only [Set.mem_iUnion, mem_spectrum_iff_exists, mem_spectrum_matrix_iff]
  constructor
  · rintro ⟨ψ, hψ, h⟩
    have : ∃ χ, fourier χ ψ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hψ (eq_zero_of_fourier_eq_zero hcon)
    obtain ⟨χ, hχ⟩ := this
    refine ⟨χ, fourier χ ψ, hχ, ?_⟩
    rw [← fourier_hopping, h, fourier_smul]
  · rintro ⟨χ, v, hv, h⟩
    refine ⟨fun x => χ x • v, ?_, ?_⟩
    · intro h0
      apply hv
      simpa using congrFun h0 0
    · rw [hopping_planeWave, h]
      funext x
      simp [smul_comm μ]

end FiniteBloch

end CondensedMatter
