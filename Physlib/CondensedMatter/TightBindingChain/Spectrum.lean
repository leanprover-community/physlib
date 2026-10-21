/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.CondensedMatter.TightBindingChain.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The spectrum of the tight binding chain

The energies `E0 - 2 t cos (k a)` at the quantized wavenumbers are all the eigenvalues of the
Hamiltonian of the tight binding chain.

## i. Overview

`hamiltonian_energyEigenstate` shows that every quantized wavenumber `k` gives an eigenvalue
`E0 - 2 t cos (k a)`. Here we show that there are no others.

There are `N` quantized wavenumbers, and their energy eigenstates are nonzero and pairwise
orthogonal, so they are a basis of the `N`-dimensional Hilbert space, orthonormal once
normalized. An eigenvector of the Hamiltonian has a nonzero overlap with one of them, and since
the Hamiltonian is Hermitian its eigenvalue is the energy of that eigenstate.

## ii. Key results

- `energyEigenstate_linearIndependent` and `energyEigenstate_span` : the energy eigenstates
  are linearly independent and span the Hilbert space.
- `energyEigenbasis` : the normalized energy eigenstates form an orthonormal basis.
- `hasEigenvalue_hamiltonian_iff` : the eigenvalues of the Hamiltonian are exactly the
  energies `E0 - 2 t cos (k a)`.

## iii. Table of contents

- A. The basis of energy eigenstates
- B. The spectrum

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open InnerProductSpace

variable (T : TightBindingChain)

/-! ## A. The basis of energy eigenstates -/

/-- The energy eigenstates are linearly independent. -/
lemma energyEigenstate_linearIndependent :
    LinearIndependent ℂ (fun n : Fin T.N => T.energyEigenstate (T.quantaWaveNumber n)) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero
    (fun n => T.energyEigenstate_ne_zero (T.quantaWaveNumber n))
    (fun _ _ h => T.energyEigenstate_orthogonal (T.quantaWaveNumber_injective.ne h))

/-- The energy eigenstates span the Hilbert space. -/
lemma energyEigenstate_span :
    ⊤ ≤ Submodule.span ℂ (Set.range fun n : Fin T.N =>
      T.energyEigenstate (T.quantaWaveNumber n)) := by
  refine le_of_eq (T.energyEigenstate_linearIndependent.span_eq_top_of_card_eq_finrank' ?_).symm
  simpa using (Module.finrank_eq_card_basis localizedState.toBasis).symm

/-- The normalized energy eigenstates `N ^ (-1/2) • energyEigenstate k` are orthonormal. -/
lemma energyEigenstate_orthonormal :
    Orthonormal ℂ (fun n : Fin T.N =>
      (((Real.sqrt T.N)⁻¹ : ℝ) : ℂ) • T.energyEigenstate (T.quantaWaveNumber n)) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [inner_smul_left, inner_smul_right]
  by_cases h : m = n
  · subst h
    simp only [↓reduceIte, energyEigenstate_inner_self]
    have hN : (0 : ℝ) < T.N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne T.N))
    have hs : (Real.sqrt T.N : ℂ) ^ 2 = T.N := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hN.le, Complex.ofReal_natCast]
    have hs0 : (Real.sqrt T.N : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hN).ne'
    rw [Complex.conj_ofReal]
    simp only [Complex.ofReal_inv]
    rw [← hs]
    field_simp
  · simp only [h, ↓reduceIte, T.energyEigenstate_orthogonal (T.quantaWaveNumber_injective.ne h)]
    simp

/-- The normalized energy eigenstates form an orthonormal basis of the Hilbert space. -/
noncomputable def energyEigenbasis : OrthonormalBasis (Fin T.N) ℂ T.HilbertSpace :=
  OrthonormalBasis.mk T.energyEigenstate_orthonormal
    (le_of_eq (T.energyEigenstate_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simpa using (Module.finrank_eq_card_basis localizedState.toBasis).symm)).symm)

/-- The `n`-th vector of the basis is the normalized energy eigenstate of the `n`-th
wavenumber. -/
@[simp]
lemma energyEigenbasis_apply (n : Fin T.N) :
    T.energyEigenbasis n =
      (((Real.sqrt T.N)⁻¹ : ℝ) : ℂ) • T.energyEigenstate (T.quantaWaveNumber n) := by
  simp [energyEigenbasis]

/-! ## B. The spectrum -/

/-- The eigenvalues of the Hamiltonian are exactly the energies `E0 - 2 t cos (k a)` of the
quantized wavenumbers. -/
lemma hasEigenvalue_hamiltonian_iff (E : ℂ) :
    Module.End.HasEigenvalue T.hamiltonian E ↔
      ∃ k : T.QuantaWaveNumber, E = T.energyEigenvalue k := by
  refine ⟨fun h => ?_, fun ⟨k, hk⟩ => hk ▸ Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (T.hamiltonian_energyEigenstate k),
      T.energyEigenstate_ne_zero k⟩⟩
  obtain ⟨ψ, hψ, hψ0⟩ := h.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hψ
  obtain ⟨n, hn⟩ : ∃ n, ⟪T.energyEigenstate (T.quantaWaveNumber n), ψ⟫_ℂ ≠ 0 := by
    by_contra! h0
    refine hψ0 (ext_inner_left_basis T.energyEigenbasis.toBasis fun n => ?_)
    rw [OrthonormalBasis.coe_toBasis, energyEigenbasis_apply, inner_smul_left, h0, mul_zero,
      inner_zero_right]
  refine ⟨T.quantaWaveNumber n, mul_right_cancel₀ hn ?_⟩
  rw [← inner_smul_right, ← hψ, ← hamiltonian_hermitian, hamiltonian_energyEigenstate]
  exact (inner_smul_left _ _ (T.energyEigenvalue _ : ℂ)).trans (by rw [Complex.conj_ofReal])

end TightBindingChain
end CondensedMatter
