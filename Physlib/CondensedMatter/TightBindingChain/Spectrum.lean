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
orthogonal, so they form a basis of the `N`-dimensional Hilbert space. An eigenvector of the
Hamiltonian has a nonzero overlap with one of them, and since the Hamiltonian is Hermitian its
eigenvalue is the energy of that eigenstate.

## ii. Key results

- `energyEigenstate_ne_zero` : an energy eigenstate is not zero.
- `energyEigenbasis` : the energy eigenstates form a basis of the Hilbert space.
- `hasEigenvalue_hamiltonian_iff` : the eigenvalues of the Hamiltonian are exactly the
  energies `E0 - 2 t cos (k a)`.

## iii. Table of contents

- A. The quantized wavenumbers as a family
- B. The basis of energy eigenstates
- C. The spectrum

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open InnerProductSpace

variable (T : TightBindingChain)

/-! ## A. The quantized wavenumbers as a family -/

/-- The quantized wavenumber `2 π / (a N) * (n - ⌊N/2⌋)` of the index `n`. -/
noncomputable def quantaWaveNumber (n : Fin T.N) : T.QuantaWaveNumber := ⟨_, n, rfl⟩

/-- Distinct indices give distinct quantized wavenumbers. -/
lemma quantaWaveNumber_injective : Function.Injective T.quantaWaveNumber := by
  intro m n h
  have hc : 2 * Real.pi / (T.a * T.N) ≠ 0 := div_ne_zero (by positivity)
    (mul_ne_zero T.a_pos.ne' (Nat.cast_ne_zero.2 (NeZero.ne T.N)))
  have := mul_left_cancel₀ hc (Subtype.ext_iff.1 h)
  exact Fin.ext (by exact_mod_cast sub_left_inj.1 this)

/-! ## B. The basis of energy eigenstates -/

/-- An energy eigenstate is not zero. -/
lemma energyEigenstate_ne_zero (k : T.QuantaWaveNumber) : T.energyEigenstate k ≠ 0 := fun h => by
  have := congrArg (⟪|0⟩, ·⟫_ℂ) h
  rw [energyEigenstate, inner_sum, inner_zero_right] at this
  simp_rw [inner_smul_right, localizedState_orthonormal_eq_ite] at this
  simp at this

/-- The energy eigenstates form a basis of the Hilbert space. -/
noncomputable def energyEigenbasis : Module.Basis (Fin T.N) ℂ T.HilbertSpace :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_of_ne_zero_of_inner_eq_zero
      (fun n => T.energyEigenstate_ne_zero (T.quantaWaveNumber n))
      (fun _ _ h => T.energyEigenstate_orthogonal (T.quantaWaveNumber_injective.ne h)))
    (Module.finrank_eq_card_basis localizedState.toBasis).symm

/-- The `n`-th vector of the basis is the energy eigenstate of the `n`-th wavenumber. -/
@[simp]
lemma energyEigenbasis_apply (n : Fin T.N) :
    T.energyEigenbasis n = T.energyEigenstate (T.quantaWaveNumber n) := by
  simp [energyEigenbasis]

/-! ## C. The spectrum -/

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
  obtain ⟨n, hn⟩ : ∃ n, ⟪T.energyEigenbasis n, ψ⟫_ℂ ≠ 0 := by
    by_contra! h0
    exact hψ0 (ext_inner_left_basis T.energyEigenbasis fun n => by rw [h0, inner_zero_right])
  refine ⟨T.quantaWaveNumber n, mul_right_cancel₀ hn ?_⟩
  rw [energyEigenbasis_apply] at hn ⊢
  rw [← inner_smul_right, ← hψ, ← hamiltonian_hermitian, hamiltonian_energyEigenstate]
  exact (inner_smul_left _ _ (T.energyEigenvalue _ : ℂ)).trans (by rw [Complex.conj_ofReal])

end TightBindingChain
end CondensedMatter
