/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.VelocityBand.Basic
/-!

# The uncertainty of a localized electron

## i. Overview

An eigenvector of `H` or of `X` has no fluctuation in that observable, so its centered Gram
defect vanishes. For a localized electron `|n⟩` this means `Var X = 0`: both sides of the
energy–position uncertainty relation are `0`, and the relation says nothing about the pair.

The pair does not vanish there. As soon as the chain hops, `t ≠ 0`, and has two sites, a
localized electron fluctuates in energy, `Var H > 0`: fixing the position sends the whole
uncertainty to the energy, and only the bracket `⟨n|⁅H, X⁆|n⟩` is zero.

Conversely, a vector with positive defect is an eigenvector of neither `H` nor `X`: it
fluctuates in both.

## ii. Key results

- `flucOf_eq_zero_of_eigen` : an eigenvector has no fluctuation in its observable.
- `fluc_ne_zero_of_defectOf_pos` : a positive defect forces fluctuations in `H` and `X`.
- `flucOf_openHamiltonian_localizedState_ne_zero` : a localized electron fluctuates in energy.
- `inner_bracket_localizedState` : the bracket vanishes in a localized electron.
- `robertson_schrodinger_localizedState` : in `|n⟩`, `Var X = 0` and the defect is `0`, while
  `Var H > 0`.

## iii. Table of contents

- A. Eigenvectors
- B. The localized electron

## iv. References

* H. P. Robertson, *The uncertainty principle*, Phys. Rev. 34 (1929) 163.
* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]
-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint
open ProbabilisticTheory
open InnerProductSpace UnitalPositiveLinearMap
variable (T : TightBindingChain)

/-!

## A. Eigenvectors

-/

/-- A unit eigenvector of `A` with real eigenvalue has no fluctuation in `A`. -/
lemma flucOf_eq_zero_of_eigen {A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace} {ψ : T.HilbertSpace}
    (hψ : ‖ψ‖ = 1) {c : ℝ} (h : A ψ = (c : ℂ) • ψ) : T.flucOf A ψ = 0 := by
  have hm : T.meanOf A ψ = c := by
    rw [meanOf, h, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
    simp
  rw [flucOf, hm, h, Complex.coe_smul, sub_self]

/-- A positive defect forces fluctuations in both `H` and `X`. -/
lemma fluc_ne_zero_of_defectOf_pos {ψ : T.HilbertSpace} (h : 0 < T.defectOf ψ) :
    T.flucOf T.openHamiltonian ψ ≠ 0 ∧ T.flucOf T.position ψ ≠ 0 := by
  refine ⟨fun hH => ?_, fun hX => ?_⟩ <;> simp_all [defectOf]

/-- A vector with positive defect is an eigenvector of neither `H` nor `X`. -/
lemma not_eigen_of_defectOf_pos {ψ : T.HilbertSpace} (hψ : ‖ψ‖ = 1)
    (h : 0 < T.defectOf ψ) (c : ℝ) :
    T.openHamiltonian ψ ≠ (c : ℂ) • ψ ∧ T.position ψ ≠ (c : ℂ) • ψ :=
  ⟨fun hc => (T.fluc_ne_zero_of_defectOf_pos h).1 (T.flucOf_eq_zero_of_eigen hψ hc),
    fun hc => (T.fluc_ne_zero_of_defectOf_pos h).2 (T.flucOf_eq_zero_of_eigen hψ hc)⟩

/-!

## B. The localized electron

-/

lemma norm_localizedState (n : Fin T.N) : ‖(|n⟩ : T.HilbertSpace)‖ = 1 :=
  (localizedState (T := T)).orthonormal.1 n

/-- A localized electron has no fluctuation in position. -/
lemma flucOf_position_localizedState (n : Fin T.N) : T.flucOf T.position |n⟩ = 0 :=
  T.flucOf_eq_zero_of_eigen (T.norm_localizedState n) (T.position_apply_localizedState n)

/-- Every site of a chain with two sites has a neighbour. -/
lemma exists_neighbour (hN : 2 ≤ T.N) (n : Fin T.N) :
    ∃ m : Fin T.N, (m : ℕ) + 1 = n ∨ (n : ℕ) + 1 = m := by
  by_cases h : (n : ℕ) + 1 < T.N
  · exact ⟨⟨n + 1, h⟩, Or.inr rfl⟩
  · exact ⟨⟨n - 1, by omega⟩, Or.inl (by simp only; omega)⟩

/-- **A localized electron fluctuates in energy.** If the chain hops and has two sites,
`H |n⟩ - ⟨H⟩ |n⟩ ≠ 0`: its overlap with a neighbour is `-t`. -/
lemma flucOf_openHamiltonian_localizedState_ne_zero (ht : T.t ≠ 0) (hN : 2 ≤ T.N)
    (n : Fin T.N) : T.flucOf T.openHamiltonian |n⟩ ≠ 0 := by
  obtain ⟨m, hm⟩ := T.exists_neighbour hN n
  have hmn : m ≠ n := by rintro rfl; omega
  intro h
  have h' := congrArg (fun φ => ⟪(|m⟩ : T.HilbertSpace), φ⟫_ℂ) h
  simp only [flucOf, ← Complex.coe_smul, inner_sub_right, inner_smul_right,
    T.localizedState_orthonormal_eq_ite, hmn, ↓reduceIte, mul_zero, sub_zero,
    T.inner_openHamiltonian, hm, inner_zero_right, neg_eq_zero, Complex.ofReal_eq_zero] at h'
  exact ht h'

/-- The bracket `⁅H, X⁆` vanishes in a localized electron. -/
lemma inner_bracket_localizedState (n : Fin T.N) :
    ⟪|n⟩, ((⁅T.openHamiltonianObservable, T.positionObservable⁆ : Observable _) :
      _ →L[ℂ] _) |n⟩⟫_ℂ = 0 := by
  rw [inner_bracket_openHamiltonian_position_eq]
  simp

/-- **Robertson–Schrödinger is empty in a localized electron.** In `|n⟩`, `Var X = 0` and the
centered Gram defect is `0`: both sides of the relation vanish. The energy does not:
`Var H > 0` as soon as the chain hops and has two sites. -/
lemma robertson_schrodinger_localizedState (ht : T.t ≠ 0) (hN : 2 ≤ T.N) (n : Fin T.N) :
    variance (ofVec (T.norm_localizedState n)) T.positionObservable = 0 ∧
      centeredGramDefect (ofVec (T.norm_localizedState n)) T.openHamiltonianObservable
        T.positionObservable = 0 ∧
      0 < variance (ofVec (T.norm_localizedState n)) T.openHamiltonianObservable := by
  have h := T.norm_localizedState n
  have hvar (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) (hA : A.IsSymmetric) :
      variance (ofVec h) (T.toObservable A hA) = ‖T.flucOf A |n⟩‖ ^ 2 := by
    rw [variance_ofVec, T.expectation_ofVec h A hA]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hvar _ T.position_hermitian, T.flucOf_position_localizedState, norm_zero]
    simp
  · rw [T.centeredGramDefect_ofVec_eq h]
    exact (T.localizedState_mem_minUncertainty n).2
  · rw [hvar _ T.openHamiltonian_hermitian]
    exact pow_pos (norm_pos_iff.mpr (T.flucOf_openHamiltonian_localizedState_ne_zero ht hN n)) 2

end TightBindingChain
end CondensedMatter
