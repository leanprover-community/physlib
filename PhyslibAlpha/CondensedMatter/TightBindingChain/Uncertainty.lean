/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.OpenBoundary
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.VectorUncertainty
public import PhyslibAlpha.QuantumMechanics.HilbertSpaces.FiniteTarget.Operators

/-!

# Energy–position uncertainty in the open tight binding chain

The Hamiltonian and the position operator of the tight binding chain with open boundary
conditions are observables of the C⋆-algebra of operators on the Hilbert space of the chain.
The Robertson–Schrödinger relation then bounds their spreads in every state by the expected
bracket `⁅H, X⁆ = -(i/2) (H X - X H)`, which only sees hopping: its matrix elements are
`-(i/2) a (n - m) ⟨m|H|n⟩`.

## Main results

- `toObservable` : a hermitian operator of the chain as an observable.
- `openHamiltonianObservable`, `positionObservable` : `H` and `X` as observables.
- `inner_bracket_openHamiltonian_position` : the matrix elements of `⁅H, X⁆`.
- `inner_bracket_openHamiltonian_position_eq` : `⁅H, X⁆` moves exactly one site `a`.
- `robertson_schrodinger_openHamiltonian_position` : the energy–position uncertainty relation.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace selfAdjoint
open ProbabilisticTheory
open ContinuousLinearMap UnitalPositiveLinearMap

namespace CondensedMatter
namespace TightBindingChain
variable (T : TightBindingChain)

/-- A hermitian operator of the chain as an observable. -/
noncomputable def toObservable (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) (hA : A.IsSymmetric) :
    Observable (T.HilbertSpace →L[ℂ] T.HilbertSpace) :=
  ⟨LinearMap.toContinuousLinearMap A, isSelfAdjoint_iff_isSymmetric.mpr hA⟩

/-- The Hamiltonian with open boundary conditions as an observable. -/
noncomputable abbrev openHamiltonianObservable :=
  T.toObservable T.openHamiltonian T.openHamiltonian_hermitian

/-- The position operator as an observable. -/
noncomputable abbrev positionObservable := T.toObservable T.position T.position_hermitian

/-- The bracket `⁅H, X⁆` only connects sites joined by hopping, weighted by their distance. -/
lemma inner_bracket_openHamiltonian_position (m n : Fin T.N) :
    ⟪|m⟩, ((⁅T.openHamiltonianObservable, T.positionObservable⁆ : Observable _) :
      _ →L[ℂ] _) |n⟩⟫_ℂ =
      -(Complex.I / 2) * ((T.a * ((n : ℕ) - (m : ℕ)) : ℝ) : ℂ) *
        ⟪|m⟩, T.openHamiltonian |n⟩⟫_ℂ := by
  rw [selfAdjoint.coe_bracket, smul_apply, inner_smul_right, mul_assoc,
    ← inner_commutator_position]
  rfl

/-- The bracket `⁅H, X⁆` moves the particle exactly one site, a distance `a`, with amplitude
`± i a t / 2`; every other matrix element vanishes. -/
lemma inner_bracket_openHamiltonian_position_eq (m n : Fin T.N) :
    ⟪|m⟩, ((⁅T.openHamiltonianObservable, T.positionObservable⁆ : Observable _) :
      _ →L[ℂ] _) |n⟩⟫_ℂ =
      if (m : ℕ) + 1 = n then Complex.I * (T.a * T.t / 2 : ℝ)
      else if (n : ℕ) + 1 = m then -(Complex.I * (T.a * T.t / 2 : ℝ)) else 0 := by
  rw [inner_bracket_openHamiltonian_position, inner_openHamiltonian]
  by_cases hA : (m : ℕ) + 1 = n
  · have hn : ((n : ℕ) : ℂ) = (m : ℕ) + 1 := by exact_mod_cast hA.symm
    simp only [hA, Fin.ext_iff, true_or, ite_true, show (m : ℕ) ≠ n by omega, ite_false]
    push_cast [hn]
    ring
  by_cases hB : (n : ℕ) + 1 = m
  · have hm : ((m : ℕ) : ℂ) = (n : ℕ) + 1 := by exact_mod_cast hB.symm
    simp only [hA, hB, Fin.ext_iff, or_true, ite_true, show (m : ℕ) ≠ n by omega, ite_false]
    push_cast [hm]
    ring
  split_ifs with h <;> simp_all

/-- **Energy–position uncertainty of the open tight binding chain.** In every state `ω`,
`Cov(H, X)² + ⟨⁅H, X⁆⟩² ≤ Var H · Var X`. -/
lemma robertson_schrodinger_openHamiltonian_position
    (ω : 𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace]) :
    covariance ω T.openHamiltonianObservable T.positionObservable ^ 2 +
        ω⟨⁅T.openHamiltonianObservable, T.positionObservable⁆⟩ ^ 2 ≤
      variance ω T.openHamiltonianObservable * variance ω T.positionObservable :=
  robertson_schrodinger ω _ _

end TightBindingChain
end CondensedMatter
