/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.OpenBoundary
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.State.VectorUncertainty

/-!

# Energy–position uncertainty in the open tight binding chain

The Hamiltonian and the position operator of the tight binding chain with open boundary
conditions, acting on the site amplitudes in `ℂ^N`, are observables of the C⋆-algebra of
operators on `ℂ^N`. The
Robertson–Schrödinger relation then bounds their spreads in every state by the expected
bracket `⁅H, X⁆ = -(i/2) (H X - X H)`, which only sees hopping: its matrix elements are
`-(i/2) a (n - m) ⟨m|H|n⟩`.

## Main results

- `toObservable` : a hermitian operator of the chain as an observable on `ℂ^N`.
- `openHamiltonianObservable`, `positionObservable` : `H` and `X` as observables.
- `inner_bracket_openHamiltonian_position` : the matrix elements of `⁅H, X⁆`.
- `inner_bracket_openHamiltonian_position_eq` : `⁅H, X⁆` moves exactly one site `a`.
- `robertson_schrodinger_openHamiltonian_position` : the energy–position uncertainty relation.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace selfAdjoint
open ContinuousLinearMap UnitalPositiveLinearMap

namespace CondensedMatter
namespace TightBindingChain
open QuantumMechanics.FiniteHilbertSpace
variable (T : TightBindingChain)

/-- A hermitian operator of the chain as an observable on the site amplitudes in `ℂ^N`. -/
noncomputable def toObservable (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace) (hA : A.IsSymmetric) :
    Observable (EuclideanSpace ℂ (Fin T.N) →L[ℂ] EuclideanSpace ℂ (Fin T.N)) :=
  ⟨LinearMap.toContinuousLinearMap (isometryEquivEuclidean.toLinearEquiv.conj A),
    isSelfAdjoint_iff_isSymmetric.mpr fun _ _ => hA _ _⟩

/-- The Hamiltonian with open boundary conditions as an observable. -/
noncomputable abbrev openHamiltonianObservable :=
  T.toObservable T.openHamiltonian T.openHamiltonian_hermitian

/-- The position operator as an observable. -/
noncomputable abbrev positionObservable := T.toObservable T.position T.position_hermitian

/-- The bracket `⁅H, X⁆` only connects sites joined by hopping, weighted by their distance. -/
lemma inner_bracket_openHamiltonian_position (m n : Fin T.N) :
    ⟪EuclideanSpace.single m (1 : ℂ), ((⁅T.openHamiltonianObservable, T.positionObservable⁆ :
      Observable _) : _ →L[ℂ] _) (EuclideanSpace.single n (1 : ℂ))⟫_ℂ =
      -(Complex.I / 2) * ((T.a * ((n : ℕ) - (m : ℕ)) : ℝ) : ℂ) *
        ⟪|m⟩, T.openHamiltonian |n⟩⟫_ℂ := by
  rw [selfAdjoint.coe_bracket, smul_apply, inner_smul_right, mul_assoc,
    ← inner_commutator_position, localizedState, basisFun_apply, basisFun_apply]
  rfl

/-- The bracket `⁅H, X⁆` moves the particle exactly one site, a distance `a`, with amplitude
`± i a t / 2`; every other matrix element vanishes. -/
lemma inner_bracket_openHamiltonian_position_eq (m n : Fin T.N) :
    ⟪EuclideanSpace.single m (1 : ℂ), ((⁅T.openHamiltonianObservable, T.positionObservable⁆ :
      Observable _) : _ →L[ℂ] _) (EuclideanSpace.single n (1 : ℂ))⟫_ℂ =
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
    (ω : 𝓢[EuclideanSpace ℂ (Fin T.N) →L[ℂ] EuclideanSpace ℂ (Fin T.N)]) :
    covariance ω T.openHamiltonianObservable T.positionObservable ^ 2 +
        ω⟨⁅T.openHamiltonianObservable, T.positionObservable⁆⟩ ^ 2 ≤
      variance ω T.openHamiltonianObservable * variance ω T.positionObservable :=
  robertson_schrodinger ω _ _

end TightBindingChain
end CondensedMatter
