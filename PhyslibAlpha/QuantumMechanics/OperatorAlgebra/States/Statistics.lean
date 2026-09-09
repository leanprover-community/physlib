/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.States.Basic
public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Jordan
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Observable

/-!

# State statistics

A state assigns real expectation values to observables. Centering observables
produces covariance and variance, the quantities used in uncertainty relations.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

namespace State

/-! ## Expectation -/

/-- The real state on observables induced by `ω`. Its value at `a` is the mean value a physicist
would call `⟨a⟩`, obtained by averaging repeated measurements of `a` on systems prepared in
state `ω`. -/
noncomputable def expectation (ω : State A) : 𝓢[ℝ, Observable A] :=
  ω.onObservables

@[inherit_doc State.expectation]
scoped[OperatorAlgebra] notation:max ω "⟨" a "⟩" => State.expectation ω a

attribute [nolint docBlame] OperatorAlgebra.«term_⟨_⟩»

/-- The complex-valued state functional agrees with the real expectation notation `ω⟨a⟩` on
observables: no information is lost, since self-adjoint elements have vanishing imaginary part. -/
lemma apply_observable_eq_expectation (ω : State A) (a : Observable A) :
    ω (a : A) = (ω⟨a⟩ : ℂ) := by
  exact (UnitalPositiveLinearMap.coe_onObservables_apply ω a).symm

/-- The trivial "do-nothing" observable `1` is measured with certainty: probabilities sum to one. -/
@[simp]
lemma expectation_one (ω : State A) :
    ω⟨(1 : Observable A)⟩ = 1 := by
  simp [expectation]

/-- Positive observables have nonnegative expectation. -/
lemma expectation_nonneg (ω : State A) {a : Observable A}
    (ha : 0 ≤ (a : A)) :
    0 ≤ ω⟨a⟩ :=
  (expectation ω).map_nonneg ha

/-! ## Centering -/

/-- The fluctuation of an observable around its mean: `a` with `ω⟨a⟩` subtracted off. Its
statistics (`covariance`, `variance`) describe the spread of `a`'s outcomes. -/
noncomputable def centered (ω : State A) (a : Observable A) : Observable A :=
  a - ω⟨a⟩ • 1

/-- A fluctuation has zero mean by construction: the average deviation from the average is zero. -/
@[simp]
lemma expectation_centered (ω : State A) (a : Observable A) :
    ω⟨centered ω a⟩ = 0 := by
  simp [centered]

/-- Shifting an observable by a deterministic constant `c` shifts its mean by `c` too, so the
fluctuation around the new mean is unchanged. -/
@[simp]
lemma centered_add_smul_one (ω : State A) (a : Observable A) (c : ℝ) :
    centered ω (a + c • 1) = centered ω a := by
  simp only [centered, map_add, map_smul, expectation_one]
  module

/-! ## Covariance and variance -/

/-- The correlation between two observables' fluctuations in state `ω`: the mean of their
symmetrized (Jordan) product once each is centered. Nonzero covariance means a measurement of `a`
carries statistical information about `b`. -/
noncomputable def covariance (ω : State A) (a b : Observable A) : ℝ :=
  ω⟨centered ω a ⊙ centered ω b⟩

/-- The spread of `a`'s measurement outcomes about its mean — the quantum analogue of a random
variable's variance, whose square root is the uncertainty `Δa` in `States.Uncertainty`. -/
noncomputable def variance (ω : State A) (a : Observable A) : ℝ :=
  covariance ω a a

/-- Unfolds `variance` as covariance of an observable with itself. -/
@[simp]
lemma covariance_self (ω : State A) (a : Observable A) :
    covariance ω a a = variance ω a :=
  rfl

/-- Variance is the expectation of the squared fluctuation about the mean. -/
lemma variance_eq_re_apply_centered_mul_self (ω : State A) (a : Observable A) :
    variance ω a = (ω ((centered ω a : A) * centered ω a)).re := by
  rw [variance, covariance]
  change (ω ((centered ω a ⊙ centered ω a : Observable A) : A)).re = _
  rw [Observable.jordan_self]

/-- Covariance is symmetric, because the underlying Jordan product is symmetric. -/
lemma covariance_comm (ω : State A) (a b : Observable A) :
    covariance ω a b = covariance ω b a := by
  simp only [covariance]
  rw [Observable.jordan_comm]

/-- Covariance depends only on fluctuations: shifting the left observable by a constant `c`
leaves it unchanged. -/
lemma covariance_add_smul_one_left (ω : State A) (a b : Observable A) (c : ℝ) :
    covariance ω (a + c • 1) b = covariance ω a b := by
  simp only [covariance, centered_add_smul_one]

/-- Covariance depends only on fluctuations: shifting the right observable by a constant `c`
leaves it unchanged. -/
lemma covariance_add_smul_one_right (ω : State A) (a b : Observable A) (c : ℝ) :
    covariance ω a (b + c • 1) = covariance ω a b := by
  simp only [covariance, centered_add_smul_one]

/-- Repeated measurements of an observable can never have negative spread about their mean: the
physical content of variance being an honest measure of statistical uncertainty. Algebraically,
this is positivity of the state applied to the "square" `(centered a) ⊙ (centered a)`, which is
`(centered a)†(centered a)` in disguise (`Observable.jordan_self`). -/
lemma variance_nonneg (ω : State A) (a : Observable A) :
    0 ≤ variance ω a := by
  rw [variance, covariance]
  apply expectation_nonneg
  show 0 ≤ (Observable.jordan (centered ω a) (centered ω a) : A)
  rw [Observable.jordan_self]
  simpa [(centered ω a).property.star_eq] using
    star_mul_self_nonneg (centered ω a : A)

end State

end OperatorAlgebra
