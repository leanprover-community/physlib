/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.Algebra.Statistics
public import PhyslibAlpha.AlgebraicFramework.StarAlgebra.Jordan

/-!

# State statistics

A state assigns real expectation values to observables (`UnitalPositiveLinearMap.expectation`,
notation `ω⟨a⟩`, built directly from `UnitalPositiveLinearMap.onObservables`). Centering an
observable around its mean produces `covariance` and `variance`, the quantities the uncertainty
relations in `CStarAlgebra.Uncertainty` are stated in terms of.

None of this needs a C⋆-norm or completeness: a state `ω : 𝓢[A]` already restricts to a real
state on `Observable A`, and positivity of `variance` is already positivity of a state applied to
`star x * x` for `x` self-adjoint. Consequently almost everything here is stated for a bare star
ring with a compatible order (`Ring`, `StarRing`, `PartialOrder`, plus `SelfAdjointDecompose`,
`Module ℂ`, `StarModule ℂ` for `𝓢[A]`/`onObservables` themselves to make sense) — exactly the
level `UnitalPositiveLinearMap.onObservables` needs. `StarOrderedRing` is added locally, only on
`variance_nonneg`, for the one positivity fact (`star_mul_self_nonneg`) that actually needs it;
symmetry of `covariance` needs no order at all, just `apply_mul_comm_eq_star`.

## Main definitions

- `UnitalPositiveLinearMap.expectation`, notation `ω⟨a⟩` : the real expectation value of an
  observable `a` in state `ω`.
- `UnitalPositiveLinearMap.centered` : an observable with its mean subtracted off.
- `UnitalPositiveLinearMap.covariance`, `UnitalPositiveLinearMap.variance` : the correlation
  between two observables' fluctuations, and the spread of one observable's own fluctuations.

-/

@[expose] public section

open scoped ComplexOrder
open scoped selfAdjoint

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A]
    [SelfAdjointDecompose A] [Module ℂ A] [StarModule ℂ A]
    [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]

namespace UnitalPositiveLinearMap

/-! ## Expectation -/

/-- The real state on observables induced by `ω`. Its value at `a` is the mean value a physicist
would call `⟨a⟩`, obtained by averaging repeated measurements of `a` on systems prepared in
state `ω`. This is exactly `onObservables`, under a name and notation that reads as expectation
rather than restriction. -/
noncomputable def expectation (ω : 𝓢[A]) : 𝓢[ℝ, Observable A] :=
  ω.onObservables

@[inherit_doc expectation]
scoped notation:max ω "⟨" a "⟩" => UnitalPositiveLinearMap.expectation ω a

attribute [nolint docBlame] UnitalPositiveLinearMap.«term_⟨_⟩»

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- The complex-valued state functional agrees with the real expectation notation `ω⟨a⟩` on
observables: no information is lost, since self-adjoint elements have vanishing imaginary part. -/
lemma apply_observable_eq_expectation (ω : 𝓢[A]) (a : Observable A) :
    ω (a : A) = (ω⟨a⟩ : ℂ) :=
  (coe_onObservables_apply ω a).symm

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- The trivial "do-nothing" observable `1` is measured with certainty: probabilities sum to one. -/
@[simp]
lemma expectation_one (ω : 𝓢[A]) :
    ω⟨(1 : Observable A)⟩ = 1 := by
  simp [expectation]

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- Positive observables have nonnegative expectation. -/
lemma expectation_nonneg (ω : 𝓢[A]) {a : Observable A} (ha : 0 ≤ (a : A)) :
    0 ≤ ω⟨a⟩ :=
  (expectation ω).map_nonneg ha

/-! ## Centering -/

/-- The fluctuation of an observable around its mean: `a` with `ω⟨a⟩` subtracted off. Its
statistics (`covariance`, `variance`) describe the spread of `a`'s outcomes. -/
noncomputable def centered (ω : 𝓢[A]) (a : Observable A) : Observable A :=
  LinearMap.centered (expectation ω).toLinearMap a

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- A fluctuation has zero mean by construction: the average deviation from the average is zero. -/
@[simp]
lemma expectation_centered (ω : 𝓢[A]) (a : Observable A) :
    ω⟨centered ω a⟩ = 0 := by
  exact LinearMap.apply_centered (expectation ω).toLinearMap (expectation_one ω) a

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- Shifting an observable by a deterministic constant `c` shifts its mean by `c` too, so the
fluctuation around the new mean is unchanged. -/
@[simp]
lemma centered_add_smul_one (ω : 𝓢[A]) (a : Observable A) (c : ℝ) :
    centered ω (a + c • 1) = centered ω a := by
  simp only [centered, LinearMap.centered, map_add, map_smul]
  rw [show (expectation ω).toLinearMap 1 = 1 from expectation_one ω]
  module

/-! ## Reversing a product -/

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
/-- Reversing the order of two self-adjoint elements in a product conjugates the state's value on
it. Purely algebraic — needs only `map_star` and self-adjointness, no positivity or completeness —
so it is what makes `covariance` symmetric below without any detour through a Jordan product. -/
lemma apply_mul_comm_eq_star (ω : 𝓢[A]) (a b : Observable A) :
    ω ((b : A) * a) = star (ω ((a : A) * b)) := by
  rw [← map_star, star_mul, a.property.star_eq, b.property.star_eq]

/-! ## Covariance and variance -/

/-- The correlation between two observables' fluctuations in state `ω`: the real part of the
expectation of the (uncentered) product of their fluctuations. `apply_mul_comm_eq_star` makes this
symmetric in `a`, `b` (`covariance_comm`) without needing a symmetrized product to define it.
Nonzero covariance means a measurement of `a` carries statistical information about `b`. -/
noncomputable def covariance (ω : 𝓢[A]) (a b : Observable A) : ℝ :=
  LinearMap.covarianceForm (expectation ω).toLinearMap a b

/-- The spread of `a`'s measurement outcomes about its mean — the quantum analogue of a random
variable's variance, whose square root is the uncertainty `Δa` in `CStarAlgebra.Uncertainty`. -/
noncomputable def variance (ω : 𝓢[A]) (a : Observable A) : ℝ :=
  covariance ω a a

/-- Unfolds `variance` as covariance of an observable with itself. -/
@[simp]
lemma covariance_self (ω : 𝓢[A]) (a : Observable A) :
    covariance ω a a = variance ω a :=
  rfl

/-- The canonical covariance form on the Jordan algebra of observables is the real part of the
state applied to the ordinary associative product of the centered observables. This is a
specialization theorem, not a second definition of covariance. -/
lemma covariance_eq_re_apply_centered_mul (ω : 𝓢[A]) (a b : Observable A) :
    covariance ω a b = (ω ((centered ω a : A) * centered ω b)).re := by
  rw [covariance]
  rw [← LinearMap.apply_centered_mul_centered (expectation ω).toLinearMap (expectation_one ω)
    selfAdjoint.one_jordanMul selfAdjoint.jordanMul_one]
  set x := centered ω a
  set y := centered ω b
  have hstar : ω ((y : A) * x) = star (ω ((x : A) * y)) :=
    apply_mul_comm_eq_star ω x y
  have hval := apply_observable_eq_expectation ω (x * y)
  rw [selfAdjoint.coe_mul, UnitalPositiveLinearMap.map_smul_of_tower, map_add, hstar,
    Complex.real_smul] at hval
  have hsum : ω ((x : A) * y) + star (ω ((x : A) * y)) =
      (2 : ℂ) * (ω ((x : A) * y)).re := by
    rw [Complex.star_def, Complex.add_conj]
    push_cast
    ring
  rw [hsum] at hval
  have hval' : ((expectation ω (x * y) : ℝ) : ℂ) = ((ω ((x : A) * y)).re : ℝ) := by
    calc
      ((expectation ω (x * y) : ℝ) : ℂ) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (2 * ((ω ((x : A) * y)).re : ℂ)) := hval.symm
      _ = ((ω ((x : A) * y)).re : ℂ) := by
        apply Complex.ext <;> (norm_num <;> ring)
  exact_mod_cast hval'

/-- Variance is the expectation of the squared fluctuation about the mean: unfolds `variance` and
`covariance` together. Stated as its own lemma (even though now definitionally `rfl`) since
`CStarAlgebra.Uncertainty` uses it under this name. -/
lemma variance_eq_re_apply_centered_mul_self (ω : 𝓢[A]) (a : Observable A) :
    variance ω a = (ω ((centered ω a : A) * centered ω a)).re := by
  rw [variance, covariance_eq_re_apply_centered_mul]

/-- Covariance is symmetric: reversing a product of self-adjoint fluctuations conjugates the
state's value on it, and conjugation does not change the real part. -/
lemma covariance_comm (ω : 𝓢[A]) (a b : Observable A) :
    covariance ω a b = covariance ω b a := by
  exact (LinearMap.covarianceForm_isSymm (expectation ω).toLinearMap
    fun x y => mul_comm x y).eq a b

/-- Covariance depends only on fluctuations: shifting the left observable by a constant `c`
leaves it unchanged. -/
lemma covariance_add_smul_one_left (ω : 𝓢[A]) (a b : Observable A) (c : ℝ) :
    covariance ω (a + c • 1) b = covariance ω a b := by
  change LinearMap.covarianceForm (expectation ω).toLinearMap (a + c • 1) b =
    LinearMap.covarianceForm (expectation ω).toLinearMap a b
  rw [map_add, map_smul]
  have hone : LinearMap.covarianceForm (expectation ω).toLinearMap (1 : Observable A) b = 0 := by
    rw [LinearMap.covarianceForm_apply]
    change expectation ω (selfAdjoint.jordanMul 1 b) - expectation ω 1 * expectation ω b = 0
    rw [selfAdjoint.one_jordanMul, expectation_one]
    ring
  simp only [LinearMap.add_apply, LinearMap.smul_apply, hone, smul_zero, add_zero]

/-- Covariance depends only on fluctuations: shifting the right observable by a constant `c`
leaves it unchanged. -/
lemma covariance_add_smul_one_right (ω : 𝓢[A]) (a b : Observable A) (c : ℝ) :
    covariance ω a (b + c • 1) = covariance ω a b := by
  change LinearMap.covarianceForm (expectation ω).toLinearMap a (b + c • 1) =
    LinearMap.covarianceForm (expectation ω).toLinearMap a b
  rw [map_add, map_smul]
  have hone : LinearMap.covarianceForm (expectation ω).toLinearMap a (1 : Observable A) = 0 := by
    rw [LinearMap.covarianceForm_apply]
    change expectation ω (selfAdjoint.jordanMul a 1) - expectation ω a * expectation ω 1 = 0
    rw [selfAdjoint.jordanMul_one, expectation_one]
    ring
  rw [hone, smul_zero, add_zero]

variable [StarOrderedRing A] in
/-- Repeated measurements of an observable can never have negative spread about their mean: the
physical content of variance being an honest measure of statistical uncertainty. Algebraically,
this is positivity of the state applied to `(centered a)† (centered a) = (centered a)^2`, which
already lands in the positive cone via `star_mul_self_nonneg` — no Jordan product needed. -/
lemma variance_nonneg (ω : 𝓢[A]) (a : Observable A) :
    0 ≤ variance ω a := by
  rw [variance_eq_re_apply_centered_mul_self]
  have h : (0 : A) ≤ (centered ω a : A) * centered ω a := by
    have hpos := star_mul_self_nonneg (centered ω a : A)
    rwa [(centered ω a).property.star_eq] at hpos
  exact (RCLike.nonneg_iff.mp (ω.map_nonneg h)).1

end UnitalPositiveLinearMap
