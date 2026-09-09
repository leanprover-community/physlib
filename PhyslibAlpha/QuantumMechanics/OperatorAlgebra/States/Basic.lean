/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Physlib.Meta.Linters.Sorry

/-!

# States on observable algebras

A state is a normalized positive complex-linear functional. It records the
expectation values of observables in a physical preparation.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A state on `A`: a positive complex-linear functional normalized at `1`. -/
abbrev State (A : Type*) [OperatorAlgebra A] := 𝓢[A]

namespace State

variable {A : Type*} [OperatorAlgebra A]

/-- Positive functionals on a C⋆-algebra are automatically bounded, hence continuous. -/
noncomputable def toContinuousLinearMap (ω : State A) : A →L[ℂ] ℂ :=
  LinearMap.mkContinuousOfExistsBound ω.toLinearMap (by
    obtain ⟨C, hC⟩ := PositiveLinearMap.exists_norm_apply_le ω.toPositiveLinearMap
    exact ⟨C, hC⟩)

/-- The continuous-map bundling is just the same expectation functional with a continuity proof
attached. -/
@[simp]
lemma toContinuousLinearMap_apply (ω : State A) (a : A) :
    ω.toContinuousLinearMap a = ω.toPositiveLinearMap a := rfl

/-- Restating normalization (`ω.map_one`) for the continuous-map bundling.

Not `@[simp]`: `toContinuousLinearMap_apply` already rewrites the left-hand side to
`ω.toPositiveLinearMap 1`, so this would not be in simp normal form. -/
lemma toContinuousLinearMap_one (ω : State A) :
    ω.toContinuousLinearMap 1 = 1 := ω.map_one

/-! ## Basic physical consequences -/

/-- A state is *-linear, not just linear: measuring `a†` and conjugating agrees with conjugating
the measurement of `a`. This forces self-adjoint (physically observable) elements to have real
expectation values. -/
@[simp]
lemma apply_star (ω : State A) (a : A) :
    ω.toPositiveLinearMap (star a) = star (ω.toPositiveLinearMap a) := by
  rw [map_star]

/-- `a†a` stands in for "the squared magnitude of `a`", so a state assigns it nonnegative
expectation. This makes `a ↦ ω(a†a)` a genuine (semi-)inner product, the seed of the GNS
construction. -/
lemma apply_star_mul_self_nonneg (ω : State A) (a : A) :
    0 ≤ ω.toPositiveLinearMap (star a * a) := by
  exact ω.toPositiveLinearMap.map_nonneg (star_mul_self_nonneg a)

/-- A state never reports an expectation value bigger than the observable's operator norm.
Proved via GNS Cauchy–Schwarz against the identity: `|ω(a)|² ≤ ω(1) · ω(a†a) ≤ ‖a‖²`. -/
lemma norm_apply_le (ω : State A) (a : A) :
    ‖ω.toPositiveLinearMap a‖ ≤ ‖a‖ := by
  let φ := ω.toPositiveLinearMap
  change ‖φ a‖ ≤ ‖a‖
  have hcs := inner_mul_inner_self_le (𝕜 := ℂ) (φ.toPreGNS 1) (φ.toPreGNS a)
  simp only [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS, star_one,
    one_mul, mul_one] at hcs
  rw [show φ (star a) = star (φ a) from ω.apply_star a, norm_star,
    show φ (1 : A) = 1 from ω.map_one] at hcs
  have hbound : (φ (star a * a)).re ≤ ‖a‖ * ‖a‖ := by
    have hle := PositiveLinearMap.norm_apply_le_of_nonneg φ (star a * a) (star_mul_self_nonneg a)
    rw [show φ (1 : A) = 1 from ω.map_one, norm_one, one_mul,
      CStarRing.norm_star_mul_self] at hle
    exact (Complex.re_le_norm _).trans hle
  have hsq : ‖φ a‖ * ‖φ a‖ ≤ ‖a‖ * ‖a‖ := by
    calc ‖φ a‖ * ‖φ a‖ ≤ (1 : ℂ).re * (φ (star a * a)).re := hcs
      _ = (φ (star a * a)).re := by simp
      _ ≤ ‖a‖ * ‖a‖ := hbound
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa [sq] using hsq)

/-- A state has operator norm exactly one: `norm_apply_le` gives `≤ 1`, and `‖ω(1)‖ ≤ ‖ω‖ * ‖1‖`
with `ω(1) = 1` forces `≥ 1`. Physically, a state neither amplifies nor damps observables. -/
lemma norm_toContinuousLinearMap (ω : State A) :
    ‖ω.toContinuousLinearMap‖ = 1 := by
  -- A state exists on `A`, so `1 ≠ 0` in `A`: without this, `A` would be the zero algebra and
  -- `‖(1 : A)‖ = 1` (needed for the lower bound below) would not hold.
  have : Nontrivial A := ⟨1, 0, fun h => by
    have hmapOne : ω.toPositiveLinearMap (1 : A) = 1 := ω.map_one'
    have hmapZero : ω.toPositiveLinearMap (0 : A) = 0 := map_zero _
    rw [h, hmapZero] at hmapOne
    exact zero_ne_one hmapOne⟩
  refine le_antisymm
    (ω.toContinuousLinearMap.opNorm_le_bound zero_le_one fun a => by
      simpa using norm_apply_le ω a) ?_
  have h := ω.toContinuousLinearMap.le_opNorm 1
  simpa [toContinuousLinearMap_apply, ω.map_one, CStarRing.norm_one] using h

/-- Physical (self-adjoint) observables have real expectation values. -/
lemma state_is_real_on_selfAdjoint (ω : State A) {a : A}
    (ha : IsSelfAdjoint a) :
    Complex.im (ω.toPositiveLinearMap a) = 0 := by
  have h : star (ω.toPositiveLinearMap a) = ω.toPositiveLinearMap a := by
    rw [← apply_star, ha.star_eq]
  exact Complex.conj_eq_iff_im.mp (by simpa [Complex.star_def] using h)

end State

namespace State

/-- Two states are the same preparation iff they agree on every observable's expectation value. -/
@[ext]
lemma ext {ω φ : State A} (h : ∀ a, ω a = φ a) : ω = φ := by
  exact UnitalPositiveLinearMap.ext h

/-- States embed injectively into the continuous dual of `A`, letting `State A` borrow its
topology and convex structure (as `stateSpace` does in `States.Convex`). -/
lemma toContinuousLinearMap_injective :
    Function.Injective (fun ω : State A => ω.toContinuousLinearMap) := by
  intro ω φ h
  apply ext
  intro a
  exact congrArg (fun f : A →L[ℂ] ℂ => f a) h

end State

end OperatorAlgebra
