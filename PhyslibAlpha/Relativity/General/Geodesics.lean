/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-!

# The geodesic Cauchy problem

Local existence and uniqueness for the geodesic equation via Picard–Lindelöf.

## i. Overview

Given Christoffel symbols `Γ` on a chart modeled on a Banach space `E`, the second-order geodesic
equation `γ'' = -Γ(γ)(γ', γ')` reduces to the first-order autonomous system
`z' = (z.2, -Γ(z.1)(z.2, z.2))` on `E × E`. When `Γ` is `C¹`, Mathlib's Picard–Lindelöf theorem
yields local existence around any initial position and velocity `(x₀, v₀)`, as well as uniqueness
under an explicit Lipschitz bound on the geodesic vector field. In flat space (`Γ = 0`),
straight lines `t ↦ x₀ + t • v₀` solve the geodesic equation.

## ii. Key results

- `Christoffel`, `geodesicAccel`, `geodesicField` : Christoffel field and first-order geodesic
  ODE vector field on `E × E`.
- `geodesic_ivp_exists` : local existence of a geodesic solution on some `(-ε, ε)` for `C¹`
  Christoffel symbols.
- `geodesic_ivp_exists_curve` : split curve-and-velocity form of local geodesic existence.
- `geodesic_ivp_unique` : uniqueness on `[a, b]` inside a Lipschitz ball.
- `flat_geodesic` : straight lines solve the flat-space geodesic equation.

## iii. Table of contents

- A. The geodesic vector field
- B. Local existence and uniqueness
- C. Flat-space straight lines

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!

## A. The geodesic vector field

-/

/-- Christoffel symbols on a chart, represented as a field of continuous bilinear maps. -/
abbrev Christoffel (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E → E →L[ℝ] E →L[ℝ] E

/-- Geodesic acceleration `-Γ(x)(v, v)`. -/
def geodesicAccel (Γ : Christoffel E) (x v : E) : E := - Γ x v v

/-- The first-order form of the geodesic equation on state `(position, velocity)`. -/
def geodesicField (Γ : Christoffel E) : E × E → E × E :=
  fun z => (z.2, geodesicAccel Γ z.1 z.2)

/-- Evaluation of `geodesicField` on a pair `(x, v)`. -/
@[simp]
lemma geodesicField_apply (Γ : Christoffel E) (x v : E) :
    geodesicField Γ (x, v) = (v, geodesicAccel Γ x v) := rfl

/-- The geodesic vector field inherits `C¹` regularity from the Christoffel symbols. -/
lemma contDiffAt_geodesicField (Γ : E → E →L[ℝ] E →L[ℝ] E) {x₀ v₀ : E}
    (hΓ : ContDiffAt ℝ 1 Γ x₀) :
    ContDiffAt ℝ 1 (geodesicField Γ) (x₀, v₀) := by
  unfold geodesicField geodesicAccel
  fun_prop

/-- First projection of a differentiable curve into a product. -/
lemma hasDerivAt_fst {f : ℝ → E × E} {f' : E × E} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).1) f'.1 t := by
  simpa [Function.comp_def] using
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t h

/-- Second projection of a differentiable curve into a product. -/
lemma hasDerivAt_snd {f : ℝ → E × E} {f' : E × E} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).2) f'.2 t := by
  simpa [Function.comp_def] using
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t h

/-!

## B. Local existence and uniqueness

-/

/-- Local existence for the geodesic Cauchy problem: given `C¹` Christoffel symbols, every pair
of initial position and velocity generates a geodesic on an open interval `(-ε, ε)`. -/
lemma geodesic_ivp_exists [CompleteSpace E] (Γ : Christoffel E) (hΓ : ContDiff ℝ 1 Γ)
    (x₀ v₀ : E) :
    ∃ ε > 0, ∃ z : ℝ → E × E, z 0 = (x₀, v₀) ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => (z s).1) (z t).2 t ∧
        HasDerivAt (fun s => (z s).2) (geodesicAccel Γ (z t).1 (z t).2) t := by
  have hf : ContDiffAt ℝ 1 (geodesicField Γ) (x₀, v₀) :=
    contDiffAt_geodesicField Γ hΓ.contDiffAt
  obtain ⟨r, hr, ε, hε, H⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  obtain ⟨z, hz0, hz⟩ := H (x₀, v₀) (mem_closedBall_self (le_of_lt hr))
  refine ⟨ε, hε, z, hz0, fun t ht => ?_⟩
  have h := hz t (by simpa using ht)
  exact ⟨hasDerivAt_fst h, hasDerivAt_snd h⟩

/-- Curve-and-velocity form of local existence for the geodesic Cauchy problem. -/
lemma geodesic_ivp_exists_curve [CompleteSpace E] (Γ : Christoffel E) (hΓ : ContDiff ℝ 1 Γ)
    (x₀ v₀ : E) :
    ∃ ε > 0, ∃ γ w : ℝ → E, γ 0 = x₀ ∧ w 0 = v₀ ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt γ (w t) t ∧
        HasDerivAt w (geodesicAccel Γ (γ t) (w t)) t := by
  obtain ⟨ε, hε, z, hz0, hz⟩ := geodesic_ivp_exists Γ hΓ x₀ v₀
  refine ⟨ε, hε, fun t => (z t).1, fun t => (z t).2, ?_, ?_, fun t ht => hz t ht⟩
  · simpa using congrArg Prod.fst hz0
  · simpa using congrArg Prod.snd hz0

/-- Uniqueness for the geodesic Cauchy problem: two solutions agreeing at `t₀ ∈ (a, b)` that
remain in a ball where `geodesicField Γ` is `K`-Lipschitz coincide on `[a, b]`. -/
lemma geodesic_ivp_unique (Γ : Christoffel E) {K : NNReal} {a b t₀ : ℝ}
    {c : E × E} {R : ℝ}
    (hLip : ∀ t ∈ Ioo a b, LipschitzOnWith K (geodesicField Γ) (closedBall c R))
    (ht : t₀ ∈ Ioo a b) {z₁ z₂ : ℝ → E × E}
    (h₁ : ContinuousOn z₁ (Icc a b))
    (h₁' : ∀ t ∈ Ioo a b, HasDerivAt z₁ (geodesicField Γ (z₁ t)) t)
    (h₁s : ∀ t ∈ Ioo a b, z₁ t ∈ closedBall c R)
    (h₂ : ContinuousOn z₂ (Icc a b))
    (h₂' : ∀ t ∈ Ioo a b, HasDerivAt z₂ (geodesicField Γ (z₂ t)) t)
    (h₂s : ∀ t ∈ Ioo a b, z₂ t ∈ closedBall c R)
    (h₀ : z₁ t₀ = z₂ t₀) : EqOn z₁ z₂ (Icc a b) :=
  ODE_solution_unique_of_mem_Icc (v := fun _ => geodesicField Γ)
    (s := fun _ => closedBall c R) hLip ht h₁ h₁' h₁s h₂ h₂' h₂s h₀

/-!

## C. Flat-space straight lines

-/

/-- In flat space (`Γ = 0`) the geodesic vector field reduces to `(v, 0)`. -/
lemma geodesicField_zero (x v : E) :
    geodesicField (fun _ : E => 0) (x, v) = (v, 0) := by
  simp [geodesicField, geodesicAccel]

/-- In flat space, `t ↦ x₀ + t • v₀` has constant velocity `v₀` and solves `γ'' = 0`. -/
lemma flat_geodesic (x₀ v₀ : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x₀ + s • v₀) v₀ t ∧
      HasDerivAt (fun _ : ℝ => v₀) 0 t := by
  refine ⟨?_, hasDerivAt_const t v₀⟩
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  simpa using (hid.smul_const v₀).const_add x₀

end GeneralRelativity
