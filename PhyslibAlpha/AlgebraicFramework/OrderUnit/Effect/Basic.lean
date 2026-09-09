/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Weight.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.UnitInterval

/-!

# Effects

## i. Overview

An effect is a bounded element of `E`: `0 ≤ e ≤ 1`, a possible outcome of a yes/no measurement.

Effects are also closed under mixing: a probabilistic combination of two effects is again an
effect (`Effect.convex`, `Effect.mix`) — the same fact as `Set.Icc` being convex.

## ii. Key definitions and results

- `Effect E`
- `Effect.complement`
- `Effect.mix` : a probabilistic mixture of two effects, again an effect.
- `Effect.IsSharp` : extremality in the effect interval.

## iii. Table of contents

- A. Effects and complements
- B. Convex mixtures
- C. Sharp effects
- D. Pairing effects with weights

-/

@[expose] public section

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [One E]

/-- An effect: a bounded element of `E`. -/
abbrev Effect (E : Type*) [AddCommGroup E] [PartialOrder E] [One E] := Set.Icc (0 : E) 1

namespace Effect

/-! ## A. Effects and complements -/

/-- Regard an effect as an element of the positive cone, forgetting the upper bound. -/
def toPosCone (e : Effect E) : PosCone E := ⟨e.1, e.2.1⟩

omit [IsOrderedAddMonoid E] in
@[simp] lemma coe_toPosCone (e : Effect E) : ((toPosCone e) : E) = e.1 := rfl

/-- The complementary effect `1 - e`. -/
def complement (e : Effect E) : Effect E :=
  ⟨1 - e.1, sub_nonneg.mpr e.2.2, sub_le_self 1 e.2.1⟩

@[simp]
lemma complement_complement (e : Effect E) : complement (complement e) = e := by
  apply Subtype.ext
  simp [complement]

variable [IsOrderUnit E]

instance : Zero (Effect E) := ⟨0, le_refl 0, IsOrderUnit.one_nonneg⟩
instance : One (Effect E) := ⟨1, IsOrderUnit.one_nonneg, le_refl 1⟩

omit [IsOrderedAddMonoid E] in
@[simp] lemma coe_zero : ((0 : Effect E) : E) = 0 := rfl

omit [IsOrderedAddMonoid E] in
@[simp] lemma coe_one : ((1 : Effect E) : E) = 1 := rfl

@[simp] lemma complement_zero : complement (0 : Effect E) = 1 := by
  apply Subtype.ext; simp [complement]

@[simp] lemma complement_one : complement (1 : Effect E) = 0 := by
  apply Subtype.ext; simp [complement]

variable [Module ℝ E] [PosSMulMono ℝ E]

/-! ## B. Convex mixtures -/

omit [IsOrderUnit E] in
/-- Effects are closed under probabilistic mixing: mixing two possible outcomes gives another
possible outcome. This is the same convexity that makes states convex (`States/Convex.lean`):
preparations (states) and measurement outcomes (effects) pair via the abstract Born rule
`(ω, e) ↦ ω(e) ∈ [0, 1]`, and both sides of that pairing are convex sets, so both have a notion of
extreme point — extreme states are pure states, extreme effects are sharp (`IsSharp`). -/
lemma convex : Convex ℝ (Effect E : Set E) := convex_Icc 0 1

/-- The mixture of two effects, choosing the first with probability `t`. -/
def mix (e₁ e₂ : Effect E) (t : unitInterval) : Effect E :=
  ⟨(t : ℝ) • (e₁ : E) + (1 - (t : ℝ)) • (e₂ : E),
    convex e₁.2 e₂.2 t.2.1 (sub_nonneg.mpr t.2.2) (by ring)⟩

omit [IsOrderUnit E] in
@[simp]
lemma coe_mix (e₁ e₂ : Effect E) (t : unitInterval) :
    (mix e₁ e₂ t : E) = (t : ℝ) • (e₁ : E) + (1 - (t : ℝ)) • (e₂ : E) := rfl

omit [IsOrderUnit E] in
@[simp] lemma mix_zero (e₁ e₂ : Effect E) : mix e₁ e₂ 0 = e₂ := by apply Subtype.ext; simp

omit [IsOrderUnit E] in
@[simp] lemma mix_one (e₁ e₂ : Effect E) : mix e₁ e₂ 1 = e₁ := by apply Subtype.ext; simp

omit [One E] [IsOrderUnit E] [Module ℝ E] [PosSMulMono ℝ E] in
/-- A nonnegative vector that adds with another nonnegative vector to `0` is itself `0`: the
positive cone of an ordered vector space meets its negation only at `0`. Not specific to effects,
but stated here for lack of a better shared home; reused e.g. by `StarAlgebra/SharpEffect.lean`. -/
lemma nonneg_add_eq_zero {a b : E} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 0) : a = 0 :=
  le_antisymm (hab ▸ le_add_of_nonneg_right hb) ha

/-! ## C. Sharp effects -/

/-- An effect is sharp when it is an extreme point of the effect interval `[0, 1]`: it cannot be
written as a nontrivial mixture of two distinct effects. Sharp effects generalize projections: in
a C⋆-algebra, `e` is sharp iff `e ^ 2 = e = star e`, i.e. `e` is a genuine projection
(`StarAlgebra/SharpEffect.lean`); a sharp measurable-outcome measurement is a PVM. -/
def IsSharp (e : Effect E) : Prop := (e : E) ∈ Set.extremePoints ℝ (Set.Icc (0 : E) 1)

/-- The impossible outcome is sharp: `0 = a • x₁ + b • x₂` with `x₁, x₂ ∈ [0, 1]` and `a, b > 0`
forces `x₁ = 0`, since `a • x₁` and `b • x₂` are nonnegative terms summing to `0`. -/
lemma isSharp_zero : IsSharp (0 : Effect E) := by
  refine ⟨⟨le_refl 0, IsOrderUnit.one_nonneg⟩, fun x₁ hx₁ _ hx₂ ⟨a, b, ha, hb, _, hz⟩ => ?_⟩
  have hax : a • x₁ = 0 :=
    nonneg_add_eq_zero (smul_nonneg ha.le hx₁.1) (smul_nonneg hb.le hx₂.1) (by simpa using hz)
  have := congrArg (a⁻¹ • ·) hax
  rwa [inv_smul_smul₀ ha.ne', smul_zero] at this

omit [IsOrderUnit E] [PosSMulMono ℝ E] in
/-- Sharpness is preserved by taking the complement: `e ↦ 1 - e` is an affine involution of the
effect interval, so it carries the open segment through `x₁, x₂` to the open segment through
`1 - x₁, 1 - x₂`, transporting extremality of `e` to extremality of `complement e`. -/
lemma isSharp_complement {e : Effect E} (h : IsSharp e) : IsSharp (complement e) := by
  refine ⟨(complement e).2, fun x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hz⟩ => ?_⟩
  have hone : a • (1 : E) + b • (1 : E) = 1 := by rw [← add_smul, hab, one_smul]
  have key : a • (1 - x₁) + b • (1 - x₂) = (e : E) := by
    have hsplit : a • (1 - x₁) + b • (1 - x₂) =
        (a • (1 : E) + b • (1 : E)) - (a • x₁ + b • x₂) := by
      simp only [smul_sub]; abel
    rw [hsplit, hone, hz]
    show (1 : E) - (1 - (e : E)) = (e : E)
    abel
  have x1eq := (mem_extremePoints_iff_left.mp h).2 (1 - x₁)
    ⟨sub_nonneg.mpr hx₁.2, sub_le_self 1 hx₁.1⟩ (1 - x₂)
    ⟨sub_nonneg.mpr hx₂.2, sub_le_self 1 hx₂.1⟩ ⟨a, b, ha, hb, hab, key⟩
  have hsum : x₁ + (e : E) = 1 := by rw [← x1eq]; abel
  exact eq_sub_of_add_eq hsum

omit [IsOrderUnit E] [PosSMulMono ℝ E] in
/-- Sharpness is preserved by taking the complement, in either direction: `isSharp_complement`
applied twice, using `complement_complement` to undo the second application. -/
lemma isSharp_complement_iff {e : Effect E} : IsSharp (complement e) ↔ IsSharp e :=
  ⟨fun h => complement_complement e ▸ isSharp_complement h, isSharp_complement⟩

/-- The certain outcome is sharp: the complement of the (sharp) impossible outcome. -/
lemma isSharp_one : IsSharp (1 : Effect E) :=
  complement_zero (E := E) ▸ isSharp_complement isSharp_zero

end Effect

namespace Weight

/-! ## D. Pairing effects with weights -/

variable [Module ℝ E] [PosSMulMono ℝ E] [IsOrderUnit E]


/-- Pairing a weight with an effect is bounded by the weight of the order unit. -/
lemma pairing_le_unit (w : Weight E) (e : Effect E) : w (Effect.toPosCone e) ≤ w unit :=
  w.mono e.2.2

/-- A weight finite at the order unit pairs finitely with every effect. -/
lemma pairing_ne_top (w : Weight E) (hw : w unit ≠ ⊤) (e : Effect E) :
    w (Effect.toPosCone e) ≠ ⊤ :=
  ne_top_of_le_ne_top hw (w.pairing_le_unit e)

end Weight
