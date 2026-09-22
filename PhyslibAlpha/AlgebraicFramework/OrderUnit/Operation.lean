/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Effect.Basic
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Normal
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Basic
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!

# Operations

## i. Overview

An operation on `E` is a positive linear endomorphism that is not required to be unital: unlike a
channel (`Channel/Basic.lean`), it can lose "probability mass" — the way a single, non-selective
outcome of a measurement transforms a state without necessarily preserving its normalization.
What keeps it physical rather than an arbitrary positive map is that it never *gains* mass either:
`op 1 ≤ 1`. A channel is exactly an operation with `op 1 = 1` (`Channel/Basic.lean`'s
`UnitalPositiveLinearMap`); a finite family of operations whose images of `1` sum to exactly `1`
is an instrument (`Measurement/Instrument.lean`).

## ii. Key definitions and results

- `Operation E`
- `Operation.id`
- `Operation.comp`
- `Operation.condition`
- `Operation.outcomeEffect`

## iii. Table of contents

- A. Operations
- B. Outcome effects

-/

@[expose] public section

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E]

/-! ## A. Operations -/

/-- An operation on `E`: a positive linear endomorphism that never sends the certain event above
itself. -/
def Operation (E : Type*) [AddCommGroup E] [PartialOrder E] [Module ℝ E] [One E] :=
  {op : E →ₚ[ℝ] E // op 1 ≤ 1}

namespace Operation

/-- Regard an operation as its underlying positive linear map. -/
instance : CoeFun (Operation E) (fun _ => E → E) := ⟨fun op => op.1⟩

@[ext]
lemma ext {op₁ op₂ : Operation E} (h : ∀ x, op₁ x = op₂ x) : op₁ = op₂ :=
  Subtype.ext (PositiveLinearMap.ext h)

/-- An operation never sends a possible outcome to something negative. -/
lemma map_nonneg (op : Operation E) {x : E} (hx : 0 ≤ x) : 0 ≤ op x :=
  op.1.map_nonneg hx

/-- An operation never sends the certain event above itself. -/
lemma apply_one_le_one (op : Operation E) : op 1 ≤ 1 :=
  op.2

/-- Normality for operations is inherited from the single canonical normal-positive-map
predicate.  It is intentionally not a second directed-supremum definition. -/
abbrev IsNormal (op : Operation E) : Prop := op.1.IsNormal

/-- The identity operation. -/
def id : Operation E := ⟨PositiveLinearMap.id ℝ E, le_rfl⟩

@[simp]
lemma id_apply (x : E) : id (E := E) x = x := rfl

/-- The identity operation is normal. -/
lemma isNormal_id : (id (E := E)).IsNormal := fun D x _ _ hLUB => by
  change IsLUB ((fun y : E => y) '' D) x
  simpa using hLUB

/-- Sequential composition of operations.  Applying `φ` and then `ψ` is again subunital:
positivity makes `ψ` monotone, so `φ(1) ≤ 1` implies `ψ(φ(1)) ≤ ψ(1) ≤ 1`. -/
def comp (ψ φ : Operation E) : Operation E :=
  ⟨ψ.1.comp φ.1, (ψ.1.monotone' φ.2).trans ψ.2⟩

@[simp]
lemma comp_apply (ψ φ : Operation E) (x : E) : ψ.comp φ x = ψ (φ x) := rfl

@[simp]
lemma id_comp (φ : Operation E) : id.comp φ = φ := by
  apply ext
  intro x
  rfl

@[simp]
lemma comp_id (φ : Operation E) : φ.comp id = φ := by
  apply ext
  intro x
  rfl

lemma comp_assoc (χ ψ φ : Operation E) : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by
  apply ext
  intro x
  rfl

/-- Normal operations are closed under sequential composition, by the canonical positive-map
normality composition theorem. -/
lemma IsNormal.comp {φ ψ : Operation E} (hφ : φ.IsNormal) (hψ : ψ.IsNormal) :
    (ψ.comp φ).IsNormal :=
  PositiveLinearMap.IsNormal.comp hφ hψ

variable [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E]

/-- Normalize the pullback of a state along an operation whose outcome has nonzero probability.
This is the common post-measurement state construction: instruments and Jordan Lüders operations
specialize it instead of maintaining parallel normalizations. -/
noncomputable def condition (op : Operation E) (ω : 𝓢[ℝ, E])
    (hmass : 0 < ω (op 1)) : 𝓢[ℝ, E] :=
  UnitalPositiveLinearMap.ofLinearMap
    ((ω (op 1))⁻¹ • (ω.toLinearMap.comp op.1.toLinearMap))
    (fun x hx => by
      change 0 ≤ (ω (op 1))⁻¹ * ω (op x)
      exact mul_nonneg (inv_nonneg.mpr hmass.le) (ω.map_nonneg (op.map_nonneg hx)))
    (by
      change (ω (op 1))⁻¹ * ω (op 1) = 1
      exact inv_mul_cancel₀ hmass.ne')

omit [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- Pointwise formula for the state conditioned by an operation. -/
@[simp]
theorem condition_apply (op : Operation E) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω (op 1)) (x : E) :
    op.condition ω hmass x = (ω (op 1))⁻¹ * ω (op x) :=
  rfl

omit [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- A normalized operational conditional state preserves the order unit. -/
theorem condition_one (op : Operation E) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω (op 1)) :
    op.condition ω hmass 1 = 1 :=
  (op.condition ω hmass).map_one

omit [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- Conditioning a normal state by a normal operation preserves normality.  The unnormalized
functional is the composite of two normal positive maps; division by the strictly positive
outcome probability transports directed suprema through multiplication by a positive scalar. -/
theorem condition_isNormal (op : Operation E) (ω : 𝓢[ℝ, E]) (hmass : 0 < ω (op 1))
    (hop : op.IsNormal) (hω : ω.IsNormal) : (op.condition ω hmass).IsNormal := by
  intro D x hD hdir hLUB
  have hcomp : (ω.toPositiveLinearMap.comp op.1).IsNormal :=
    PositiveLinearMap.IsNormal.comp hop hω
  have hcompLUB := hcomp D x hD hdir hLUB
  change IsLUB ((fun y : E => ω (op y)) '' D) (ω (op x)) at hcompLUB
  have hscaled := hcompLUB.mul_left (inv_nonneg.mpr hmass.le)
  change IsLUB ((fun y : E => (ω (op 1))⁻¹ * ω (op y)) '' D)
    ((ω (op 1))⁻¹ * ω (op x))
  simpa only [Set.image_image] using hscaled

/-! ## B. Outcome effects -/

/-- The image of the certain event under an operation, as an effect: the probability of the
operation actually "firing" in a given state. -/
def outcomeEffect (op : Operation E) : Effect E :=
  ⟨op 1, op.map_nonneg IsOrderUnit.one_nonneg, op.apply_one_le_one⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
@[simp]
lemma coe_outcomeEffect (op : Operation E) : (outcomeEffect op : E) = op 1 := rfl

end Operation
