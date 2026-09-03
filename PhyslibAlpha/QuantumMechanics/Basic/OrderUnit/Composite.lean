/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import PhyslibAlpha.QuantumMechanics.Basic.OrderUnit.Basic

/-!

# Composite systems: the maximal cone on a tensor product of order-unit spaces

Nothing in `OrderUnit/Basic.lean` lets us talk about *two* systems together. Physically, putting
system `A` (order-unit space `E₁`) next to system `B` (order-unit space `E₂`) without letting them
interact should give a joint system whose underlying vector space is the ordinary algebraic tensor
product `E₁ ⊗[ℝ] E₂` — mathlib's `TensorProduct` already gives us that, unconditionally, with no
order structure attached to it at all. The physics is entirely in *which cone* of positive elements
we put on top of it: that choice is the joint system's genuine content, and there is more than one
reasonable candidate (this is the min/max tensor product ambiguity that
`OrderUnit/Channel/Basic.lean`'s "Future work" section already names as the reason complete
positivity cannot even be stated yet).

This file builds the most naive, and always-available, candidate: the **maximal cone**, generated
by declaring every simple tensor `x ⊗ₜ y` of two positive elements to be positive, and then closing
under addition (and hence under sums) to get an honest cone. Concretely `x ⊗ₜ y ≥ 0` should be read
as "prepare `A` in outcome `x` and, independently, `B` in outcome `y`" — a product experiment, which
is certainly a possible outcome of the joint system whichever proposed cone we use, so every
reasonable candidate cone contains this one; that is exactly what makes "maximal" the correct name,
and also what makes it possible to define with no extra hypotheses on `E₁`, `E₂` at all.

The type-level content mirrors `PosCone` on purpose: `PosCone E := {x : E // 0 ≤ x}` is `ℝ≥0`-module
because adding or nonnegatively rescaling possible outcomes keeps you among possible outcomes;
`MaxCone E₁ E₂` is the analogous subtype of `E₁ ⊗[ℝ] E₂`, and it is a `ℝ≥0`-module for the same
reason, proved here from scratch since `E₁ ⊗[ℝ] E₂` carries no order of its own for `PosCone`'s
own machinery to reuse.

`MaxCone.tmulRight` records the basic compatibility fact that earns this the name "cone of a
composite system": tensoring a fixed positive `y₀ : E₂` onto positive elements of `E₁` is itself a
positive (indeed `ℝ≥0`-linear) map into the joint cone — the algebraic shadow of "preparing `B` in a
fixed state doesn't stop `A`'s statistics from being genuine statistics."

## Main definitions

- `maxConeGen E₁ E₂` : the generating set, simple tensors `x ⊗ₜ y` with `0 ≤ x`, `0 ≤ y`.
- `maxConeSet E₁ E₂` : the `AddSubmonoid` of `E₁ ⊗[ℝ] E₂` it generates — finite sums of such
  simple tensors, i.e. the maximal cone as a subset.
- `MaxCone E₁ E₂` : the maximal cone as a type, with its `AddCommMonoid` and `Module ℝ≥0`
  structure, in the same shape as `PosCone`.
- `MaxCone.tmulRight` : for fixed `0 ≤ y₀`, the `ℝ≥0`-linear positive map
  `PosCone E₁ →ₗ[ℝ≥0] MaxCone E₁ E₂`, `x ↦ x ⊗ₜ y₀`.

## Future work

- **The order unit.** Whether `1 ⊗ₜ 1` dominates every element of `MaxCone E₁ E₂` — the fact that
  would make this an honest `IsOrderUnit`-carrying order-unit space — is not established here, even
  restricting to `E₁`, `E₂` finite-dimensional. The obstruction is real, not just a missing lemma:
  a general order-unit space need not be a vector lattice, so an arbitrary `t : E₁ ⊗[ℝ] E₂` need
  only be *some* finite sum `∑ xᵢ ⊗ₜ yᵢ` with no control over the sign of the individual `xᵢ`, `yᵢ`
  — there is no Jordan-type decomposition of `t` into a difference of two elements of `MaxCone E₁
  E₂` to fall back on, unlike the C*-algebra/matrix setting where `M_n(ℂ)`'s extra structure
  (self-adjointness, the C*-identity) gives exactly such control. Bounding `t` by a multiple of
  `1 ⊗ₜ 1` genuinely needs more than the order-unit axioms this file assumes; the natural place to
  look is a Cauchy–Schwarz-type argument once `E₁`, `E₂` carry more structure than a bare order
  unit (e.g. once each `Eᵢ` is realized as self-adjoint elements of a C*-algebra, where the minimal
  tensor product's operator norm gives exactly this bound). Left open.
- **The minimal (spatial) cone and the gap between the two.** This file only builds the maximal
  cone. The minimal cone (functionals on both factors that are jointly positive) is the other
  extreme, and ordinary quantum mechanics needs the one strictly in between the two (matching
  positive-semidefinite matrices) — none of that is attempted here.
- **Complete positivity.** With `MaxCone` in hand, a channel `φ : E₂ →ₚ₁[ℝ] E₁` could in principle
  be asked whether `id ⊗ φ` (suitably defined) is positive on `MaxCone E₃ E₂ → MaxCone E₃ E₁` for
  a bystander system `E₃` — the actual statement of complete positivity `OrderUnit/Channel/Basic.
  lean` gestures at. Not built here: it needs `id ⊗ φ` as a genuine linear map on the tensor
  product first (routine from mathlib's `TensorProduct.map`), and then a positivity proof, which is
  not automatic even once `id ⊗ φ` exists as a linear map.

-/

@[expose] public section

open scoped NNReal TensorProduct

variable (E₁ E₂ : Type*)
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁] [Module ℝ E₁] [PosSMulMono ℝ E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂] [Module ℝ E₂] [PosSMulMono ℝ E₂]

/-- The generators of the maximal cone: simple tensors of positive elements, read as "prepare `A`
in outcome `x` and `B` in outcome `y`, independently" — certainly a possible outcome of the joint
system. -/
def maxConeGen : Set (E₁ ⊗[ℝ] E₂) :=
  {t | ∃ x : E₁, ∃ y : E₂, 0 ≤ x ∧ 0 ≤ y ∧ t = x ⊗ₜ[ℝ] y}

/-- The maximal cone on `E₁ ⊗[ℝ] E₂`, as a subset closed under addition: finite sums of simple
tensors of positive elements. This is the "generated additively by simple tensors" cone from the
docstring above, in `AddSubmonoid` form so that closure under addition is automatic. -/
def maxConeSet : AddSubmonoid (E₁ ⊗[ℝ] E₂) := AddSubmonoid.closure (maxConeGen E₁ E₂)

variable {E₁ E₂}

omit [IsOrderedAddMonoid E₁] [PosSMulMono ℝ E₁] [IsOrderedAddMonoid E₂] [PosSMulMono ℝ E₂] in
/-- A simple tensor of positive elements lies in the maximal cone. -/
lemma tmul_mem_maxConeSet {x : E₁} {y : E₂} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ⊗ₜ[ℝ] y ∈ maxConeSet E₁ E₂ :=
  AddSubmonoid.subset_closure ⟨x, y, hx, hy, rfl⟩

omit [IsOrderedAddMonoid E₁] [IsOrderedAddMonoid E₂] [PosSMulMono ℝ E₂] in
/-- The maximal cone is closed under scaling by a nonnegative real: together with `maxConeSet`
already being closed under addition (it is an `AddSubmonoid`), this is exactly what it takes for
`maxConeSet E₁ E₂` to be a genuine cone in the sense `PosCone` is. -/
lemma maxConeSet_nnsmul_mem {c : ℝ≥0} {t : E₁ ⊗[ℝ] E₂} (ht : t ∈ maxConeSet E₁ E₂) :
    (c : ℝ) • t ∈ maxConeSet E₁ E₂ := by
  induction ht using AddSubmonoid.closure_induction with
  | mem t ht =>
    obtain ⟨x, y, hx, hy, rfl⟩ := ht
    rw [TensorProduct.smul_tmul']
    exact tmul_mem_maxConeSet (smul_nonneg c.2 hx) hy
  | zero => simp
  | add t₁ t₂ _ _ h₁ h₂ => rw [smul_add]; exact AddSubmonoid.add_mem _ h₁ h₂

variable (E₁ E₂)

/-- The maximal cone on `E₁ ⊗[ℝ] E₂`, as a type — the composite-system analogue of `PosCone`. -/
abbrev MaxCone : Type _ := maxConeSet E₁ E₂

namespace MaxCone

/-- Scaling an element of the maximal cone by a nonnegative real keeps it in the maximal cone, and
does so compatibly with addition to make `MaxCone E₁ E₂` a `ℝ≥0`-module — the exact analogue of
`PosCone.instModule`. -/
instance instModule : Module ℝ≥0 (MaxCone E₁ E₂) where
  smul c x := ⟨(c : ℝ) • (x : E₁ ⊗[ℝ] E₂), maxConeSet_nnsmul_mem x.2⟩
  one_smul _ := Subtype.ext (one_smul ℝ _)
  mul_smul c d _ := Subtype.ext (mul_smul (c : ℝ) (d : ℝ) _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add c _ _ := Subtype.ext (smul_add (c : ℝ) _ _)
  add_smul c d _ := Subtype.ext (by push_cast; exact add_smul (c : ℝ) (d : ℝ) _)
  zero_smul _ := Subtype.ext (by push_cast; exact zero_smul ℝ _)

omit [IsOrderedAddMonoid E₁] [IsOrderedAddMonoid E₂] [PosSMulMono ℝ E₂] in
@[simp, norm_cast]
lemma coe_smul (c : ℝ≥0) (x : MaxCone E₁ E₂) :
    ((c • x : MaxCone E₁ E₂) : E₁ ⊗[ℝ] E₂) = (c : ℝ) • (x : E₁ ⊗[ℝ] E₂) := rfl

omit [IsOrderedAddMonoid E₁] [IsOrderedAddMonoid E₂] [PosSMulMono ℝ E₂] in
@[simp]
lemma mk_smul (c : ℝ≥0) {t : E₁ ⊗[ℝ] E₂} (ht : t ∈ maxConeSet E₁ E₂) :
    c • (⟨t, ht⟩ : MaxCone E₁ E₂) = ⟨(c : ℝ) • t, maxConeSet_nnsmul_mem ht⟩ := rfl

variable {E₁ E₂}

/-- For fixed `0 ≤ y₀ : E₂`, tensoring on the right with `y₀` sends possible outcomes of `A` to
possible outcomes of the joint system, `ℝ≥0`-linearly: preparing `B` in the fixed outcome `y₀`
doesn't disturb `A`'s status as a genuine sub-system. This is the basic "partial trace"-flavored
compatibility fact that makes `MaxCone` deserve the name "positive cone of a composite system." -/
def tmulRight {y₀ : E₂} (hy₀ : 0 ≤ y₀) : PosCone E₁ →ₗ[ℝ≥0] MaxCone E₁ E₂ where
  toFun x := ⟨(x : E₁) ⊗ₜ[ℝ] y₀, tmul_mem_maxConeSet x.2 hy₀⟩
  map_add' x y := by
    refine Subtype.ext ?_
    show ((x : E₁) + (y : E₁)) ⊗ₜ[ℝ] y₀ = (x : E₁) ⊗ₜ[ℝ] y₀ + (y : E₁) ⊗ₜ[ℝ] y₀
    exact TensorProduct.add_tmul _ _ _
  map_smul' c x := by
    refine Subtype.ext ?_
    show ((c : ℝ) • (x : E₁)) ⊗ₜ[ℝ] y₀ = (c : ℝ) • ((x : E₁) ⊗ₜ[ℝ] y₀)
    exact (TensorProduct.smul_tmul' (c : ℝ) (x : E₁) y₀).symm

omit [IsOrderedAddMonoid E₂] [PosSMulMono ℝ E₂] in
@[simp]
lemma tmulRight_apply {y₀ : E₂} (hy₀ : 0 ≤ y₀) (x : PosCone E₁) :
    (tmulRight hy₀ x : E₁ ⊗[ℝ] E₂) = (x : E₁) ⊗ₜ[ℝ] y₀ := rfl

/-- Same as `tmulRight` with the roles of `E₁`, `E₂` swapped: tensoring a fixed positive `x₀ : E₁`
on the left sends possible outcomes of `B` to possible outcomes of the joint system. -/
def tmulLeft {x₀ : E₁} (hx₀ : 0 ≤ x₀) : PosCone E₂ →ₗ[ℝ≥0] MaxCone E₁ E₂ where
  toFun y := ⟨x₀ ⊗ₜ[ℝ] (y : E₂), tmul_mem_maxConeSet hx₀ y.2⟩
  map_add' x y := by
    refine Subtype.ext ?_
    show x₀ ⊗ₜ[ℝ] ((x : E₂) + (y : E₂)) = x₀ ⊗ₜ[ℝ] (x : E₂) + x₀ ⊗ₜ[ℝ] (y : E₂)
    exact TensorProduct.tmul_add _ _ _
  map_smul' c y := by
    refine Subtype.ext ?_
    show x₀ ⊗ₜ[ℝ] ((c : ℝ) • (y : E₂)) = (c : ℝ) • (x₀ ⊗ₜ[ℝ] (y : E₂))
    exact TensorProduct.tmul_smul _ _ _

omit [IsOrderedAddMonoid E₁] in
@[simp]
lemma tmulLeft_apply {x₀ : E₁} (hx₀ : 0 ≤ x₀) (y : PosCone E₂) :
    (tmulLeft hx₀ y : E₁ ⊗[ℝ] E₂) = x₀ ⊗ₜ[ℝ] (y : E₂) := rfl

end MaxCone
