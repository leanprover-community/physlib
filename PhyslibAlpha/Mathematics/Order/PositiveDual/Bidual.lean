/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.PositiveDual.Basic
public import PhyslibAlpha.Mathematics.Analysis.RealBounds
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Algebra.Module.Pi

/-!
# The bidual

The bidual of an ordered vector space via positive functionals, and its monotone completeness.

## i. Overview

An element of an ordered real vector space `E` assigns to every positive functional its value,
additively and positively homogeneously, and dominated by the values of some element of `E`. The
bidual consists of all such assignments. It contains `E` when the order is directed, and is
ordered by comparing values on every positive functional. Positive functionals extend to the
bidual by evaluation.

The bidual is monotone complete: a bounded upward directed family of elements has a least upper
bound, their pointwise supremum.

## ii. Key results

- `Bidual E` : the bidual of `E`.
- `Bidual.ofE` : an element of `E` as an element of the bidual.
- `Bidual.eval` : a positive functional extended to the bidual.
- `Bidual.isLUB_ciSup` : a bounded directed family in the bidual has its pointwise supremum as
  least upper bound.

## iii. Table of contents

- A. The bidual
- B. Order
- C. Elements and positive functionals
- D. Monotone completeness

## iv. References

* None.

-/

@[expose] public section

open scoped NNReal

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]

/-! ## A. The bidual -/

variable (E) in
/-- Functions on positive functionals that are additive, positively homogeneous, and dominated by
an element of `E`. -/
def bidualSubmodule : Submodule ℝ ((E →ₚ[ℝ] ℝ) → ℝ) where
  carrier := {x | (∀ φ ψ, x (φ + ψ) = x φ + x ψ) ∧ (∀ (c : ℝ≥0) φ, x (c • φ) = c * x φ) ∧
    ∃ f : E, ∀ φ, |x φ| ≤ φ f}
  add_mem' := by
    rintro x y ⟨hx₁, hx₂, f, hf⟩ ⟨hy₁, hy₂, g, hg⟩
    refine ⟨fun φ ψ => ?_, fun c φ => ?_, f + g, fun φ => ?_⟩
    · simp only [Pi.add_apply, hx₁, hy₁]; ring
    · simp only [Pi.add_apply, hx₂, hy₂]; ring
    · simp only [Pi.add_apply, map_add]
      exact (abs_add_le _ _).trans (add_le_add (hf φ) (hg φ))
  zero_mem' := ⟨by simp, by simp, 0, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx₁, hx₂, f, hf⟩
    refine ⟨fun φ ψ => ?_, fun d φ => ?_, |c| • f, fun φ => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hx₁]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hx₂]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, map_smul]
      exact mul_le_mul_of_nonneg_left (hf φ) (abs_nonneg c)

variable (E) in
/-- The bidual of `E`. -/
def Bidual : Type _ := bidualSubmodule E

namespace Bidual

instance : AddCommGroup (Bidual E) := inferInstanceAs (AddCommGroup (bidualSubmodule E))

instance : Module ℝ (Bidual E) := inferInstanceAs (Module ℝ (bidualSubmodule E))

/-- The element of the bidual given by an additive, positively homogeneous, bounded function. -/
def mk (x : (E →ₚ[ℝ] ℝ) → ℝ) (h₁ : ∀ φ ψ, x (φ + ψ) = x φ + x ψ)
    (h₂ : ∀ (c : ℝ≥0) φ, x (c • φ) = c * x φ) (h₃ : ∃ f : E, ∀ φ, |x φ| ≤ φ f) :
    Bidual E :=
  (⟨x, h₁, h₂, h₃⟩ : bidualSubmodule E)

/-- An element of the bidual as an element of the submodule. -/
def toSub (x : Bidual E) : bidualSubmodule E := x

instance : CoeFun (Bidual E) fun _ => (E →ₚ[ℝ] ℝ) → ℝ := ⟨fun x => x.toSub.1⟩

@[simp] lemma mk_apply (x : (E →ₚ[ℝ] ℝ) → ℝ) (h₁ h₂ h₃) (φ : E →ₚ[ℝ] ℝ) :
    mk x h₁ h₂ h₃ φ = x φ := rfl

@[ext]
lemma ext {x y : Bidual E} (h : ∀ φ, x φ = y φ) : x = y :=
  Subtype.ext (funext h)

lemma map_add (x : Bidual E) (φ ψ : E →ₚ[ℝ] ℝ) : x (φ + ψ) = x φ + x ψ :=
  x.toSub.2.1 φ ψ

lemma map_nnsmul (x : Bidual E) (c : ℝ≥0) (φ : E →ₚ[ℝ] ℝ) : x (c • φ) = c * x φ :=
  x.toSub.2.2.1 c φ

lemma exists_bound (x : Bidual E) : ∃ f : E, ∀ φ, |x φ| ≤ φ f :=
  x.toSub.2.2.2

/-- A dominating element has nonnegative values on positive functionals. -/
lemma apply_nonneg_of_bound {x : Bidual E} {f : E} (hf : ∀ φ, |x φ| ≤ φ f)
    (φ : E →ₚ[ℝ] ℝ) : 0 ≤ φ f :=
  (abs_nonneg _).trans (hf φ)

@[simp] lemma coe_add (x y : Bidual E) (φ : E →ₚ[ℝ] ℝ) : (x + y) φ = x φ + y φ := rfl
@[simp] lemma coe_sub (x y : Bidual E) (φ : E →ₚ[ℝ] ℝ) : (x - y) φ = x φ - y φ := rfl
@[simp] lemma coe_neg (x : Bidual E) (φ : E →ₚ[ℝ] ℝ) : (-x) φ = -x φ := rfl
@[simp] lemma coe_zero (φ : E →ₚ[ℝ] ℝ) : (0 : Bidual E) φ = 0 := rfl
@[simp] lemma coe_smul (c : ℝ) (x : Bidual E) (φ : E →ₚ[ℝ] ℝ) : (c • x) φ = c * x φ := rfl

lemma map_zero (x : Bidual E) : x 0 = 0 := by
  have := x.map_add 0 0
  rw [zero_add] at this
  linarith

lemma map_sum {ι : Type*} (x : Bidual E) (s : Finset ι) (φ : ι → E →ₚ[ℝ] ℝ) :
    x (∑ i ∈ s, φ i) = ∑ i ∈ s, x (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using x.map_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, x.map_add, ih, Finset.sum_insert hi]

/-! ## B. Order -/

/-- An element of the bidual is nonnegative when it is nonnegative on every positive functional. -/
instance : PartialOrder (Bidual E) :=
  PartialOrder.lift (fun x : Bidual E => (x : (E →ₚ[ℝ] ℝ) → ℝ)) fun _ _ h => ext (congrFun h)

lemma le_def {x y : Bidual E} : x ≤ y ↔ ∀ φ, x φ ≤ y φ :=
  Iff.rfl

instance : IsOrderedAddMonoid (Bidual E) where
  add_le_add_left _ _ h z φ := by simpa using add_le_add_right (h φ) (z φ)

instance : PosSMulMono ℝ (Bidual E) :=
  ⟨fun _ hc _ _ h φ => by simpa using mul_le_mul_of_nonneg_left (h φ) hc⟩

/-! ## C. Elements and positive functionals -/

section Directed

variable [IsDirectedOrder E]

/-- An element of `E` as an element of the bidual: its value on each positive functional. -/
def ofE : E →ₗ[ℝ] Bidual E where
  toFun A := mk (fun φ => φ A) (fun _ _ => rfl) (fun _ _ => rfl) (by
    obtain ⟨f, hAf, hAf'⟩ := exists_ge_ge A (-A)
    refine ⟨f, fun φ => abs_le.2 ⟨?_, OrderHomClass.mono φ hAf⟩⟩
    have := OrderHomClass.mono φ hAf'
    rw [map_neg] at this
    linarith)
  map_add' _ _ := ext fun φ => _root_.map_add φ _ _
  map_smul' _ _ := ext fun φ => _root_.map_smul φ _ _

@[simp] lemma ofE_apply (A : E) (φ : E →ₚ[ℝ] ℝ) : ofE A φ = φ A := rfl

lemma ofE_mono {A B : E} (h : A ≤ B) : ofE A ≤ ofE B := fun φ => φ.monotone' h

/-- The bidual of a directed space is directed: `ofE (f + g)` lies above `x` and `y` when `f`
dominates `x` and `g` dominates `y`. -/
instance : IsDirectedOrder (Bidual E) :=
  ⟨fun x y => by
    obtain ⟨f, hf⟩ := x.exists_bound
    obtain ⟨g, hg⟩ := y.exists_bound
    refine ⟨ofE (f + g), fun φ => ?_, fun φ => ?_⟩
    · have := apply_nonneg_of_bound hg φ
      change x φ ≤ φ (f + g)
      rw [_root_.map_add]; linarith [le_abs_self (x φ), hf φ]
    · have := apply_nonneg_of_bound hf φ
      change y φ ≤ φ (f + g)
      rw [_root_.map_add]; linarith [le_abs_self (y φ), hg φ]⟩

/-- A positive functional extended to the bidual by evaluation. -/
def eval (φ : E →ₚ[ℝ] ℝ) : Bidual E →ₚ[ℝ] ℝ :=
  .mk₀ { toFun x := x φ, map_add' _ _ := rfl, map_smul' _ _ := rfl } fun _ hx => hx φ

omit [IsDirectedOrder E] in
@[simp] lemma eval_apply (φ : E →ₚ[ℝ] ℝ) (x : Bidual E) : eval φ x = x φ := rfl

@[simp] lemma eval_ofE (φ : E →ₚ[ℝ] ℝ) (A : E) : eval φ (ofE A) = φ A := rfl

/-- Extension to the bidual preserves the order of positive functionals. -/
lemma eval_mono {φ ψ : E →ₚ[ℝ] ℝ} (h : φ ≤ ψ) : eval φ ≤ eval ψ := fun x hx => by
  rw [eval_apply, eval_apply, ← PositiveLinearMap.add_subOfLE ψ φ h, x.map_add]
  exact le_add_of_nonneg_right (hx _)

end Directed

/-! ## D. Monotone completeness -/

section Directed

variable {ι : Type*} [Nonempty ι] {x : ι → Bidual E} (hx : Directed (· ≤ ·) x) {b : Bidual E}
  (hb : ∀ i, x i ≤ b)
include hx hb

omit [Nonempty ι] hx in
lemma bddAbove_apply (φ : E →ₚ[ℝ] ℝ) : BddAbove (Set.range fun i => x i φ) :=
  ⟨b φ, Set.forall_mem_range.2 fun i => hb i φ⟩

/-- The pointwise supremum of a bounded directed family. -/
noncomputable def ciSup : Bidual E :=
  mk (fun φ => ⨆ i, x i φ) (fun φ ψ => by
    simp only [map_add]
    exact Real.ciSup_add (bddAbove_apply hb φ) (bddAbove_apply hb ψ) fun i j =>
      (hx i j).imp fun _ h => ⟨h.1 φ, h.2 ψ⟩)
    (fun c φ => by
    simp only [map_nnsmul]
    exact (Real.mul_iSup_of_nonneg c.2 _).symm) (by
    obtain ⟨f, hf⟩ := b.exists_bound
    obtain ⟨g, hg⟩ := (x (Classical.arbitrary ι)).exists_bound
    refine ⟨f + g, fun φ => abs_le.2 ⟨?_, ?_⟩⟩
    · have := (abs_le.1 (hg φ)).1
      have h := apply_nonneg_of_bound hf φ
      refine le_trans ?_ (le_ciSup (bddAbove_apply hb φ) (Classical.arbitrary ι))
      rw [_root_.map_add]; linarith
    · have := (abs_le.1 (hf φ)).2
      have h := apply_nonneg_of_bound hg φ
      refine (ciSup_le fun i => hb i φ).trans ?_
      rw [_root_.map_add]; linarith)

@[simp] lemma ciSup_apply (φ : E →ₚ[ℝ] ℝ) : ciSup hx hb φ = ⨆ i, x i φ := rfl

/-- **Monotone completeness**: a bounded directed family in the bidual has its pointwise supremum
as least upper bound. -/
lemma isLUB_ciSup : IsLUB (Set.range x) (ciSup hx hb) :=
  ⟨Set.forall_mem_range.2 fun i φ => le_ciSup (bddAbove_apply hb φ) i,
    fun _ hy φ => ciSup_le fun i => hy ⟨i, rfl⟩ φ⟩

end Directed

end Bidual
