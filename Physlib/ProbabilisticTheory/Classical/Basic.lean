/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.ForMathlib.LpStarOrder
public import Physlib.ProbabilisticTheory.CStarAlgebra.Basic
public import Physlib.ProbabilisticTheory.Effect.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

/-!
# Classical probabilistic theories

In a classical system every observable has a definite value in each configuration.

## i. Overview

An observable of a classical system with configurations `X` is a bounded real function on `X`.
A closed algebra `S` of bounded functions fixes which functions count as observables. On a
measurable space these are the bounded measurable functions, which give the theory
`measurable X`.

The observables in `S` form the probabilistic theory `classical S`. Observables add, multiply and
compare value by value. Their algebra is commutative, which is characteristic of classical
systems.

## ii. Key results

- `ProbabilisticTheory.classical` : the classical theory of a closed algebra of bounded functions.
- `ProbabilisticTheory.Classical.instFunLike` : the value of an observable in a configuration.
- `ProbabilisticTheory.Classical.le_def` : observables are ordered by their values.
- `ProbabilisticTheory.Classical.mem_effect_iff` : effects are observables with values between `0`
  and `1`.
- `ProbabilisticTheory.Classical.measurable` : the classical theory of bounded measurable
  observables.
- `ProbabilisticTheory.Classical.Event` : the events, measurable sets of configurations.
- `ProbabilisticTheory.Classical.isLUB_range_apply` : the least upper bound of a sequence of
  observables is their pointwise supremum.

## iii. Table of contents

- A. The classical theory
- B. Values of observables
- C. The measurable classical theory

## iv. References

-/

@[expose] public section

open Set
open scoped ENNReal ComplexOrder

namespace ProbabilisticTheory

/-! ## A. The classical theory -/

/-- The classical theory whose observables are the real functions in a closed algebra `S` of
bounded functions. -/
noncomputable def classical {X : Type*} (S : StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞))
    [IsClosed (S : Set (lp (fun _ : X ↦ ℂ) ∞))] : ProbabilisticTheory :=
  ofCStarAlgebra S

end ProbabilisticTheory

namespace ProbabilisticTheory.Classical

variable {X : Type*} {S : StarSubalgebra ℂ (lp (fun _ : X ↦ ℂ) ∞)}
  [IsClosed (S : Set (lp (fun _ : X ↦ ℂ) ∞))]

/-! ## B. Values of observables -/

/-- An observable as a real function in `S`. -/
def toSelfAdjoint : Observables (classical S) ≃ selfAdjoint S :=
  Equiv.refl _

/-- Observables multiply value by value. -/
noncomputable instance : CommRing (Observables (classical S)) :=
  let R : CommRing (selfAdjoint S) := inferInstance
  { R with
    toAddCommGroup := (classical S).addCommGroup
    toOne := (classical S).one }

/-- The value of an observable in a configuration. -/
noncomputable instance instFunLike : FunLike (Observables (classical S)) X ℝ where
  coe f x := (((toSelfAdjoint f).1 : lp (fun _ : X ↦ ℂ) ∞) x).re
  coe_injective f g h := toSelfAdjoint.injective <| Subtype.ext <| Subtype.ext <| lp.ext <|
    funext fun x ↦ by
      have re (f : Observables (classical S)) := Complex.conj_eq_iff_re.mp
        (congrFun (congrArg (⇑) (congrArg Subtype.val (toSelfAdjoint f).2)) x)
      rw [← re f, ← re g]; exact congrArg Complex.ofReal (congrFun h x)

/-- The function of an observable takes real values. -/
lemma ofReal_apply (f : Observables (classical S)) (x : X) :
    (f x : ℂ) = ((toSelfAdjoint f).1 : lp (fun _ : X ↦ ℂ) ∞) x :=
  Complex.conj_eq_iff_re.mp (congrFun (congrArg (⇑) (congrArg Subtype.val (toSelfAdjoint f).2)) x)

@[simp] lemma zero_apply (x : X) : (0 : Observables (classical S)) x = 0 := rfl

@[simp] lemma one_apply (x : X) : (1 : Observables (classical S)) x = 1 := rfl

@[simp] lemma add_apply (f g : Observables (classical S)) (x : X) : (f + g) x = f x + g x := rfl

@[simp] lemma sub_apply (f g : Observables (classical S)) (x : X) : (f - g) x = f x - g x := rfl

/-- The sum of observables adds their values. -/
@[simp] lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → Observables (classical S))
    (x : X) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

@[simp] lemma smul_apply (c : ℝ) (f : Observables (classical S)) (x : X) :
    (c • f) x = c * f x :=
  Complex.re_ofReal_mul _ _

/-- The product of two observables multiplies their values. -/
@[simp] lemma mul_apply (f g : Observables (classical S)) (x : X) : (f * g) x = f x * g x :=
  Complex.ofReal_injective <| by
    rw [Complex.ofReal_mul, ofReal_apply, ofReal_apply, ofReal_apply]; rfl

@[simp] lemma pow_apply (f : Observables (classical S)) (n : ℕ) (x : X) :
    (f ^ n) x = f x ^ n := by
  induction n <;> simp [pow_succ, *]

/-- Observables are ordered by their values. -/
lemma le_def {f g : Observables (classical S)} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  forall_congr' fun x ↦ by rw [← Complex.real_le_real, ofReal_apply, ofReal_apply]; rfl

/-- The effects of a classical theory are the observables with values between `0` and `1`. -/
lemma mem_effect_iff {f : Observables (classical S)} :
    f ∈ Effect (classical S) ↔ ∀ x, f x ∈ Icc 0 1 := by
  simp [Effect, le_def, forall_and]

/-- The square of an observable is positive. -/
lemma sq_nonneg' (f : Observables (classical S)) : 0 ≤ f ^ 2 :=
  le_def.mpr fun x ↦ by simpa using sq_nonneg (f x)

/-! ## C. The measurable classical theory -/

/-- The classical theory whose observables are the bounded measurable functions of the
configuration. -/
noncomputable abbrev measurable (X : Type*) [MeasurableSpace X] : ProbabilisticTheory :=
  classical (lp.measurableSubalgebra X)

/-- An event is a measurable set of configurations. -/
abbrev Event (X : Type*) [MeasurableSpace X] : Type _ := {s : Set X // MeasurableSet s}

variable [MeasurableSpace X]

/-- The value of an observable depends measurably on the configuration. -/
lemma measurable_coe (f : Observables (measurable X)) : Measurable f :=
  RCLike.measurable_re.comp (toSelfAdjoint f).1.2

/-- The values of an observable are bounded. -/
lemma exists_abs_le (f : Observables (measurable X)) : ∃ C, ∀ x, |f x| ≤ C :=
  ⟨_, fun x ↦ (Complex.abs_re_le_norm _).trans
    (lp.norm_apply_le_norm ENNReal.top_ne_zero (toSelfAdjoint f).1.1 x)⟩

/-- A bounded measurable real function as an observable. -/
noncomputable def ofFun (f : X → ℝ) (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C) :
    Observables (measurable X) :=
  toSelfAdjoint.symm ⟨⟨⟨Complex.ofReal ∘ f, memℓp_infty (hb.imp fun _ hC ↦ by
      rintro _ ⟨x, rfl⟩
      simpa using hC x)⟩, RCLike.measurable_ofReal.comp hf⟩,
    Subtype.ext (lp.ext (funext fun x ↦ Complex.conj_ofReal (f x)))⟩

@[simp] lemma coe_ofFun (f : X → ℝ) (hf : Measurable f) (hb) : ⇑(ofFun f hf hb) = f := rfl

/-- The pointwise supremum of a sequence of observables bounded above is again an observable. -/
lemma exists_isLUB_range_apply {f : ℕ → Observables (measurable X)} {g : Observables (measurable X)}
    (hfg : ∀ n, f n ≤ g) : ∃ s : Observables (measurable X), ∀ x, IsLUB (range (f · x)) (s x) := by
  obtain ⟨C₀, h₀⟩ := exists_abs_le (f 0)
  obtain ⟨C₁, h₁⟩ := exists_abs_le g
  have hb x : BddAbove (range (f · x)) := ⟨g x, forall_mem_range.mpr fun n ↦ le_def.mp (hfg n) x⟩
  refine ⟨ofFun _ (.iSup fun n ↦ measurable_coe (f n)) ⟨max C₀ C₁, fun x ↦ ?_⟩,
    fun x ↦ isLUB_ciSup (hb x)⟩
  exact (abs_le_max_abs_abs (le_ciSup (hb x) 0) (ciSup_le fun n ↦ le_def.mp (hfg n) x)).trans
    (max_le_max (h₀ x) (h₁ x))

/-- The pointwise supremum of a sequence of observables is their least upper bound. -/
lemma isLUB_range_of_apply {f : ℕ → Observables (measurable X)} {g : Observables (measurable X)}
    (h : ∀ x, IsLUB (range (f · x)) (g x)) : IsLUB (range f) g :=
  ⟨forall_mem_range.mpr fun n ↦ le_def.mpr fun x ↦ (h x).1 ⟨n, rfl⟩,
    fun _ hu ↦ le_def.mpr fun x ↦ (h x).2 (forall_mem_range.mpr fun n ↦ le_def.mp (hu ⟨n, rfl⟩) x)⟩

/-- The least upper bound of a sequence of observables is their pointwise supremum. -/
lemma isLUB_range_apply {f : ℕ → Observables (measurable X)} {g : Observables (measurable X)}
    (h : IsLUB (range f) g) (x : X) : IsLUB (range (f · x)) (g x) := by
  obtain ⟨s, hs⟩ := exists_isLUB_range_apply fun n ↦ h.1 ⟨n, rfl⟩
  exact h.unique (isLUB_range_of_apply hs) ▸ hs x

end ProbabilisticTheory.Classical
