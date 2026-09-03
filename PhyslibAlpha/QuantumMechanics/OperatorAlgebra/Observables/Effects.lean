/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.Observables.Positive
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Effects

Effects are observables whose possible values lie between `0` and `1`. They describe individual
outcomes of general quantum measurements.
-/

@[expose] public section
namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A quantum effect: an observable between `0` and `1`. -/
abbrev Effect (A : Type*) [OperatorAlgebra A] := Set.Icc (0 : Observable A) 1

namespace Observable

/-! ## A. Spectral characterization -/

/-- An observable is an effect exactly when its spectrum lies in `[0, 1]`. -/
lemma mem_effect_iff_spectrum_subset (a : Observable A) :
    a ∈ Set.Icc (0 : Observable A) 1 ↔
      spectrum ℝ (a : A) ⊆ Set.Icc 0 1 := by
  constructor
  · rintro ⟨ha₀, ha₁⟩ x hx
    exact ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a : A) a.property).mp
        ha₀ x hx,
      (CFC.le_one_iff (R := ℝ) (a : A) a.property).mp ha₁ x hx⟩
  · intro ha
    exact ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (a : A) a.property).mpr
        fun x hx => (ha hx).1,
      (CFC.le_one_iff (R := ℝ) (a : A) a.property).mpr fun x hx => (ha hx).2⟩

end Observable

namespace Effect

/-! ## B. Constructors and complement -/

/-- A continuous `[0,1]`-valued function of an observable is an effect. -/
noncomputable def ofFunctionalCalculus (f : C(ℝ, ℝ)) (a : Observable A)
    (hf : Set.MapsTo f (spectrum ℝ (a : A)) (Set.Icc 0 1)) : Effect A := by
  let b : Observable A := ⟨cfc f (a : A), cfc_predicate f (a : A)⟩
  refine ⟨b, ?_, ?_⟩
  · change 0 ≤ cfc (f : ℝ → ℝ) (a : A)
    exact (cfc_nonneg_iff (p := IsSelfAdjoint) (f : ℝ → ℝ) (a : A)
      f.continuous.continuousOn a.property).mpr fun _ hx => (hf hx).1
  · change cfc (f : ℝ → ℝ) (a : A) ≤ 1
    exact (cfc_le_one_iff (p := IsSelfAdjoint) (f : ℝ → ℝ) (a : A)
      f.continuous.continuousOn a.property).mpr fun _ hx => (hf hx).2

/-- The complementary effect `1 - E`. -/
noncomputable def complement (E : Effect A) : Effect A :=
  ⟨1 - E.1, sub_nonneg.mpr E.2.2,
    sub_le_self 1 (show (0 : Observable A) ≤ E.1 from E.2.1)⟩

/-- Taking the complement twice returns the original effect. -/
@[simp]
lemma complement_complement (E : Effect A) : complement (complement E) = E := by
  apply Subtype.ext
  simp [complement]

/-! ## C. Relation to positive observables -/

/-- An effect is, in particular, a positive observable: `PositiveObservable` only asks `0 ≤ a`,
which an effect already gives, and simply forgets the extra upper bound `a ≤ 1`. -/
def toPositiveObservable (E : Effect A) : PositiveObservable A := ⟨E.1, E.2.1⟩

@[simp]
lemma coe_toPositiveObservable (E : Effect A) :
    (toPositiveObservable E : Observable A) = E.1 := rfl

end Effect

namespace PositiveObservable

/-- Every positive observable rescales into an effect: `a` is bounded by `‖a‖ • 1`
(`IsSelfAdjoint.le_algebraMap_norm_self`), so dividing by its norm brings it into `[0, 1]`.
`Effect A` is exactly the positive observables already bounded by `1`; this is the general
positive observable's way back in, and `Effect.toPositiveObservable` composed with this need not
recover `a` itself — only a rescaled copy of it. -/
noncomputable def toEffect (a : PositiveObservable A) : Effect A := by
  refine ⟨‖(a.1 : A)‖⁻¹ • a.1, ?_, ?_⟩
  · show (0 : A) ≤ ((‖(a.1 : A)‖⁻¹ • a.1 : Observable A) : A)
    rw [selfAdjoint.val_smul]
    exact smul_nonneg (inv_nonneg.mpr (norm_nonneg _)) a.2
  · show ((‖(a.1 : A)‖⁻¹ • a.1 : Observable A) : A) ≤ (1 : A)
    rw [selfAdjoint.val_smul]
    rcases eq_or_ne (a.1 : A) 0 with h0 | h0
    · simp [h0]
    · have hnorm : (0 : ℝ) < ‖(a.1 : A)‖ := norm_pos_iff.mpr h0
      have hbound : (a.1 : A) ≤ ‖(a.1 : A)‖ • (1 : A) := by
        have := IsSelfAdjoint.le_algebraMap_norm_self (a := (a.1 : A)) a.1.property
        rwa [Algebra.algebraMap_eq_smul_one] at this
      have hscaled : ‖(a.1 : A)‖⁻¹ • (a.1 : A) ≤ ‖(a.1 : A)‖⁻¹ • (‖(a.1 : A)‖ • (1 : A)) :=
        smul_le_smul_of_nonneg_left hbound (inv_nonneg.mpr hnorm.le)
      rwa [smul_smul, inv_mul_cancel₀ hnorm.ne', one_smul] at hscaled

end PositiveObservable

end OperatorAlgebra
