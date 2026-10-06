/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Measurement.Binary
public import PhyslibAlpha.ProbabilisticTheory.Measurement.Postprocessing

/-!
# Compatibility of measurements

Compatible and jointly measurable measurements, with an order criterion for binary ones.

## i. Overview

Two measurements are compatible when both can be obtained from one measurement by classical
post-processing of its outcome: performing the common measurement answers both.

A joint measurement of two measurements is a measurement of pairs of outcomes whose marginals are
the two measurements. Jointly measurable measurements are compatible. The binary measurements of
two effects `e` and `f` are jointly measurable exactly when some `g` lies above `0` and `e + f - 1`
and below `e` and `f`: `g` is the effect of both outcomes being `true`.

## ii. Key results

- `Measurement.Compatible` : compatibility of measurements.
- `Measurement.Compatible.mono` : compatibility is preserved by post-processing.
- `Measurement.Joint` : a joint measurement of two measurements.
- `Measurement.JointlyMeasurable.compatible` : jointly measurable measurements are
  compatible.
- `Effect.jointlyMeasurable_binaryMeasurement_iff` : the order criterion for joint measurability of
  two binary measurements.

## iii. Table of contents

- A. Compatibility of measurements
- B. Joint measurements
- C. Binary compatibility

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ProbabilityTheory

namespace Measurement

open scoped Measurement

universe u v

variable {Ω Ω' Ω₁ Ω₂ : Type v} {E : Type u}
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [OrderUnitSpace E]

/-! ## A. Compatibility of measurements -/

/-- Two measurements are compatible when they are both operational post-processings of a common
measurement. -/
def Compatible (M : Measurement Ω E) (N : Measurement Ω' E) : Prop :=
  ∃ (Γ : Type v) (_ : MeasurableSpace Γ) (G : Measurement Γ E), M ≤ₚ G ∧ N ≤ₚ G

/-- Every measurement is compatible with itself. -/
lemma compatible_refl (M : Measurement Ω E) : Compatible M M :=
  ⟨Ω, inferInstance, M, postprocessing_refl M, postprocessing_refl M⟩

/-- Compatibility of measurements is symmetric. -/
lemma compatible_symm {M : Measurement Ω E} {N : Measurement Ω' E}
    (h : Compatible M N) : Compatible N M := by
  obtain ⟨Γ, mΓ, G, hM, hN⟩ := h
  exact ⟨Γ, mΓ, G, hN, hM⟩

/-- Replacing compatible measurements by post-processings preserves compatibility. -/
lemma Compatible.mono {M : Measurement Ω E} {N : Measurement Ω' E}
    {M' : Measurement Ω₁ E} {N' : Measurement Ω₂ E} (h : Compatible M N)
    (hM : M' ≤ₚ M) (hN : N' ≤ₚ N) : Compatible M' N' := by
  obtain ⟨Γ, mΓ, G, hMG, hNG⟩ := h
  exact ⟨Γ, mΓ, G, postprocessing_trans hM hMG, postprocessing_trans hN hNG⟩

/-- A measurement is compatible with each of its operational post-processings. -/
lemma compatible_of_postprocessing_left {M : Measurement Ω E}
    {N : Measurement Ω' E} (h : M ≤ₚ N) : Compatible M N :=
  ⟨Ω', inferInstance, N, h, postprocessing_refl N⟩

/-- A measurement is compatible with each measurement of which it is a post-processing. -/
lemma compatible_of_postprocessing_right {M : Measurement Ω E}
    {N : Measurement Ω' E} (h : N ≤ₚ M) : Compatible M N :=
  compatible_symm (compatible_of_postprocessing_left h)

end Measurement

namespace Measurement

open scoped Measurement

universe u v

variable {Ω Ω' : Type v} {E : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω'] [OrderUnitSpace E]

/-! ## B. Joint measurements -/

/-- A joint measurement of `M` and `N`: a measurement with outcome pairs whose marginals are `M`
and `N`. -/
structure Joint (M : Measurement Ω E) (N : Measurement Ω' E) where
  /-- The joint measurement. -/
  joint : Measurement (Ω × Ω') E
  /-- Its first marginal is `M`. -/
  fst_marginal : joint.mapOutcome Prod.fst measurable_fst = M
  /-- Its second marginal is `N`. -/
  snd_marginal : joint.mapOutcome Prod.snd measurable_snd = N

/-- Two measurements are jointly measurable when they have a joint measurement. -/
def JointlyMeasurable (M : Measurement Ω E) (N : Measurement Ω' E) : Prop :=
  Nonempty (Joint M N)

/-- Jointly measurable measurements are compatible. -/
lemma JointlyMeasurable.compatible {M : Measurement Ω E}
    {N : Measurement Ω' E} (h : JointlyMeasurable M N) : Compatible M N := by
  obtain ⟨G, rfl, rfl⟩ := h
  exact ⟨Ω × Ω', inferInstance, G, mapOutcome_isPostprocessing G Prod.fst measurable_fst,
    mapOutcome_isPostprocessing G Prod.snd measurable_snd⟩

end Measurement

namespace Effect

open Measurement

universe u

variable {E : Type u} [OrderUnitSpace E]

/-! ## C. Binary compatibility -/

/-- The four effects of a joint measurement of the binary measurements of `e` and `f` whose
`(true, true)` effect is `g`. -/
def binaryJointAtom (e f : Effect E) (g : E) : Bool × Bool → E
  | (true, true) => g
  | (true, false) => e - g
  | (false, true) => f - g
  | (false, false) => 1 - e - f + g

/-- Conditions on `g` making every `binaryJointAtom e f g` an effect. -/
def IsBinaryJointEffect (e f : Effect E) (g : E) : Prop :=
  0 ≤ g ∧ g ≤ e ∧ g ≤ f ∧ (e : E) + f - 1 ≤ g

/-- `g` is a joint effect for `e` and `f` up to `δ • 1`. -/
def IsApproxBinaryJointEffect (e f : Effect E) (δ : ℝ) (g : E) : Prop :=
  -(δ • (1 : E)) ≤ g ∧ g ≤ e + δ • 1 ∧ g ≤ f + δ • 1 ∧ (e : E) + f - 1 ≤ g + δ • 1

lemma IsBinaryJointEffect.isApprox {e f : Effect E} {g : E} (hg : IsBinaryJointEffect e f g)
    {δ : ℝ} (hδ : 0 ≤ δ) : IsApproxBinaryJointEffect e f δ g := by
  have h : (0 : E) ≤ δ • 1 := smul_nonneg hδ OrderUnitSpace.one_nonneg
  obtain ⟨h₀, h₁, h₂, h₃⟩ := hg
  exact ⟨(neg_nonpos.2 h).trans h₀, h₁.trans (le_add_of_nonneg_right h),
    h₂.trans (le_add_of_nonneg_right h), h₃.trans (le_add_of_nonneg_right h)⟩

lemma binaryJointAtom_mem {e f : Effect E} {g : E} (hg : IsBinaryJointEffect e f g) :
    ∀ p, binaryJointAtom e f g p ∈ (Effect E : Set E) := by
  obtain ⟨hg0, hge, hgf, hefg⟩ := hg
  rintro ⟨_ | _, _ | _⟩
  · refine ⟨?_, ?_⟩ <;> simp only [binaryJointAtom]
    · rw [show 1 - (e : E) - f + g = g - (e + f - 1) by abel]; exact sub_nonneg.2 hefg
    · rw [show 1 - (e : E) - f + g = 1 - (e + f - g) by abel]
      exact sub_le_self _ (sub_nonneg.2 (hge.trans (le_add_of_nonneg_right f.2.1)))
  · exact ⟨sub_nonneg.2 hgf, (sub_le_self _ hg0).trans f.2.2⟩
  · exact ⟨sub_nonneg.2 hge, (sub_le_self _ hg0).trans e.2.2⟩
  · exact ⟨hg0, hge.trans e.2.2⟩

lemma sum_binaryJointAtom (e f : Effect E) (g : E) : ∑ p, binaryJointAtom e f g p = 1 := by
  simp [Fintype.sum_prod_type, binaryJointAtom]

end Effect

namespace Effect

open Measurement

universe u

variable {E : Type u} [ArchimedeanOrderUnitSpace E]

/-- The joint measurement of the binary measurements of `e` and `f` with `(true, true)` effect
`g`. -/
noncomputable def binaryJoint {e f : Effect E} {g : E} (hg : IsBinaryJointEffect e f g) :
    Joint (binaryMeasurement e) (binaryMeasurement f) where
  joint := ofAtoms (fun p => ⟨_, binaryJointAtom_mem hg p⟩) (sum_binaryJointAtom e f g)
  fst_marginal := ext_of_singleton fun b => Subtype.ext <| by
    classical
    rw [coe_mapOutcome_apply, coe_ofAtoms_apply]
    cases b
    · rw [binaryMeasurement_false]; simp [Fintype.sum_prod_type, binaryJointAtom, complement]
    · rw [binaryMeasurement_true]; simp [Fintype.sum_prod_type, binaryJointAtom]
  snd_marginal := ext_of_singleton fun b => Subtype.ext <| by
    classical
    rw [coe_mapOutcome_apply, coe_ofAtoms_apply]
    cases b
    · rw [binaryMeasurement_false]; simp [Fintype.sum_prod_type, binaryJointAtom, complement]
      abel
    · rw [binaryMeasurement_true]; simp [Fintype.sum_prod_type, binaryJointAtom]

section BinaryJoint

variable {e f : Effect E}

/-- The effect of the joint outcome `p`. -/
noncomputable def _root_.ProbabilisticTheory.Measurement.Joint.jointAtom
    (J : Joint (binaryMeasurement e) (binaryMeasurement f)) (p : Bool × Bool) : E :=
  J.joint {p} (measurableSet_singleton p)

variable (J : Joint (binaryMeasurement e) (binaryMeasurement f))

lemma _root_.ProbabilisticTheory.Measurement.Joint.jointAtom_nonneg (p : Bool × Bool) :
    0 ≤ J.jointAtom p :=
  (J.joint {p} _).2.1

open Classical in
lemma _root_.ProbabilisticTheory.Measurement.Joint.coe_joint_eq_sum (s : Set (Bool × Bool))
    (hs : MeasurableSet s) :
    (J.joint s hs : E) = ∑ p, if p ∈ s then J.jointAtom p else 0 := by
  conv_lhs => rw [J.joint.eq_ofAtoms]
  rw [coe_ofAtoms_apply]; rfl

/-- The first marginal: the joint outcomes with first entry `true` add up to `e`. -/
lemma _root_.ProbabilisticTheory.Measurement.Joint.jointAtom_fst :
    J.jointAtom (true, true) + J.jointAtom (true, false) = e := by
  have h := congrArg (fun M : Measurement Bool E => (M {true} .of_discrete : E))
    J.fst_marginal
  simp only [coe_mapOutcome_apply, binaryMeasurement_true] at h
  rw [J.coe_joint_eq_sum] at h
  simpa [Fintype.sum_prod_type] using h

/-- The second marginal: the joint outcomes with second entry `true` add up to `f`. -/
lemma _root_.ProbabilisticTheory.Measurement.Joint.jointAtom_snd :
    J.jointAtom (true, true) + J.jointAtom (false, true) = f := by
  have h := congrArg (fun M : Measurement Bool E => (M {true} .of_discrete : E))
    J.snd_marginal
  simp only [coe_mapOutcome_apply, binaryMeasurement_true] at h
  rw [J.coe_joint_eq_sum] at h
  simpa [Fintype.sum_prod_type, add_comm] using h

/-- The four joint outcomes add up to the unit. -/
lemma _root_.ProbabilisticTheory.Measurement.Joint.jointAtom_sum :
    J.jointAtom (true, true) + J.jointAtom (true, false) +
    (J.jointAtom (false, true) + J.jointAtom (false, false)) = 1 := by
  have h := J.coe_joint_eq_sum .univ .univ
  rw [map_univ] at h
  simpa [Fintype.sum_prod_type, add_comm, add_left_comm, add_assoc] using h.symm

/-- The `(true, true)` effect of a joint measurement of two binary measurements satisfies the
joint-effect conditions. -/
lemma _root_.ProbabilisticTheory.Measurement.Joint.isBinaryJointEffect_jointAtom :
    IsBinaryJointEffect e f (J.jointAtom (true, true)) := by
  refine ⟨J.jointAtom_nonneg _, ?_, ?_, ?_⟩
  · rw [← J.jointAtom_fst]; exact le_add_of_nonneg_right (J.jointAtom_nonneg _)
  · rw [← J.jointAtom_snd]; exact le_add_of_nonneg_right (J.jointAtom_nonneg _)
  · rw [← J.jointAtom_fst, ← J.jointAtom_snd, ← J.jointAtom_sum]
    calc J.jointAtom (true, true) + J.jointAtom (true, false) +
          (J.jointAtom (true, true) + J.jointAtom (false, true)) -
          (J.jointAtom (true, true) + J.jointAtom (true, false) +
            (J.jointAtom (false, true) + J.jointAtom (false, false)))
        = J.jointAtom (true, true) - J.jointAtom (false, false) := by abel
      _ ≤ J.jointAtom (true, true) := sub_le_self _ (J.jointAtom_nonneg _)

end BinaryJoint

/-- The binary measurements of `e` and `f` are jointly measurable exactly when some `g` lies below
`e` and `f` and above `0` and `e + f - 1`. -/
lemma jointlyMeasurable_binaryMeasurement_iff (e f : Effect E) :
    JointlyMeasurable (binaryMeasurement e) (binaryMeasurement f) ↔
      ∃ g : E, IsBinaryJointEffect e f g :=
  ⟨fun ⟨J⟩ => ⟨_, J.isBinaryJointEffect_jointAtom⟩, fun ⟨_, hg⟩ => ⟨binaryJoint hg⟩⟩

/-- Binary measurements of effects with a common lower bound as above are compatible. -/
lemma compatible_binaryMeasurement {e f : Effect E} {g : E} (hg : IsBinaryJointEffect e f g) :
    Compatible (binaryMeasurement e) (binaryMeasurement f) :=
  JointlyMeasurable.compatible ⟨binaryJoint hg⟩

end Effect

end ProbabilisticTheory
