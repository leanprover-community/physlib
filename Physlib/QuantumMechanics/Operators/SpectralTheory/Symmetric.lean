/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Philippe Kevorkian, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.Basic
/-!

# Spectral theory for symmetric operators

## i. Overview

In this module we develop the spectral theory for symmetric operators.

The numerical range of an operator, `Θ T = {⟪x, T x⟫_ℂ | x ∈ T.domain ∧ ‖x‖ = 1}`, is a subset of ℂ.
For symmetric operators the numerical range consists only of real numbers and it is meaningful
to discuss its upper/lower bounds. To facilitate this, we define `LinearPMap.realNumericalRange`
as the projection of `LinearPMap.numericalRange` onto the real axis. For symmetric operators this
simply reinterprets the numerical range as a subset of ℝ.

## ii. Key results

- `realNumericalRange` (`Θᵣₑ`) : The projection of the numerical range onto the real axis.
- `compl_ofReal_subset_regularityDomain` : The regularity domain of a symmetric operator contains
    all complex numbers with non-zero imaginary part.
- `regularityDomain_isConnected_iff` : The regularity domain of a symmetric operator is connected
    if and only if it contains a real number.
- `IsSymmetric.isEssentiallySelfAdjoint_of_defectNumber_eq_zero` : The basic criterion for
    essential self-adjointness: symmetric + densely defined + vanishing defect numbers at `± i`.
- `IsSymmetric.isEssentiallySelfAdjoint_of_dense_span_eigenvectors` : A symmetric operator with a
    family of eigenvectors in its domain whose span is dense is essentially self-adjoint.

## iii. Table of contents

- A. Numerical range
- B. Regularity domain
- C. Point spectrum
- D. Essential self-adjointness

## iv. References

* None.
-/

@[expose] public section

namespace LinearPMap
namespace IsSymmetric

open InnerProductSpace
open Complex
open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-!
## A. Numerical range
-/

/-- The projection of the numerical range onto the real axis. -/
def realNumericalRange (T : H →ₗ.[ℂ] H) : Set ℝ := re '' (Θ T)

@[inherit_doc realNumericalRange]
local notation "Θᵣₑ" => realNumericalRange

lemma realNumericalRange_eq (T : H →ₗ.[ℂ] H) : Θᵣₑ T = re '' Θ T := rfl

@[simp]
lemma realNumericalRange_neg (T : H →ₗ.[ℂ] H) : Θᵣₑ (-T) = -Θᵣₑ T := by
  ext
  simp [realNumericalRange_eq, neg_eq_iff_eq_neg]

variable {T : H →ₗ.[ℂ] H} (hT : T.IsSymmetric)
include hT

/-- The numerical range of a symmetric operator is contained in the real axis. -/
lemma im_eq_zero_of_mem_numericalRange {z : ℂ} (hz : z ∈ Θ T) : z.im = 0 := by
  obtain ⟨x, hx, hxz⟩ := hz
  simp only [← hT x x] at hxz
  exact conj_eq_iff_im.mp (hxz ▸ isSymmetric_iff_inner_map_self_real.mp hT x)

/-- The numerical range of a symmetric operator is contained in the real axis. -/
lemma numericalRange_subset : Θ T ⊆ range ofReal :=
  fun z hz ↦ ⟨z.re, Complex.ext rfl (hT.im_eq_zero_of_mem_numericalRange hz).symm⟩

/-- The numerical range of a symmetric operator is equal to its projection onto the real axis. -/
lemma numericalRange_eq : Θ T = ofReal '' Θᵣₑ T := by
  rw [realNumericalRange_eq, ← image_comp]
  exact (image_id _).symm.trans
    (image_congr fun z hz ↦ Complex.ext rfl (hT.im_eq_zero_of_mem_numericalRange hz))

lemma closure_numericalRange_subset : _root_.closure (Θ T) ⊆ range ofReal :=
  (closure_mono hT.numericalRange_subset).trans
    Complex.isometry_ofReal.isClosedEmbedding.isClosed_range.closure_subset

/-!
## B. Regularity domain
-/

/-- The regularity domain of a symmetric operator contains all complex numbers with non-zero
  imaginary part. -/
lemma mem_regularityDomain_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z ∈ T.regularityDomain := by
  apply T.compl_closure_numericalRange_subset_regularityDomain
  refine (mem_compl_iff _ _).mpr fun h ↦ hz ?_
  obtain ⟨r, _, rfl⟩ := hT.closure_numericalRange_subset h
  exact ofReal_im r

/-- The regularity domain of a symmetric operator contains all complex numbers with non-zero
  imaginary part. -/
lemma compl_ofReal_subset_regularityDomain : (range ofReal)ᶜ ⊆ T.regularityDomain :=
  fun z hz ↦ hT.mem_regularityDomain_of_im_ne_zero fun h ↦ hz ⟨z.re, Eq.symm (Complex.ext rfl h)⟩

/-- If `m` is a lower bound on the numerical range then the regularity domain contains `(-∞,m)`. -/
lemma Iio_subset_regularityDomain {m : ℝ} (h : m ∈ lowerBounds (Θᵣₑ T)) :
    ofReal '' Iio m ⊆ T.regularityDomain := by
  intro z ⟨r, hr, hrz⟩
  refine ⟨m - r, sub_pos.mpr hr, fun x ↦ ?_⟩
  rcases eq_zero_or_neZero x with rfl | hx
  · simp
  · obtain ⟨s, hs, hs'⟩ := hT.numericalRange_eq ▸ mem_numericalRange hx.ne
    apply h at hs
    have hsr : r < s := lt_of_lt_of_le hr hs
    refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hx.ne)
    calc
      _ = (m - r) * ‖x‖ ^ 2 := by rw [mul_assoc, pow_two]
      _ ≤ (s - r) * ‖x‖ ^ 2 := by nlinarith
      _ = ‖s * ‖x‖ ^ 2 - r * ‖x‖ ^ 2‖ := by simp [← sub_mul, abs_of_pos, sub_pos, hsr]
      _ = ‖(s : ℂ) * ‖x‖ ^ 2 - r * ‖x‖ ^ 2‖ := by simp [← ofReal_pow, ← ofReal_mul, ← ofReal_sub]
      _ = ‖⟪↑x, T x⟫_ℂ - r * ‖x‖ ^ 2‖ := by simp [hs', mul_comm, hx.ne]
      _ = ‖⟪↑x, T x - z • x⟫_ℂ‖ := by simp [inner_sub_right, inner_smul_right, hrz]
      _ ≤ ‖T x - z • x‖ * ‖x‖ := mul_comm _ ‖x‖ ▸ norm_inner_le_norm _ _

/-- If `m` is an upper bound on the numerical range then the regularity domain contains `(m,∞)`. -/
lemma Ioi_subset_regularityDomain {m : ℝ} (h : m ∈ upperBounds (Θᵣₑ T)) :
    ofReal '' Ioi m ⊆ T.regularityDomain := by
  intro z ⟨r, hr, hrz⟩
  rw [← neg_mem_neg, ← regularityDomain_neg]
  refine hT.neg.Iio_subset_regularityDomain (m := -m) ?_ ?_
  · exact fun _ _ ↦ by simp_all [neg_le.mp, upperBounds]
  · exact ⟨-r, by simp [mem_Ioi.mp hr], by simp [hrz]⟩

/-- The regularity domain of a symmetric operator is connected iff it contains a real number. -/
lemma regularityDomain_isConnected_iff :
    IsConnected T.regularityDomain ↔ (ofReal ⁻¹' T.regularityDomain).Nonempty := by
  rw [T.regularityDomain_isOpen.isConnected_iff_isPathConnected]
  constructor
  · intro h
    obtain ⟨f, hf⟩ : JoinedIn T.regularityDomain (-I) I :=
      h.joinedIn _ (hT.mem_regularityDomain_of_im_ne_zero (by simp)) _
        (hT.mem_regularityDomain_of_im_ne_zero (by simp))
    have hIVT := intermediate_value_Icc (f := fun t ↦ (f t).im) zero_le_one (by fun_prop)
    simp only [Path.source, neg_im, I_im, Path.target] at hIVT
    obtain ⟨t, _, ht⟩ := hIVT (show (0 : ℝ) ∈ Icc (-1) 1 by simp)
    specialize hf t
    rw [← re_add_im (f t), show (f t).im = 0 from ht] at hf
    exact ⟨(f t).re, by simp_all⟩
  · intro ⟨r, hr⟩
    apply mem_preimage.mp at hr
    refine isPathConnected_iff.mpr ⟨?_, fun z₁ hz₁ z₂ hz₂ ↦ ?_⟩
    · exact ⟨I, hT.mem_regularityDomain_of_im_ne_zero (by simp)⟩
    · have h : ∀ z ∈ T.regularityDomain, JoinedIn T.regularityDomain z r := by
        intro z hz
        by_cases hz_im : z.im = 0
        · rcases eq_or_ne z r with rfl | hzr
          · exact JoinedIn.refl hr
          · let path : Path z r := {
              toFun t := ((z + r) + (z - r) * cexp (Real.pi * t * I)) / 2
              source' := by simp
              target' := by simp [add_comm z r, add_add_sub_cancel]
            }
            refine ⟨path, fun t ↦ ?_⟩
            by_cases! ht : ∃ n : ℤ, n = (t : ℝ)
            · obtain ⟨n, htn⟩ := ht
              have hexp : cexp (Real.pi * t * I) = (-1) ^ n := by
                rw [← exp_pi_mul_I, ← exp_int_mul, ← htn]
                exact congrArg cexp (by push_cast; ring)
              rcases Int.even_or_odd n with he | ho
              · simp [path, hexp, he.neg_one_zpow, hz]
              · simp [path, hexp, ho.neg_one_zpow, add_comm z r, hr]
            · have hzr' : z.re - r ≠ 0 :=
                  fun h ↦ hzr <| Complex.ext (sub_eq_zero.mp h) (by simp [hz_im])
              refine hT.mem_regularityDomain_of_im_ne_zero ?_
              simp [path, hz_im, exp_im, Real.sin_eq_zero_iff, mul_comm, hzr', ht]
        · refine JoinedIn.of_segment_subset fun w ⟨a, b, _, _, _, hw⟩ ↦ ?_
          rcases eq_zero_or_neZero a with rfl | _
          · simp_all
          · exact hT.mem_regularityDomain_of_im_ne_zero fun _ ↦ hz_im (by simp_all [← hw])
      exact (h z₁ hz₁).trans (h z₂ hz₂).symm

/-- The regularity domain of a lower semibounded symmetric operator is connected. -/
lemma regularityDomain_isConnected_of_bddBelow (h : BddBelow (Θᵣₑ T)) :
    IsConnected T.regularityDomain := by
  obtain ⟨m, hm⟩ := h
  apply hT.regularityDomain_isConnected_iff.mpr
  exact ⟨m - 1, hT.Iio_subset_regularityDomain hm ⟨m - 1, by simp⟩⟩

/-- The regularity domain of an upper semibounded symmetric operator is connected. -/
lemma regularityDomain_isConnected_of_bddAbove (h : BddAbove (Θᵣₑ T)) :
    IsConnected T.regularityDomain := by
  obtain ⟨m, hm⟩ := h
  apply hT.regularityDomain_isConnected_iff.mpr
  exact ⟨m + 1, hT.Ioi_subset_regularityDomain hm ⟨m + 1, by simp⟩⟩

/-!
## C. Point spectrum
-/

/-- Eigenvalues of a symmetric unbounded operator are real. -/
lemma pointSpectrum_real : σᵖ T ⊆ range ofReal := by
  intro z hz
  apply hT.numericalRange_subset
  obtain ⟨x, hx, hx₀⟩ := (Submodule.ne_bot_iff _).mp hz
  suffices z = (‖x‖ ^ 2)⁻¹ * ⟪↑x, T ⟨x, x.2.1⟩⟫_ℂ by
    exact this ▸ mem_numericalRange (T := T) (x := ⟨x, x.2.1⟩) (by simp [hx₀])
  rw [ofReal_inv]
  refine (eq_inv_mul_iff_mul_eq₀ (by simp [hx₀])).mpr (Eq.symm ?_)
  calc
    _ = ⟪↑x, (T - z • 1) x + z • x⟫_ℂ := by simp [sub_apply]
    _ = ⟪x, z • x⟫_ℂ := by simp [← toFun_eq_coe, LinearMap.mem_ker.mp hx]
    _ = ↑(‖x‖ ^ 2) * z := by simp [inner_smul_right, mul_comm]

/-- An eigenvector `x` of a symmetric operator `T`, `T x = c • x`, lies in the range of
  `T - z • 1` for every `z` with nonzero imaginary part. -/
lemma mem_range_sub_smul_of_apply_eq_smul {x : T.domain} {c z : ℂ} (hx : T x = c • (x : H))
    (hz : z.im ≠ 0) : (x : H) ∈ (T - z • 1).toFun.range := by
  by_cases h0 : (x : H) = 0
  · rw [h0]
    exact Submodule.zero_mem _
  have hcz : c - z ≠ 0 := by
    intro hcz
    apply hz
    have h1 := hT x x
    rw [hx, inner_smul_left, inner_smul_right] at h1
    rw [← sub_eq_zero.mp hcz]
    exact conj_eq_iff_im.mp (mul_right_cancel₀ (inner_self_ne_zero.mpr h0) h1)
  have hxT : (c - z)⁻¹ • (x : H) ∈ T.domain := T.domain.smul_mem _ x.2
  have hx' : (c - z)⁻¹ • (x : H) ∈ (T - z • 1).domain := by simp [sub_domain, hxT]
  refine ⟨⟨_, hx'⟩, ?_⟩
  have h1 : T ⟨(c - z)⁻¹ • (x : H), hxT⟩ = (c - z)⁻¹ • T x := T.map_smul _ x
  simp only [toFun_eq_coe, sub_apply, h1, hx, smul_smul, smul_domain, one_domain, coe_smul,
    one_coe, LinearEquiv.coe_coe, Pi.smul_apply, Submodule.topEquiv_apply]
  rw [mul_comm z, ← sub_smul, ← mul_sub, inv_mul_cancel₀ hcz, one_smul]

/-!
## D. Essential self-adjointness
-/

variable [CompleteSpace H]

/-- The basic criterion for essential self-adjointness: a symmetric, densely-defined operator
whose defect numbers at `I` and `-I` both vanish is essentially self-adjoint. -/
lemma isEssentiallySelfAdjoint_of_defectNumber_eq_zero
    (hdense : T.HasDenseDomain) (hpos : T.defectNumber I = 0) (hneg : T.defectNumber (-I) = 0) :
    T.IsEssentiallySelfAdjoint := by
  have hrange {z : ℂ} (hz : z.im ≠ 0) (hd : T.defectNumber z = 0) :
      (T.closure - z • 1).toFun.range = ⊤ := by
    have hz' : z ∈ T.regularityDomain := hT.mem_regularityDomain_of_im_ne_zero hz
    have hcl : T.closure.IsClosed := (hT.isClosable hdense).closure_isClosed
    rw [← hcl.defectNumber_eq_zero_iff (T.regularityDomain_closure ▸ hz'),
      defectNumber_closure hz']
    exact hd
  rw [isEssentiallySelfAdjoint_def]
  apply (hT.closure hdense).isSelfAdjoint_of_range_eq_top hdense.closure
  · have hI : T.closure + I • 1 = T.closure - (-I) • 1 :=
      LinearPMap.ext rfl fun x hf hg => by simp [sub_apply, add_apply, smul_apply, sub_neg_eq_add]
    rw [hI]
    exact hrange (by norm_num) hneg
  · exact hrange (by norm_num) hpos

/-- A symmetric operator `T` with a family `v` of vectors of its domain which are eigenvectors,
  `T (v j) = c j • v j` for complex numbers `c j`, and whose span is dense, is essentially
  self-adjoint. No orthonormality, no nonzero condition and no reality of the `c j` is assumed. -/
lemma isEssentiallySelfAdjoint_of_dense_span_eigenvectors {ι : Type*} (v : ι → T.domain)
    (c : ι → ℂ) (hv : ∀ j, T (v j) = c j • (v j : H))
    (hspan : Dense (Submodule.span ℂ (Set.range fun j ↦ (v j : H)) : Set H)) :
    T.IsEssentiallySelfAdjoint := by
  have hbot : (Submodule.span ℂ (Set.range fun j ↦ (v j : H)))ᗮ = ⊥ :=
    Submodule.topologicalClosure_eq_top_iff.mp
      (Submodule.dense_iff_topologicalClosure_eq_top.mp hspan)
  have hdef (z : ℂ) (hz : z.im ≠ 0) : T.defectNumber z = 0 := by
    have hle : Submodule.span ℂ (Set.range fun j ↦ (v j : H)) ≤ (T - z • 1).toFun.range :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦
        hT.mem_range_sub_smul_of_apply_eq_smul (hv j) hz)
    have h : Module.rank ℂ ((T - z • 1).toFun.range)ᗮ = 0 :=
      Submodule.rank_eq_zero.mpr (eq_bot_iff.mpr (hbot ▸ Submodule.orthogonal_le hle))
    exact h
  exact hT.isEssentiallySelfAdjoint_of_defectNumber_eq_zero
    (hspan.mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j ↦ (v j).2)))
    (hdef I (by simp)) (hdef (-I) (by simp))

end IsSymmetric
end LinearPMap
