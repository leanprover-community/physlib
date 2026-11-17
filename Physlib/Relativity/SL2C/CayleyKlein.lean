/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.Relativity.SL2C.Basic
public import Physlib.Relativity.LorentzGroup.Rotations

/-!
# Cayley–Klein parameters

## i. Overview

Two complex numbers `a b` with `‖a‖² + ‖b‖² = 1`, the Cayley–Klein parameters, give the unitary
element `!![a, -conj b; b, conj a]` of `SL(2, ℂ)`. Its image in the Lorentz group is a rotation,
whose matrix is written explicitly in terms of `a` and `b`.

## ii. Key results

- `cayleyKlein` : the element of `SL(2, ℂ)` with Cayley–Klein parameters `a b`.
- `cayleyKlein_mem_unitaryGroup` : a Cayley–Klein element is unitary.
- `toLorentzGroup_cayleyKlein_mem_rotations` : the image of a Cayley–Klein element is a
  rotation.
- `cayleyKleinRotation` : the Lorentz-group rotation of the Cayley–Klein parameters `a b`.
- `cayleyKleinRotation_inr_inr` : the spatial block of `cayleyKleinRotation a b h` is the
  matrix written explicitly in terms of `a` and `b`.
- `exists_cayleyKleinRotation_apply_two` : every unit vector is the image of the third axis
  under some Cayley–Klein rotation.

## iii. Table of contents

- A. The Cayley–Klein element
- B. The Cayley–Klein rotation

## iv. References

* https://mathworld.wolfram.com/Cayley-KleinParameters.html

-/

@[expose] public section

namespace Lorentz

namespace SL2C

open Matrix MatrixGroups Complex PauliMatrix

noncomputable section

/-!

## A. The Cayley–Klein element

-/

/-- The element `!![a, -conj b; b, conj a]` of `SL(2, ℂ)`, given by its Cayley–Klein
parameters `a b` with `‖a‖² + ‖b‖² = 1`. -/
def cayleyKlein (a b : ℂ) (h : normSq a + normSq b = 1) : SL(2, ℂ) :=
  ⟨!![a, -(starRingEnd ℂ b); b, starRingEnd ℂ a], by
    rw [det_fin_two_of, neg_mul, sub_neg_eq_add, mul_conj, mul_comm _ b, mul_conj]
    exact_mod_cast h⟩

/-- A Cayley–Klein element is unitary. -/
lemma cayleyKlein_mem_unitaryGroup (a b : ℂ) (h : normSq a + normSq b = 1) :
    (cayleyKlein a b h).1 ∈ unitaryGroup (Fin 2) ℂ := by
  have h' : (normSq a : ℂ) + normSq b = 1 := by exact_mod_cast h
  rw [mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyKlein, mul_apply, Fin.sum_univ_two, mul_conj, ← h'] <;>
    ring

/-- The image of a Cayley–Klein element is a rotation. -/
lemma toLorentzGroup_cayleyKlein_mem_rotations (a b : ℂ) (h : normSq a + normSq b = 1) :
    toLorentzGroup (cayleyKlein a b h) ∈ LorentzGroup.Rotations 3 := by
  refine ⟨?_, toLorentzGroup_det_one _⟩
  rw [toLorentzGroup_inl_inl]
  simp [cayleyKlein, Complex.sq_norm]
  linarith

/-!

## B. The Cayley–Klein rotation

-/

/-- The rotation of the Cayley–Klein parameters `a b`, as an element of the Lorentz rotation
subgroup. -/
def cayleyKleinRotation (a b : ℂ) (h : normSq a + normSq b = 1) : LorentzGroup.Rotations 3 :=
  ⟨toLorentzGroup (cayleyKlein a b h), toLorentzGroup_cayleyKlein_mem_rotations a b h⟩

/-- The spatial block of the rotation of the Cayley–Klein parameters `a b`. -/
lemma cayleyKleinRotation_inr_inr (a b : ℂ) (h : normSq a + normSq b = 1) (i j : Fin 3) :
    (cayleyKleinRotation a b h).1.1 (Sum.inr i) (Sum.inr j) =
      !![(a ^ 2 - b ^ 2).re, (a ^ 2 - b ^ 2).im, 2 * (a * starRingEnd ℂ b).re;
        -(a ^ 2 + b ^ 2).im, (a ^ 2 + b ^ 2).re, -2 * (a * starRingEnd ℂ b).im;
        -2 * (a * b).re, -2 * (a * b).im, normSq a - normSq b] i j := by
  apply ofReal_injective
  rw [cayleyKleinRotation, toLorentzGroup_eq_trace, trace_pauliSelfAdjoint'_mul_apply]
  fin_cases i <;> fin_cases j <;>
      simp [cayleyKlein, pauliSelfAdjoint', pauliMatrix, mul_apply, Fin.sum_univ_two] <;>
    apply Complex.ext <;> simp [sq, normSq_apply] <;> ring

/-- Every unit vector is the image of the third axis under some Cayley–Klein rotation. -/
lemma exists_cayleyKleinRotation_apply_two (n : Fin 3 → ℝ)
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    ∃ a b, ∃ h : normSq a + normSq b = 1,
      ∀ i, (cayleyKleinRotation a b h).1.1 (Sum.inr i) (Sum.inr 2) = n i := by
  by_cases h2 : n 2 = -1
  · have h0 : n 0 = 0 := by nlinarith
    have h1 : n 1 = 0 := by nlinarith
    refine ⟨0, 1, by simp, fun i => ?_⟩
    rw [cayleyKleinRotation_inr_inr]
    fin_cases i <;> simp [h0, h1, h2]
  have hpos : 0 < 1 + n 2 := by
    rcases (show -1 ≤ n 2 by nlinarith).lt_or_eq with h | h
    · linarith
    · exact absurd h.symm h2
  set r := √((1 + n 2) / 2)
  have hr : r ^ 2 = (1 + n 2) / 2 := Real.sq_sqrt (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hab : normSq ⟨r, 0⟩ + normSq ⟨n 0 / (2 * r), n 1 / (2 * r)⟩ = 1 := by
    simp only [normSq_mk]
    field_simp
    nlinarith
  refine ⟨⟨r, 0⟩, ⟨n 0 / (2 * r), n 1 / (2 * r)⟩, hab, fun i => ?_⟩
  rw [cayleyKleinRotation_inr_inr]
  fin_cases i <;> simp [normSq_mk]
  · field_simp
  · field_simp
  · field_simp; nlinarith

end

end SL2C

end Lorentz
