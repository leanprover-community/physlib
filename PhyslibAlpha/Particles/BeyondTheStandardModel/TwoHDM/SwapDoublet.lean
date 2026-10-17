/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.BeyondTheStandardModel.TwoHDM.EffectivePotential
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Degrees
/-!
# Swapping the two Higgs doublets

The doublet swap Φ1 ↔ Φ2 commutes with gauge action, preserving invariance and mass dimension.

## i. Overview

Exchanging the two doublets `Φ1 ↔ Φ2` is an `ℝ`-linear map `swapDoublet` that commutes with the
gauge action. It therefore preserves gauge invariance and the maximum mass dimension, while turning
the alignment of `Φ1` into the alignment of `Φ2`. This is precisely the symmetry used to clear the
`‖Φ2‖²` factor when writing the potential through the gauge invariants, mirroring the `‖Φ1‖²`
clearing.

## ii. Key results

* `swapDoublet` — the doublet exchange, as an `ℝ`-linear map.
* `swapDoublet_smul` — it commutes with the gauge action.
* `gramVector_swapDoublet_*` — its effect on the Gram vector (a sign flip on the imaginary and
  difference components).
* `IsInvariant.comp_swapDoublet`, `HasMaxMassDimLE.comp_swapDoublet` — it preserves gauge invariance
  and bounded mass dimension.

## iii. Table of contents

- A. The doublet-swap map and its components
- B. Commutation with the gauge action
- C. The action on the Gram vector
- D. Effect on gauge invariance and mass dimension

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace TwoHiggsDoublet
open InnerProductSpace
open StandardModel

namespace EffectivePotential

/-!
## A. The doublet-swap map and its components
-/

/-- Swapping the two doublets, as an `ℝ`-linear map. It commutes with the gauge action, so it sends
  gauge-invariant polynomial potentials to gauge-invariant polynomial potentials, but turns the
  alignment of `Φ1` into the alignment of `Φ2`. -/
def swapDoublet : TwoHiggsDoublet →ₗ[ℝ] TwoHiggsDoublet where
  toFun φ := { Φ1 := φ.Φ2, Φ2 := φ.Φ1 }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma swapDoublet_Φ1 (φ : TwoHiggsDoublet) : (swapDoublet φ).Φ1 = φ.Φ2 := rfl
@[simp] lemma swapDoublet_Φ2 (φ : TwoHiggsDoublet) : (swapDoublet φ).Φ2 = φ.Φ1 := rfl

@[simp] lemma swapDoublet_swapDoublet (φ : TwoHiggsDoublet) : swapDoublet (swapDoublet φ) = φ := by
  apply ext_of_fst_snd <;> rfl

/-!
## B. Commutation with the gauge action
-/

lemma swapDoublet_smul (g : StandardModel.GaugeGroupI) (φ : TwoHiggsDoublet) :
    swapDoublet (g • φ) = g • swapDoublet φ := by
  apply ext_of_fst_snd <;> simp

/-!
## C. The action on the Gram vector
-/

/-- Swapping the doublets sends the gram vector through the sign flip of the imaginary and
  difference components. -/
lemma gramVector_swapDoublet_inl (φ : TwoHiggsDoublet) :
    (swapDoublet φ).gramVector (Sum.inl 0) = φ.gramVector (Sum.inl 0) := by
  rw [gramVector_inl_zero_eq, gramVector_inl_zero_eq, swapDoublet_Φ1, swapDoublet_Φ2]; ring

lemma gramVector_swapDoublet_inr0 (φ : TwoHiggsDoublet) :
    (swapDoublet φ).gramVector (Sum.inr 0) = φ.gramVector (Sum.inr 0) := by
  rw [gramVector_inr_zero_eq, gramVector_inr_zero_eq, swapDoublet_Φ1, swapDoublet_Φ2,
    ← inner_conj_symm, Complex.conj_re]

lemma gramVector_swapDoublet_inr1 (φ : TwoHiggsDoublet) :
    (swapDoublet φ).gramVector (Sum.inr 1) = -φ.gramVector (Sum.inr 1) := by
  rw [gramVector_inr_one_eq, gramVector_inr_one_eq, swapDoublet_Φ1, swapDoublet_Φ2,
    ← inner_conj_symm, Complex.conj_im]; ring

lemma gramVector_swapDoublet_inr2 (φ : TwoHiggsDoublet) :
    (swapDoublet φ).gramVector (Sum.inr 2) = -φ.gramVector (Sum.inr 2) := by
  rw [gramVector_inr_two_eq, gramVector_inr_two_eq, swapDoublet_Φ1, swapDoublet_Φ2]; ring

/-!
## D. Effect on gauge invariance and mass dimension
-/

lemma HasMaxMassDimLE.comp_swapDoublet {V : EffectivePotential} {n : ℕ}
    (h : HasMaxMassDimLE V n) : HasMaxMassDimLE (fun φ => V (swapDoublet φ)) n := by
  obtain ⟨p, hp, hdeg⟩ := h
  refine ⟨MvPolynomial.rename
    (fun i : Module.Dual ℝ TwoHiggsDoublet => i.comp swapDoublet) p, fun φ => ?_, ?_⟩
  · change V (swapDoublet φ) = _
    rw [MvPolynomial.eval_rename, hp (swapDoublet φ)]; rfl
  · exact le_trans (MvPolynomial.totalDegree_rename_le _ _) hdeg

lemma IsInvariant.comp_swapDoublet {V : EffectivePotential} (hI : IsInvariant V) :
    IsInvariant (fun φ => V (swapDoublet φ)) := by
  intro g φ
  show V (swapDoublet (g • φ)) = V (swapDoublet φ)
  rw [swapDoublet_smul, hI g]

end EffectivePotential

end TwoHiggsDoublet
