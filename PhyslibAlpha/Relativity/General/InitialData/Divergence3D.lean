/-
Copyright (c) 2026 The Gravitation formalisation contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!

# Divergence theorem on a spatial box

## i. Overview

This file starts the three-dimensional energy layer.  It records Mathlib's
Bochner divergence theorem in the form used by the wave energy method: for a
continuous vector field on a closed box whose derivatives exist in the interior
and whose normal components vanish on every face, the integral of the
divergence is zero.

The next layer will identify the energy derivative with this divergence for a
solution of `u_tt = Δu`; the present file only supplies the integration-by-parts
tool.


## ii. Key results

- `divergence3D`
- `integral_divergence_box_eq_zero`

## iii. Table of contents

- A. The divergence theorem in a box

## iv. References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §C.2.
-/
@[expose] public section

/-! ## A. The divergence theorem in a box -/

open Set MeasureTheory BoxIntegral

namespace GeneralRelativity

/-- Three-dimensional coordinate space for the spatial box. -/
abbrev Space3 : Type := Fin 3 → ℝ

/-- **Divergence theorem with vanishing boundary flux.**  If `F` is continuous
on the closed box, differentiable in its interior with derivative `F'`, and each
face integral of the normal component of `F` vanishes, then the integral of the
divergence of `F` is zero. -/
lemma integral_divergence_box_eq_zero
    (I : Box (Fin 3)) (F : Space3 → Space3) (F' : Space3 → Space3 →L[ℝ] Space3)
    (hF_cont : ContinuousOn F (Box.Icc I))
    (hF_deriv : ∀ x ∈ Box.Ioo I, HasFDerivAt F (F' x) x)
    (hdiv_int : IntegrableOn (fun x => ∑ i, F' x (Pi.single i 1) i) (Box.Icc I))
    (hface_upper : ∀ i : Fin 3,
      (∫ x in Box.Icc (I.face i), F (i.insertNth (I.upper i) x) i) = 0)
    (hface_lower : ∀ i : Fin 3,
      (∫ x in Box.Icc (I.face i), F (i.insertNth (I.lower i) x) i) = 0) :
    (∫ x in Box.Icc I, ∑ i, F' x (Pi.single i 1) i) = 0 := by
  have h := integral_divergence_of_hasFDerivAt_off_countable
    (n := 2) (E := ℝ) (a := I.lower) (b := I.upper) I.lower_le_upper F F' ∅
    (by simp) hF_cont
    (by
      intro x hx
      refine hF_deriv x ?_
      change x ∈ Set.pi Set.univ (fun i => Set.Ioo (I.lower i) (I.upper i))
      exact hx.1)
    hdiv_int
  have hR :
      (∑ i : Fin 3,
        ((∫ x in Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove),
            F (i.insertNth (I.upper i) x) i) -
          ∫ x in Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove),
            F (i.insertNth (I.lower i) x) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hu :
        (∫ x in Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove),
          F (i.insertNth (I.upper i) x) i) = 0 := by
      simpa [Box.Icc_def, Box.face] using hface_upper i
    have hl :
        (∫ x in Icc (I.lower ∘ i.succAbove) (I.upper ∘ i.succAbove),
          F (i.insertNth (I.lower i) x) i) = 0 := by
      simpa [Box.Icc_def, Box.face] using hface_lower i
    rw [hu, hl, sub_self]
  rw [hR] at h
  simpa [Box.Icc_def] using h

end GeneralRelativity
