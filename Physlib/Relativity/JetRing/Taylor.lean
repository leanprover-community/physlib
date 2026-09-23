/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Relativity.JetRing.Basic
/-!
# Taylor determinacy of jets

## i. Overview

A jet is determined by the base-point values of its iterated derivatives, and a jet all of
whose first derivatives vanish is the constant jet of its value. These are the two facts
that make the jets of a matrix gauge group a faithful package of local gauge data, in the
sense of `LocalGaugeData.Faithful`.

## ii. Key results

- `JetRing.ext_of_constantCoeff_foldl_pderiv` : Taylor determinacy.
- `JetRing.eq_C_of_pderiv_eq_zero` : a jet with vanishing derivatives is constant.

-/

@[expose] public section

namespace JetRing

open MvPowerSeries

/-- **Taylor determinacy**: two jets with the same base-point values of all iterated
  derivatives are equal. -/
lemma ext_of_constantCoeff_foldl_pderiv {f g : JetRing}
    (h : ∀ s : Multiset (Fin 1 ⊕ Fin 3),
      constantCoeff (s.foldl (fun h ρ => pderiv ρ h) f)
        = constantCoeff (s.foldl (fun h ρ => pderiv ρ h) g)) : f = g := by
  ext m
  obtain ⟨s, rfl⟩ : ∃ s : Multiset (Fin 1 ⊕ Fin 3), s.toFinsupp = m :=
    ⟨Multiset.toFinsupp.symm m, Multiset.toFinsupp.apply_symm_apply m⟩
  have hs := h s
  rw [constantCoeff_foldl_pderiv, constantCoeff_foldl_pderiv] at hs
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)) hs

/-- A jet all of whose first derivatives vanish is the constant jet of its value. -/
lemma eq_C_of_pderiv_eq_zero {f : JetRing} (hf : ∀ μ, pderiv μ f = 0) :
    f = C (constantCoeff f) :=
  pderiv.ext (fun i => by rw [hf i, pderiv_C]) (by rw [constantCoeff_C])

end JetRing
