/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Physlib.SpaceAndTime.SpaceTime.SpaceTimeAlgebra.Basic
/-!
# Taylor determinacy and completeness of jets

## i. Overview

A jet is determined by the base-point values of its iterated derivatives, and a jet all of
whose first derivatives vanish is the constant jet of its value. These are the two facts
that make the jets of a matrix gauge group a faithful package of local gauge data, in the
sense of `LocalGaugeData.Faithful`. Conversely every family of base-point Taylor data is
realized by a jet, `ofDerivValues`, and entrywise by a matrix of jets, `taylorMatrix`: this
is the Taylor completeness half of `LocalGaugeData.Free`.

## ii. Key results

- `SpaceTimeAlgebra.ext_of_constantCoeff_iteratedPDeriv` : Taylor determinacy.
- `SpaceTimeAlgebra.eq_C_of_pderiv_eq_zero` : a jet with vanishing derivatives is constant.
- `SpaceTimeAlgebra.ofDerivValues` :
  Taylor completeness.
- `SpaceTimeAlgebra.taylorMatrix` : Taylor completeness for matrices of jets.

## iii. Table of contents

- A. Taylor determinacy
- B. Taylor completeness

-/

@[expose] public section

namespace SpaceTimeAlgebra

open MvPowerSeries

/-!

## B. Taylor completeness

-/

lemma star_ofDerivValues (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ) :
    star (ofDerivValues f) = ofDerivValues fun s => star (f s) := by
  ext m
  rw [coeff_star, coeff_ofDerivValues, coeff_ofDerivValues, star_mul', star_inv₀,
    star_natCast]

lemma ofDerivValues_sum {ι : Type} (t : Finset ι) (f : ι → Multiset (Fin 1 ⊕ Fin 3) → ℂ) :
    ofDerivValues (fun s => ∑ i ∈ t, f i s) = ∑ i ∈ t, ofDerivValues (f i) := by
  ext m
  simp only [coeff_ofDerivValues, map_sum, Finset.mul_sum]

/-- The matrix of jets with prescribed base-point Taylor data `M`, entrywise. -/
noncomputable def taylorMatrix {κ : Type} (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) :
    Matrix κ κ SpaceTimeAlgebra :=
  Matrix.of fun i j => ofDerivValues fun s => M s i j

lemma taylorMatrix_apply {κ : Type} (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) (i j : κ) :
    taylorMatrix M i j = ofDerivValues fun s => M s i j :=
  rfl

lemma star_taylorMatrix {κ : Type} {M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ}
    (hM : ∀ s, star (M s) = M s) : star (taylorMatrix M) = taylorMatrix M := by
  ext i j : 1
  rw [Matrix.star_apply, taylorMatrix_apply, taylorMatrix_apply, star_ofDerivValues]
  exact congrArg ofDerivValues (funext fun s => by rw [← Matrix.star_apply, hM s])

lemma trace_taylorMatrix {κ : Type} [Fintype κ] {M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ}
    (hM : ∀ s, (M s).trace = 0) : (taylorMatrix M).trace = 0 := by
  have h : ∀ s, ∑ i, M s i i = 0 := fun s => hM s
  simp only [Matrix.trace, Matrix.diag_apply, taylorMatrix_apply, ← ofDerivValues_sum, h]
  ext m
  simp [coeff_ofDerivValues]

/-- The base-point Taylor data of `taylorMatrix M` are `M`, entrywise. -/
lemma map_constantCoeff_iteratedPDeriv_taylorMatrix {κ : Type}
    (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (taylorMatrix M).map (fun f => constantCoeff (iteratedPDeriv s f)) = M s := by
  ext i j
  rw [Matrix.map_apply, taylorMatrix_apply, constantCoeff_iteratedPDeriv_ofDerivValues]

end SpaceTimeAlgebra
