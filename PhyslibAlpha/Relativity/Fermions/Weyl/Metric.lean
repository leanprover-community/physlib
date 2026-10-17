/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.Metric
/-!
# The Weyl metric as an element of `SL(2, ℂ)`

The symplectic form `ε` as a group element, and the identities moving it past a group element.

## i. Overview

The Weyl metric `Fermion.metricRaw = !![0, 1; -1, 0]` has determinant one, so it is itself an
element of `SL(2, ℂ)`, written `Lorentz.SL2C.epsilon`. In that form it is the invariant
symplectic form, `gᵀ ε g = ε`. Contracting spinor indices needs the single-index version of
that invariance: a factor of `(g⁻¹)ᵀ`, or of `(g⁻¹)ᴴ`, moved across `ε` becomes a factor of
`g`, or of its entrywise conjugate, on the other slot. Those are `metricRaw_comm` and
`metricRaw_comm_star` at `g⁻¹`, read entrywise. Alongside this, `leftMetricVal_rep` states the
invariance of `εᵃᵃ` as the plain equation on the tensor product, rather than through the
intertwining property of `leftMetric`.

## ii. Key results

- `Fermion.leftMetricVal_rep` : `εᵃᵃ` is invariant under `SL(2, ℂ)`.
- `Lorentz.SL2C.epsilon` : the Weyl metric as an element of `SL(2, ℂ)`.
- `Lorentz.SL2C.transpose_mul_epsilon_mul` : `ε` is the invariant symplectic form.
- `Lorentz.SL2C.sum_epsilon_mul_inv_transpose`,
  `Lorentz.SL2C.sum_epsilon_mul_inv_conjTranspose` : the single-index forms.

## iii. Table of contents

- A. Invariance of the left metric
- B. The symplectic form as an element of `SL(2, ℂ)`

## iv. References

The Weyl metrics and `Fermion.metricRaw` are in `Physlib.Relativity.Fermions.Weyl.Metric`.

-/

@[expose] public section

namespace Fermion

noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## A. Invariance of the left metric

-/

/-- The metric `εᵃᵃ` is invariant under the action of `SL(2,ℂ)`. -/
lemma leftMetricVal_rep (M : SL(2,ℂ)) :
    TensorProduct.map (LeftHandedWeyl.rep M) (LeftHandedWeyl.rep M) leftMetricVal =
      leftMetricVal := by
  have h := LinearMap.congr_fun (leftMetric.isIntertwining' M) (1 : ℂ)
  simpa [leftMetric_apply_one, Representation.tprod_apply] using h.symm

end

end Fermion

/-!

## B. The symplectic form as an element of `SL(2, ℂ)`

`ε = metricRaw` has determinant one, so it lies in `SL(2,ℂ)`, and `gᵀ ε g = ε` for every `g`
there. The single-index identities move a factor of `(g⁻¹)ᵀ` or `(g⁻¹)ᴴ` across `ε`, where it
becomes a factor of `g` or of its conjugate on the other slot: they are `metricRaw_comm` and
`metricRaw_comm_star` at `g⁻¹`, read entrywise.

-/

namespace Lorentz.SL2C

open Matrix MatrixGroups

/-- The antisymmetric symplectic form `ε = !![0, 1; -1, 0]`, the Weyl metric
  `Fermion.metricRaw`, as an element of `SL(2,ℂ)`. -/
def epsilon : SL(2,ℂ) :=
  ⟨Fermion.metricRaw, by simp [Fermion.metricRaw, Matrix.det_fin_two_of]⟩

/-- The matrix underlying `epsilon`. -/
lemma epsilon_coe : (epsilon : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := rfl

/-- The matrix underlying `epsilon` is the Weyl metric `Fermion.metricRaw`. -/
lemma epsilon_coe_metricRaw : (epsilon : Matrix (Fin 2) (Fin 2) ℂ) = Fermion.metricRaw := rfl

/-- The entries of `ε` are real. -/
lemma star_epsilon_apply (l k : Fin 2) : star (epsilon.1 l k) = epsilon.1 l k := by
  fin_cases l <;> fin_cases k <;> simp [epsilon_coe]

/-- `ε g⁻¹ = gᵀ ε`: `Fermion.metricRaw_comm` at `g⁻¹`. -/
lemma epsilon_mul_inv (g : SL(2,ℂ)) : epsilon.1 * g.1⁻¹ = g.1ᵀ * epsilon.1 := by
  have h := Fermion.metricRaw_comm g⁻¹
  rw [inverse_coe g⁻¹, inv_inv, ← inverse_coe g] at h
  exact h

/-- `ε` is the invariant symplectic form of `SL(2,ℂ)`: `gᵀ ε g = ε`. -/
lemma transpose_mul_epsilon_mul (g : SL(2,ℂ)) : g.1ᵀ * epsilon.1 * g.1 = epsilon.1 := by
  rw [← epsilon_mul_inv, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (by simp), Matrix.mul_one]

/-- Single-index form: a factor of `(g⁻¹)ᵀ` moved across `ε` becomes a factor of `g` on the
  other slot. -/
lemma sum_epsilon_mul_inv_transpose (g : SL(2,ℂ)) (l a : Fin 2) :
    ∑ k : Fin 2, epsilon.1 l k * (g.1⁻¹)ᵀ a k = ∑ b : Fin 2, g.1 b l * epsilon.1 b a := by
  have h : (epsilon.1 * g.1⁻¹) l a = (g.1ᵀ * epsilon.1) l a := by rw [epsilon_mul_inv]
  simpa [Matrix.mul_apply, Matrix.transpose_apply] using h

/-- The conjugate single-index form: a factor of `(g⁻¹)ᴴ` moved across `ε` becomes a factor of
  the conjugate of `g` on the other slot. -/
lemma sum_epsilon_mul_inv_conjTranspose (g : SL(2,ℂ)) (l a : Fin 2) :
    ∑ k : Fin 2, epsilon.1 l k * (g.1⁻¹)ᴴ a k
      = ∑ b : Fin 2, star (g.1 b l) * epsilon.1 b a := by
  have h0 := Fermion.metricRaw_comm_star g⁻¹
  rw [inverse_coe g⁻¹, inv_inv, ← inverse_coe g] at h0
  have h : (epsilon.1 * (g.1⁻¹).map star) l a = (g.1ᴴ * epsilon.1) l a := by
    rw [epsilon_coe_metricRaw, h0]
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply] using h

end Lorentz.SL2C
