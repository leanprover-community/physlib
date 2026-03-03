/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.Mathematics.Geometry.Metric.QuadraticForm.NegDim

/-!
# Noncanonical Sylvester choices for real quadratic forms

This file provides auxiliary, **noncanonical** data extracted from the existence theorem
`QuadraticForm.equivalent_signType_weighted_sum_squared` in
`Mathlib.LinearAlgebra.QuadraticForm.Real`.

The idea is that `equivalent_signType_weighted_sum_squared` produces an existential witness
of diagonalization; here we choose such a witness noncomputably.

The canonical inertia indices are defined in
`PhysLean.Mathematics.Geometry.Metric.QuadraticForm.NegDim` (via `QuadraticForm.posIndex`) and are
invariant under `QuadraticForm.Equivalent` without any diagonalization choice.

## Main definitions

- `QuadraticForm.signTypeWeights`: a chosen Sylvester diagonalization weight function
- `QuadraticForm.signatureChoice`: the resulting chosen signature `(pos, neg, zero)`

## Main statements

- `QuadraticForm.signature_eq_signatureChoice`: the canonical signature equals the chosen one

## Tags

quadratic form, Sylvester law, signature
-/

namespace QuadraticForm

open Finset Module QuadraticMap SignType
open scoped BigOperators

/-- A choice of `SignType`-weights in Sylvester's diagonalization of a quadratic form.

This is auxiliary data: it exists by `QuadraticForm.equivalent_signType_weighted_sum_squared`,
but is not canonical (it is chosen noncomputably). -/
noncomputable def signTypeWeights {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (q : QuadraticForm ℝ E) : Fin (finrank ℝ E) → SignType :=
  Classical.choose (QuadraticForm.equivalent_signType_weighted_sum_squared q)

lemma equivalent_weightedSumSquares_signTypeWeights {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (q : QuadraticForm ℝ E) :
    QuadraticMap.Equivalent q
      (QuadraticMap.weightedSumSquares ℝ fun i => ((signTypeWeights q i : SignType) : ℝ)) :=
  Classical.choose_spec (QuadraticForm.equivalent_signType_weighted_sum_squared q)

/-- A *chosen* signature `(pos, neg, zero)` of a real quadratic form, defined using
`signTypeWeights`. -/
noncomputable def signatureChoice {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (q : QuadraticForm ℝ E) : Signature := by
  let w := signTypeWeights q
  refine ⟨
    (univ.filter fun i => w i = SignType.pos).card,
    (univ.filter fun i => w i = SignType.neg).card,
    (univ.filter fun i => w i = 0).card⟩

lemma signatureChoice_le_finrank {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (q : QuadraticForm ℝ E) :
    (signatureChoice q).neg ≤ finrank ℝ E ∧ (signatureChoice q).pos ≤ finrank ℝ E ∧
      (signatureChoice q).zero ≤ finrank ℝ E := by
  constructor
  · simp [signatureChoice, signTypeWeights]
    simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin (finrank ℝ E))))
      (p := fun i => signTypeWeights q i = SignType.neg))
  constructor
  · simp [signatureChoice, signTypeWeights]
    simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin (finrank ℝ E))))
      (p := fun i => signTypeWeights q i = SignType.pos))
  · simp [signatureChoice, signTypeWeights]
    simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin (finrank ℝ E))))
      (p := fun i => signTypeWeights q i = 0))

/-!
### Canonical signature equals Sylvester choice

Using the diagonal computation for `weightedSumSquares` and the Sylvester diagonalization existence
theorem, we show that the canonical signature defined via `posIndex` agrees with the chosen
`signatureChoice`.
-/

section SylvesterBridge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

theorem posDim_eq_signatureChoice_pos (q : QuadraticForm ℝ E) :
    q.posDim = (signatureChoice q).pos := by
  let w : Fin (finrank ℝ E) → SignType := signTypeWeights q
  let Qd : QuadraticForm ℝ (Fin (finrank ℝ E) → ℝ) :=
    (QuadraticMap.weightedSumSquares ℝ fun i : Fin (finrank ℝ E) => (w i : ℝ))
  have heq : q.Equivalent Qd := by
    simpa [Qd, w, signTypeWeights] using (equivalent_weightedSumSquares_signTypeWeights q)
  have hpos : q.posDim = Qd.posDim :=
    posDim_eq_of_equivalent (E := E) (E₂ := Fin (finrank ℝ E) → ℝ) heq
  have hposd :
      Qd.posDim = (Finset.univ.filter fun i : Fin (finrank ℝ E) => w i = SignType.pos).card := by
    simpa [Qd] using (posDim_weightedSumSquares_signType (n := finrank ℝ E) w)
  simpa [signatureChoice, w, signTypeWeights] using hpos.trans hposd

theorem negDim_eq_signatureChoice_neg (q : QuadraticForm ℝ E) :
    q.negDim = (signatureChoice q).neg := by
  let w : Fin (finrank ℝ E) → SignType := signTypeWeights q
  let Qd : QuadraticForm ℝ (Fin (finrank ℝ E) → ℝ) :=
    (QuadraticMap.weightedSumSquares ℝ fun i : Fin (finrank ℝ E) => (w i : ℝ))
  have heq : q.Equivalent Qd := by
    simpa [Qd, w, signTypeWeights] using (equivalent_weightedSumSquares_signTypeWeights q)
  have hneg : q.negDim = Qd.negDim :=
    negDim_eq_of_equivalent (E := E) (E₂ := Fin (finrank ℝ E) → ℝ) heq
  have hnegd :
      Qd.negDim = (Finset.univ.filter fun i : Fin (finrank ℝ E) => w i = SignType.neg).card := by
    simpa [Qd] using (negDim_weightedSumSquares_signType (n := finrank ℝ E) w)
  simpa [signatureChoice, w, signTypeWeights] using hneg.trans hnegd

theorem zeroDim_eq_signatureChoice_zero (q : QuadraticForm ℝ E) :
    q.zeroDim = (signatureChoice q).zero := by
  let w : Fin (finrank ℝ E) → SignType := signTypeWeights q
  let Qd : QuadraticForm ℝ (Fin (finrank ℝ E) → ℝ) :=
    (QuadraticMap.weightedSumSquares ℝ fun i : Fin (finrank ℝ E) => (w i : ℝ))
  have heq : q.Equivalent Qd := by
    simpa [Qd, w, signTypeWeights] using (equivalent_weightedSumSquares_signTypeWeights q)
  have hzero : q.zeroDim = Qd.zeroDim :=
    zeroDim_eq_of_equivalent (E := E) (E₂ := Fin (finrank ℝ E) → ℝ) heq
  have hzerod :
      Qd.zeroDim = (Finset.univ.filter fun i : Fin (finrank ℝ E) => w i = 0).card := by
    simpa [Qd] using (zeroDim_weightedSumSquares_signType (n := finrank ℝ E) w)
  simpa [signatureChoice, w, signTypeWeights] using hzero.trans hzerod

theorem signature_eq_signatureChoice (q : QuadraticForm ℝ E) :
    q.signature = signatureChoice q := by
  ext
  · simpa using posDim_eq_signatureChoice_pos (E := E) q
  · simpa using negDim_eq_signatureChoice_neg (E := E) q
  · simpa using zeroDim_eq_signatureChoice_zero (E := E) q

theorem signatureChoice_eq_of_equivalent {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂]
    [FiniteDimensional ℝ E₂] {Q : QuadraticForm ℝ E} {Q₂ : QuadraticForm ℝ E₂}
    (h : Q.Equivalent Q₂) :
    signatureChoice Q = signatureChoice Q₂ := by
  calc
    signatureChoice Q = Q.signature := (signature_eq_signatureChoice (E := E) Q).symm
    _ = Q₂.signature := signature_eq_of_equivalent (E := E) (E₂ := E₂) h
    _ = signatureChoice Q₂ := signature_eq_signatureChoice (E := E₂) Q₂

end SylvesterBridge

end QuadraticForm
