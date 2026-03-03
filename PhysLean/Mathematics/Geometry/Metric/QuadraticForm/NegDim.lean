/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Inertia indices for real quadratic forms

This file defines canonical inertia data for a real quadratic form on a finite-dimensional real
vector space.

The main construction is `QuadraticForm.posIndex`, the maximal dimension of a submodule on which a
quadratic form is positive definite. From this we define the canonical indices
`QuadraticForm.posDim`, `QuadraticForm.negDim`, `QuadraticForm.zeroDim`, and the canonical
`QuadraticForm.signature`.

These constructions are invariant under `QuadraticForm.Equivalent` and do not depend on a choice of
diagonalization.

## Main definitions

- `QuadraticForm.posIndex`: maximal dimension of a submodule where `Q` is positive definite
- `QuadraticForm.posDim`: positive index of inertia (defined as `posIndex Q`)
- `QuadraticForm.negDim`: negative index of inertia (defined as `posIndex (-Q)`)
- `QuadraticForm.zeroDim`: nullity, defined so `posDim + negDim + zeroDim = finrank`
- `QuadraticForm.signature`: the triple `(posDim, negDim, zeroDim)`

## Implementation notes

We also define noncanonical auxiliary data (`QuadraticForm.signTypeWeights`,
`QuadraticForm.signatureChoice`) by choosing Sylvester diagonalization weights, for bridging to
`QuadraticForm.equivalent_signType_weighted_sum_squared` in
`Mathlib.LinearAlgebra.QuadraticForm.Real`. These choices are not claimed to be canonical.

## Tags

quadratic form, inertia, signature, Sylvester law, index
-/

namespace QuadraticForm

open Finset Module QuadraticMap SignType
open scoped BigOperators

/-! ### Signature and indices -/

/-- A (finite-dimensional) real quadratic form has a signature `(pos, neg, zero)` given by
Sylvester's law of inertia: the numbers of positive, negative, and zero squares in a diagonal
representation. -/
@[ext] structure Signature where
  pos : ℕ
  neg : ℕ
  zero : ℕ

namespace Signature

/-- Alias for the `zero` component (common terminology: nullity). -/
abbrev nullity (s : Signature) : ℕ := s.zero

end Signature

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
`signTypeWeights`.

This is **not** asserted to be canonical/invariant in this file; it is primarily a bridge to
Mathlib's existence result (Sylvester diagonalization). -/
noncomputable def signatureChoice {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (q : QuadraticForm ℝ E) : Signature := by
  let w := signTypeWeights q
  refine ⟨
    (univ.filter fun i => w i = SignType.pos).card,
    (univ.filter fun i => w i = SignType.neg).card,
    (univ.filter fun i => w i = 0).card⟩

/-!
We will define canonical indices (`posDim`, `negDim`, `zeroDim`, `signature`) below using `posIndex`,
and we keep `signatureChoice` only as auxiliary data.
-/

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

/-- For a standard basis vector in a weighted sum of squares, only one term in the sum is nonzero. -/
lemma QuadraticMap.weightedSumSquares_basis_vector {E : Type*} [AddCommGroup E] [Module ℝ E]
    {weights : Fin (finrank ℝ E) → ℝ} {i : Fin (finrank ℝ E)} (v : Fin (finrank ℝ E) → ℝ)
    (hv : ∀ j, v j = if j = i then 1 else 0) :
    QuadraticMap.weightedSumSquares ℝ weights v = weights i := by
  simp only [QuadraticMap.weightedSumSquares_apply]
  rw [Finset.sum_eq_single i]
  · simp only [hv i, ↓reduceIte, mul_one, smul_eq_mul]
  · intro j _ hj
    simp only [hv j, if_neg hj, mul_zero, smul_eq_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, smul_eq_mul, mul_eq_zero, or_self,
      IsEmpty.forall_iff]

/-- When a quadratic form is equivalent to a weighted sum of squares, negative weights correspond
to vectors where the form takes negative values. -/
lemma neg_weight_implies_neg_value {E : Type*} [AddCommGroup E] [Module ℝ E]
    {q : QuadraticForm ℝ E} {w : Fin (finrank ℝ E) → SignType}
    (h_equiv : QuadraticMap.Equivalent q (QuadraticMap.weightedSumSquares ℝ fun i => (w i : ℝ)))
    {i : Fin (finrank ℝ E)} (hi : w i = SignType.neg) :
    ∃ v : E, v ≠ 0 ∧ q v < 0 := by
  let f := Classical.choice h_equiv
  let v_std : Fin (finrank ℝ E) → ℝ := fun j => if j = i then 1 else 0
  let v := f.symm v_std
  have hv_ne_zero : v ≠ 0 := by
    intro h
    have : f v = f 0 := by rw [h]
    have : f (f.symm v_std) = f 0 := by rw [← this]
    have : v_std = 0 := by
      rw [← f.apply_symm_apply v_std]
      exact Eq.trans this (map_zero f)
    have : v_std i = 0 := by rw [this]; rfl
    simp only [↓reduceIte, one_ne_zero, v_std] at this
  have hq_neg : q v < 0 := by
    have heq : q v = QuadraticMap.weightedSumSquares ℝ (fun j => (w j : ℝ)) v_std :=
      QuadraticMap.IsometryEquiv.map_app f.symm v_std
    have hw : QuadraticMap.weightedSumSquares ℝ (fun j => (w j : ℝ)) v_std = (w i : ℝ) := by
      apply QuadraticMap.weightedSumSquares_basis_vector v_std
      intro j; simp only [v_std]
    rw [heq, hw]
    have : (w i : ℝ) = -1 := by
      simp only [hi, SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one]
    rw [this]
    exact neg_one_lt_zero
  exact ⟨v, hv_ne_zero, hq_neg⟩

/-- A positive definite quadratic form cannot have any negative weights in its diagonalization. -/
lemma posDef_no_neg_weights {E : Type*} [AddCommGroup E] [Module ℝ E]
    {q : QuadraticForm ℝ E} (hq : q.PosDef) {w : Fin (finrank ℝ E) → SignType}
    (h_equiv : QuadraticMap.Equivalent q (QuadraticMap.weightedSumSquares ℝ fun i => (w i : ℝ))) :
    ∀ i, w i ≠ SignType.neg := by
  intro i hi
  obtain ⟨v, hv_ne_zero, hq_neg⟩ := QuadraticForm.neg_weight_implies_neg_value h_equiv hi
  have hq_pos : 0 < q v := hq v hv_ne_zero
  exact lt_asymm hq_neg hq_pos

/-!
### Inertia uniqueness (canonical indices)

We want the signature counts to be invariants (independent
of the choice of diagonalization). We provide the key intermediate notion of
the **positive index**, defined as the maximum dimension of a subspace on which the form is
positive definite.

In this file we prove invariance of this index under `QuadraticForm.Equivalent`. In a subsequent
step, one computes this index for diagonal `weightedSumSquares` forms, and deduces uniqueness of
the inertia counts.
-/

section InertiaUniqueness

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- `IsPosDefOn Q W` means that the restriction of `Q` to the submodule `W` is positive definite. -/
def IsPosDefOn (Q : QuadraticForm ℝ V) (W : Submodule ℝ V) : Prop :=
  (Q.comp W.subtype).PosDef

/-- The finset of candidate dimensions of positive-definite submodules of a quadratic form. -/
private noncomputable def posIndexCandidates (Q : QuadraticForm ℝ V) : Finset ℕ := by
  classical
  exact (Finset.range (finrank ℝ V + 1)).filter fun k =>
    ∃ W : Submodule ℝ V, finrank ℝ W = k ∧ IsPosDefOn (V := V) Q W

omit [FiniteDimensional ℝ V] in
private lemma posIndexCandidates_nonempty (Q : QuadraticForm ℝ V) :
    (posIndexCandidates (V := V) Q).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  refine Finset.mem_filter.2 ?_
  refine ⟨by simp, ?_⟩
  refine ⟨(⊥ : Submodule ℝ V), by simp, ?_⟩
  intro x hx
  exfalso
  exact hx (Subsingleton.elim x 0)

/-- The positive index of a real quadratic form: the maximal dimension of a subspace on which the
form is positive definite. -/
noncomputable def posIndex (Q : QuadraticForm ℝ V) : ℕ := by
  classical
  exact (posIndexCandidates (V := V) Q).max' (posIndexCandidates_nonempty (V := V) Q)

omit [FiniteDimensional ℝ V] in
lemma posIndex_spec (Q : QuadraticForm ℝ V) :
    ∃ W : Submodule ℝ V, finrank ℝ W = posIndex (V := V) Q ∧ IsPosDefOn (V := V) Q W := by
  classical
  have hmem :
      posIndex (V := V) Q ∈ posIndexCandidates (V := V) Q := by
    simpa [posIndex] using
      (Finset.max'_mem _ (posIndexCandidates_nonempty (V := V) Q))
  rcases (Finset.mem_filter.1 hmem).2 with ⟨W, hW, hWpos⟩
  exact ⟨W, hW, hWpos⟩

lemma le_posIndex_of_exists {Q : QuadraticForm ℝ V} {k : ℕ}
    (hk : ∃ W : Submodule ℝ V, finrank ℝ W = k ∧ IsPosDefOn (V := V) Q W) :
    k ≤ posIndex (V := V) Q := by
  classical
  have hk_mem : k ∈ posIndexCandidates (V := V) Q := by
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, hk⟩
    rcases hk with ⟨W, hW, -⟩
    have hk_le : k ≤ finrank ℝ V := by
      simpa [hW] using (Submodule.finrank_le (R := ℝ) (M := V) W)
    simpa [posIndexCandidates] using (Finset.mem_range.2 (Nat.lt_succ_of_le hk_le))
  simpa [posIndex] using Finset.le_max' (posIndexCandidates (V := V) Q) k hk_mem

/- If `Q` and `Q₂` are equivalent, then `posIndex Q ≤ posIndex Q₂`. -/
omit [FiniteDimensional ℝ V] in
lemma posIndex_le_of_equivalent {V₂ : Type*} [AddCommGroup V₂] [Module ℝ V₂]
    [FiniteDimensional ℝ V₂] {Q : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ V₂}
    (h : Q.Equivalent Q₂) :
    posIndex (V := V) Q ≤ posIndex (V := V₂) Q₂ := by
  classical
  rcases h with ⟨e⟩
  rcases posIndex_spec (Q := Q) with ⟨W, hWfin, hWpos⟩
  let f : V →ₗ[ℝ] V₂ := (e.toLinearEquiv : V ≃ₗ[ℝ] V₂).toLinearMap
  have hf_inj : Function.Injective f := e.toLinearEquiv.injective
  let W₂ : Submodule ℝ V₂ := W.map f
  have hfinrank : finrank ℝ W₂ = finrank ℝ W := by
    simpa [W₂] using (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf_inj W)).symm
  have hW₂pos : IsPosDefOn (V := V₂) Q₂ W₂ := by
    intro x hx
    rcases x with ⟨xv, hxv⟩
    have hx0 : (⟨xv, by simpa [W₂] using hxv⟩ : W.map f) ≠ 0 := by
      intro h0
      apply hx
      ext
      simpa using congrArg Subtype.val h0
    let eqv := Submodule.equivMapOfInjective f hf_inj W
    set x' : W.map f := ⟨xv, by simpa [W₂] using hxv⟩
    have hx' : (eqv.symm x') ≠ 0 := by
      intro h0
      apply hx0
      have := congrArg eqv h0
      simpa using this
    have hpos' : 0 < (Q.comp W.subtype) (eqv.symm x') := hWpos _ hx'
    have hxmap : f ((eqv.symm x' : W) : V) = (x' : V₂) :=
      Submodule.map_equivMapOfInjective_symm_apply f hf_inj W x'
    have heq : Q₂ (x' : V₂) = Q ((eqv.symm x' : W) : V) := by
      have : Q₂ (f ((eqv.symm x' : W) : V)) = Q ((eqv.symm x' : W) : V) := by
        simp [f]
      simpa [hxmap] using this
    simpa [IsPosDefOn, QuadraticMap.comp_apply, heq, x'] using hpos'
  have hk :
      ∃ U : Submodule ℝ V₂, finrank ℝ U = posIndex (V := V) Q ∧ IsPosDefOn (V := V₂) Q₂ U :=
    ⟨W₂, by simp [hWfin, hfinrank], hW₂pos⟩
  exact le_posIndex_of_exists (V := V₂) hk

/-- `posIndex` is invariant under equivalence of quadratic forms. -/
theorem posIndex_eq_of_equivalent {V₂ : Type*} [AddCommGroup V₂] [Module ℝ V₂]
    [FiniteDimensional ℝ V₂] {Q : QuadraticForm ℝ V} {Q₂ : QuadraticForm ℝ V₂}
    (h : Q.Equivalent Q₂) :
    posIndex (V := V) Q = posIndex (V := V₂) Q₂ := by
  refine le_antisymm (posIndex_le_of_equivalent (V := V) (V₂ := V₂) (Q := Q) (Q₂ := Q₂) h) ?_
  rcases h with ⟨e⟩
  exact posIndex_le_of_equivalent (V := V₂) (V₂ := V) (Q := Q₂) (Q₂ := Q) ⟨e.symm⟩

end InertiaUniqueness

/-! ### Canonical signature and indices -/

section Canonical

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

lemma posIndex_le_finrank (Q : QuadraticForm ℝ E) :
    posIndex (V := E) Q ≤ finrank ℝ E := by
  rcases posIndex_spec (Q := Q) with ⟨W, hW, -⟩
  have : finrank ℝ W ≤ finrank ℝ E := Submodule.finrank_le (R := ℝ) (M := E) W
  simpa [hW] using this

/-- The positive index of inertia of a real quadratic form (canonical). -/
noncomputable def posDim (Q : QuadraticForm ℝ E) : ℕ :=
  posIndex (V := E) Q

/-- The negative index of inertia of a real quadratic form (canonical). -/
noncomputable def negDim (Q : QuadraticForm ℝ E) : ℕ :=
  posIndex (V := E) (-Q)

omit [FiniteDimensional ℝ E] in
@[simp]
lemma posDim_def (Q : QuadraticForm ℝ E) : Q.posDim = posIndex (V := E) Q := rfl

omit [FiniteDimensional ℝ E] in
@[simp]
lemma negDim_def (Q : QuadraticForm ℝ E) : Q.negDim = posIndex (V := E) (-Q) := rfl

lemma posDim_le_finrank (Q : QuadraticForm ℝ E) : Q.posDim ≤ finrank ℝ E :=
  posIndex_le_finrank (E := E) Q

lemma negDim_le_finrank (Q : QuadraticForm ℝ E) : Q.negDim ≤ finrank ℝ E :=
  posIndex_le_finrank (E := E) (-Q)

omit [FiniteDimensional ℝ E] in
@[simp] lemma posDim_neg (Q : QuadraticForm ℝ E) : (-Q).posDim = Q.negDim := rfl

omit [FiniteDimensional ℝ E] in
lemma negDim_neg (Q : QuadraticForm ℝ E) : (-Q).negDim = Q.posDim := by
  simp [negDim, posDim]

lemma posDim_add_negDim_le_finrank (Q : QuadraticForm ℝ E) :
    Q.posDim + Q.negDim ≤ finrank ℝ E := by
  rcases posIndex_spec (Q := Q) with ⟨Wpos, hWpos, hpos⟩
  rcases posIndex_spec (Q := -Q) with ⟨Wneg, hWneg, hneg⟩
  have hdisj : Disjoint Wpos Wneg := by
    rw [Submodule.disjoint_def]
    intro x hxpos hxneg
    by_contra hx0
    have hxpos' : 0 < Q x := by
      have : 0 < (Q.comp Wpos.subtype) ⟨x, hxpos⟩ := hpos ⟨x, hxpos⟩ (by simpa using hx0)
      simpa [IsPosDefOn, QuadraticMap.comp_apply] using this
    have hxneg' : Q x < 0 := by
      have : 0 < ((-Q).comp Wneg.subtype) ⟨x, hxneg⟩ := hneg ⟨x, hxneg⟩ (by simpa using hx0)
      have : 0 < (-Q) x := by simpa [IsPosDefOn, QuadraticMap.comp_apply] using this
      simpa using (neg_pos.mp this)
    exact (not_lt_of_gt hxpos') hxneg'
  have hdim : finrank ℝ Wpos + finrank ℝ Wneg ≤ finrank ℝ E :=
    Submodule.finrank_add_finrank_le_of_disjoint hdisj
  simpa [posDim, negDim, hWpos, hWneg] using hdim

/-- The nullity of a real quadratic form, defined so that `pos + neg + zero = finrank`. -/
noncomputable def zeroDim (Q : QuadraticForm ℝ E) : ℕ :=
  finrank ℝ E - Q.posDim - Q.negDim

omit [FiniteDimensional ℝ E] in
@[simp]
lemma zeroDim_def (Q : QuadraticForm ℝ E) :
    Q.zeroDim = finrank ℝ E - Q.posDim - Q.negDim := rfl

omit [FiniteDimensional ℝ E] in
lemma zeroDim_neg (Q : QuadraticForm ℝ E) : (-Q).zeroDim = Q.zeroDim := by
  -- Both sides reduce to `finrank - (posIndex Q + posIndex (-Q))`.
  simp [zeroDim, posDim, negDim, Nat.sub_sub, Nat.add_comm]

/-- The signature `(pos, neg, zero)` of a real quadratic form (canonical). -/
noncomputable def signature (Q : QuadraticForm ℝ E) : Signature :=
  ⟨Q.posDim, Q.negDim, Q.zeroDim⟩

omit [FiniteDimensional ℝ E] in
@[simp]
lemma signature_pos (Q : QuadraticForm ℝ E) : Q.signature.pos = Q.posDim := rfl

omit [FiniteDimensional ℝ E] in
@[simp]
lemma signature_neg (Q : QuadraticForm ℝ E) : Q.signature.neg = Q.negDim := rfl

omit [FiniteDimensional ℝ E] in
@[simp]
lemma signature_zero (Q : QuadraticForm ℝ E) : Q.signature.zero = Q.zeroDim := rfl

omit [FiniteDimensional ℝ E] in
@[simp]
lemma signature_def (Q : QuadraticForm ℝ E) :
    Q.signature = ⟨Q.posDim, Q.negDim, Q.zeroDim⟩ := rfl

lemma posDim_add_negDim_add_zeroDim (Q : QuadraticForm ℝ E) :
    Q.posDim + Q.negDim + Q.zeroDim = finrank ℝ E := by
  set n : ℕ := finrank ℝ E
  set p : ℕ := Q.posDim
  set m : ℕ := Q.negDim
  have hp : p ≤ n := by
    simpa [p, n] using (posDim_le_finrank (E := E) Q)
  have hpm : p + m ≤ n := by
    simpa [p, m, n] using (posDim_add_negDim_le_finrank (E := E) Q)
  have hm : m ≤ n - p := by
    exact (Nat.le_sub_iff_add_le hp).2 (by simpa [Nat.add_comm, p, m, n] using hpm)
  calc
    Q.posDim + Q.negDim + Q.zeroDim
        = p + m + (n - p - m) := by simp [zeroDim, n, p, m]
    _ = p + (m + ((n - p) - m)) := by
      simp [Nat.add_assoc]
    _ = p + (n - p) := by
      simp [Nat.add_sub_of_le hm]
    _ = n := by
      simp [Nat.add_sub_of_le hp]

lemma signature_sum (Q : QuadraticForm ℝ E) :
    Q.signature.pos + Q.signature.neg + Q.signature.zero = finrank ℝ E := by
  simpa using (posDim_add_negDim_add_zeroDim (E := E) Q)

/-- For a positive definite quadratic form, `posDim = finrank`. -/
theorem posDim_posDef {Q : QuadraticForm ℝ E} (hQ : Q.PosDef) :
    Q.posDim = finrank ℝ E := by
  apply le_antisymm (posDim_le_finrank (E := E) Q)
  have hk :
      ∃ W : Submodule ℝ E, finrank ℝ W = finrank ℝ E ∧ IsPosDefOn (V := E) Q W := by
    refine ⟨(⊤ : Submodule ℝ E), by simp, ?_⟩
    intro x hx
    have hx' : (x : E) ≠ 0 := by
      intro h0
      apply hx
      ext
      simp [h0]
    simpa [IsPosDefOn, QuadraticMap.comp_apply] using (hQ (x : E) hx')
  have : finrank ℝ E ≤ posIndex (V := E) Q :=
    le_posIndex_of_exists (V := E) (k := finrank ℝ E) hk
  simpa [posDim] using this

/-- For a positive definite quadratic form, `negDim = 0`. -/
theorem negDim_posDef {Q : QuadraticForm ℝ E} (hQ : Q.PosDef) : Q.negDim = 0 := by
  rcases posIndex_spec (Q := -Q) with ⟨W, hW, hWpos⟩
  have hWbot : W = ⊥ := by
    ext x
    constructor
    · intro hx
      by_contra hx0
      have hpos' : 0 < ((-Q).comp W.subtype) ⟨x, hx⟩ := hWpos ⟨x, hx⟩ (by
        intro h0; apply hx0; simpa using congrArg Subtype.val h0)
      have hneg' : Q x < 0 := by
        have : 0 < (-Q) x := by simpa [QuadraticMap.comp_apply] using hpos'
        simpa using (neg_pos.mp this)
      have hposQ : 0 < Q x := hQ x hx0
      exact (not_lt_of_gt hposQ) hneg'
    · intro hx
      have hx0 : x = 0 := by
        simpa [Submodule.mem_bot] using hx
      simp [hx0]
  have hfin0 : finrank ℝ W = 0 := by simp [hWbot]
  have : posIndex (V := E) (-Q) = 0 := by simpa [hW] using hfin0
  simp [negDim, this]

/-- For a positive definite quadratic form, `zeroDim = 0`. -/
theorem zeroDim_posDef {Q : QuadraticForm ℝ E} (hQ : Q.PosDef) :
    Q.zeroDim = 0 := by
  have hpos : Q.posDim = finrank ℝ E := posDim_posDef (E := E) hQ
  have hneg : Q.negDim = 0 := negDim_posDef (E := E) hQ
  have hpos' : posIndex (V := E) Q = finrank ℝ E := by simpa [posDim] using hpos
  have hneg' : posIndex (V := E) (-Q) = 0 := by simpa [negDim] using hneg
  simp [zeroDim, posDim, negDim, hpos', hneg']

omit [FiniteDimensional ℝ E] in
lemma Equivalent.neg {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [FiniteDimensional ℝ E₂]
    {Q : QuadraticForm ℝ E} {Q₂ : QuadraticForm ℝ E₂} (h : Q.Equivalent Q₂) :
    (-Q).Equivalent (-Q₂) := by
  rcases h with ⟨e⟩
  refine ⟨?_⟩
  refine
    { toLinearEquiv := e.toLinearEquiv
      map_app' := fun x => ?_ }
  simp

theorem posDim_eq_of_equivalent {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [FiniteDimensional ℝ E₂]
    {Q : QuadraticForm ℝ E} {Q₂ : QuadraticForm ℝ E₂} (h : Q.Equivalent Q₂) :
    Q.posDim = Q₂.posDim := by
  simp [posDim, posIndex_eq_of_equivalent (Q := Q) (Q₂ := Q₂) h]

theorem negDim_eq_of_equivalent {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [FiniteDimensional ℝ E₂]
    {Q : QuadraticForm ℝ E} {Q₂ : QuadraticForm ℝ E₂} (h : Q.Equivalent Q₂) :
    Q.negDim = Q₂.negDim := by
  have h' : (-Q).Equivalent (-Q₂) := Equivalent.neg (E := E) (E₂ := E₂) h
  simp [negDim, posIndex_eq_of_equivalent (Q := -Q) (Q₂ := -Q₂) h']

theorem zeroDim_eq_of_equivalent {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [FiniteDimensional ℝ E₂]
    {Q : QuadraticForm ℝ E} {Q₂ : QuadraticForm ℝ E₂} (h : Q.Equivalent Q₂) :
    Q.zeroDim = Q₂.zeroDim := by
  rcases h with ⟨e⟩
  have hfin : finrank ℝ E = finrank ℝ E₂ := LinearEquiv.finrank_eq e.toLinearEquiv
  have hposI : posIndex (V := E) Q = posIndex (V := E₂) Q₂ :=
    posIndex_eq_of_equivalent (Q := Q) (Q₂ := Q₂) ⟨e⟩
  have hnegI : posIndex (V := E) (-Q) = posIndex (V := E₂) (-Q₂) :=
    posIndex_eq_of_equivalent (Q := -Q) (Q₂ := -Q₂) (Equivalent.neg (E := E) (E₂ := E₂) ⟨e⟩)
  simp [zeroDim, posDim, negDim, hfin, hposI, hnegI]

theorem signature_eq_of_equivalent {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [FiniteDimensional ℝ E₂]
    {Q : QuadraticForm ℝ E} {Q₂ : QuadraticForm ℝ E₂} (h : Q.Equivalent Q₂) :
    Q.signature = Q₂.signature := by
  rcases h with ⟨e⟩
  have hfin : finrank ℝ E = finrank ℝ E₂ := LinearEquiv.finrank_eq e.toLinearEquiv
  have hposI : posIndex (V := E) Q = posIndex (V := E₂) Q₂ :=
    posIndex_eq_of_equivalent (Q := Q) (Q₂ := Q₂) ⟨e⟩
  have hnegI : posIndex (V := E) (-Q) = posIndex (V := E₂) (-Q₂) :=
    posIndex_eq_of_equivalent (Q := -Q) (Q₂ := -Q₂) (Equivalent.neg (E := E) (E₂ := E₂) ⟨e⟩)
  ext <;> simp [signature, posDim, negDim, zeroDim, hfin, hposI, hnegI]

end Canonical

/-!
### Diagonal computation

We compute the canonical indices for the diagonal form `weightedSumSquares` with `SignType` weights.
This is the key bridge between the canonical `posIndex`-based definition and Mathlib's Sylvester
diagonalization existence theorem.
-/

section Diagonal

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The diagonal quadratic form with `SignType` weights `w`, i.e. the weighted sum of squares
with weights in `{ -1, 0, 1 }`. -/
abbrev diagForm (w : Fin n → SignType) : QuadraticForm ℝ (Fin n → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ fun i => (w i : ℝ)

/-- The set of indices where `w` takes the value `s`. -/
def signSet (s : SignType) (w : Fin n → SignType) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i = s

/-- The set of indices where `w` is positive. -/
abbrev posSet (w : Fin n → SignType) : Finset (Fin n) :=
  signSet (n := n) SignType.pos w

/-- The set of indices where `w` is negative. -/
abbrev negSet (w : Fin n → SignType) : Finset (Fin n) :=
  signSet (n := n) SignType.neg w

/-- The set of indices where `w` is zero. -/
abbrev zeroSet (w : Fin n → SignType) : Finset (Fin n) :=
  signSet (n := n) 0 w

lemma mem_posSet {w : Fin n → SignType} {i : Fin n} :
    i ∈ posSet (n := n) w ↔ w i = SignType.pos := by
  simp [posSet, signSet]

lemma mem_negSet {w : Fin n → SignType} {i : Fin n} :
    i ∈ negSet (n := n) w ↔ w i = SignType.neg := by
  simp [negSet, signSet]

lemma mem_zeroSet {w : Fin n → SignType} {i : Fin n} :
    i ∈ zeroSet (n := n) w ↔ w i = 0 := by
  simp [zeroSet, signSet]

lemma posSet_neg (w : Fin n → SignType) :
    posSet (n := n) (fun i => -w i) = negSet (n := n) w := by
  ext i
  cases hi : w i <;> simp [posSet, negSet, signSet, hi]

/-- The submodule of vectors supported on the positive-weight coordinates. -/
def supportedOnPos (w : Fin n → SignType) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∀ i, w i ≠ SignType.pos → v i = 0}
  zero_mem' := by intro i hi; simp
  add_mem' := by
    intro v₁ v₂ hv₁ hv₂ i hi
    simp [Pi.add_apply, hv₁ i hi, hv₂ i hi]
  smul_mem' := by
    intro a v hv i hi
    simp [Pi.smul_apply, hv i hi]

@[simp] lemma mem_supportedOnPos {w : Fin n → SignType} {v : Fin n → ℝ} :
    v ∈ supportedOnPos (n := n) w ↔ ∀ i, w i ≠ SignType.pos → v i = 0 :=
  Iff.rfl

/-- Restriction of a vector to the positive-weight coordinates. -/
def restrictPos (w : Fin n → SignType) :
    (Fin n → ℝ) →ₗ[ℝ] ({i // i ∈ posSet (n := n) w} → ℝ) where
  toFun v i := v i.1
  map_add' := by intro v₁ v₂; ext i; rfl
  map_smul' := by intro a v; ext i; rfl

@[simp] lemma restrictPos_apply {w : Fin n → SignType} (v : Fin n → ℝ)
    (i : {i // i ∈ posSet (n := n) w}) :
    restrictPos (n := n) w v i = v i.1 := rfl

/-- If a vector has no positive-weight coordinates, then its value under `diagForm w` is nonpositive. -/
lemma diagForm_nonpos_of_no_pos {w : Fin n → SignType} {v : Fin n → ℝ}
    (hv : ∀ i, w i = SignType.pos → v i = 0) :
    diagForm (n := n) w v ≤ 0 := by
  simp only [diagForm, QuadraticMap.weightedSumSquares_apply]
  refine Finset.sum_nonpos ?_
  intro i _
  cases hwi : w i <;> simp [hwi, hv i, mul_self_nonneg]

/-- On `supportedOnPos w`, the diagonal form `diagForm w` is positive definite. -/
lemma isPosDefOn_diagForm_supportedOnPos (w : Fin n → SignType) :
    IsPosDefOn (V := Fin n → ℝ) (diagForm (n := n) w) (supportedOnPos (n := n) w) := by
  classical
  intro v hv0
  -- pick a coordinate where `v` is nonzero
  have hv' : ∃ i, (v : Fin n → ℝ) i ≠ 0 := by
    by_contra h
    apply hv0
    ext i
    have : (v : Fin n → ℝ) i = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    simpa using this
  rcases hv' with ⟨i, hi⟩
  have hwpos : w i = SignType.pos := by
    by_contra hne
    have : (v : Fin n → ℝ) i = 0 := by
      exact (mem_supportedOnPos (n := n) (w := w) |>.1 v.property) i hne
    exact hi this
  have hterm_pos : 0 < (v : Fin n → ℝ) i ^ 2 := by
    simpa [pow_two] using sq_pos_of_ne_zero hi
  have hle :
      (v : Fin n → ℝ) i ^ 2 ≤ diagForm (n := n) w (v : Fin n → ℝ) := by
    simp only [diagForm, QuadraticMap.weightedSumSquares_apply]
    have hnonneg :
        ∀ j : Fin n, 0 ≤ ((w j : ℝ) • ((v : Fin n → ℝ) j * (v : Fin n → ℝ) j)) := by
      intro j
      by_cases hj : w j = SignType.pos
      · simp [hj, mul_self_nonneg]
      · have : (v : Fin n → ℝ) j = 0 := (mem_supportedOnPos (n := n) (w := w)).1 v.property j hj
        simp [this]
    have : ((w i : ℝ) • ((v : Fin n → ℝ) i * (v : Fin n → ℝ) i))
        ≤ ∑ j : Fin n, (w j : ℝ) • ((v : Fin n → ℝ) j * (v : Fin n → ℝ) j) := by
      refine Finset.single_le_sum (fun j _ => hnonneg j) ?_
      simp
    simpa [hwpos, pow_two] using this
  exact lt_of_lt_of_le hterm_pos hle

/-- The submodule `supportedOnPos w` is linearly equivalent to functions on the positive index set. -/
noncomputable def supportedOnPosEquiv (w : Fin n → SignType) :
    supportedOnPos (n := n) w ≃ₗ[ℝ] ({i // i ∈ posSet (n := n) w} → ℝ) := by
  classical
  refine
    { toLinearMap :=
        { toFun := fun v i => (v : Fin n → ℝ) i.1
          map_add' := by intro v₁ v₂; ext i; rfl
          map_smul' := by intro a v; ext i; rfl }
      invFun := fun u =>
        ⟨fun i => if h : i ∈ posSet (n := n) w then u ⟨i, h⟩ else 0, by
          intro i hi
          by_cases h : i ∈ posSet (n := n) w
          · exfalso
            exact hi ((mem_posSet (n := n) (w := w)).1 h)
          · simp [h]⟩
      left_inv := by
        intro v
        ext i
        by_cases h : i ∈ posSet (n := n) w
        · have : w i = SignType.pos := (mem_posSet (n := n) (w := w)).1 h
          simp [h]
        · have : w i ≠ SignType.pos := by
            intro hpos
            exact h ((mem_posSet (n := n) (w := w)).2 hpos)
          have : (v : Fin n → ℝ) i = 0 :=
            (mem_supportedOnPos (n := n) (w := w)).1 v.property i this
          simp [h, this]
      right_inv := by
        intro u
        ext i
        simp }

lemma finrank_supportedOnPos (w : Fin n → SignType) :
    finrank ℝ (supportedOnPos (n := n) w) = (posSet (n := n) w).card := by
  classical
  have h :
      finrank ℝ ({i // i ∈ posSet (n := n) w} → ℝ) = (posSet (n := n) w).card := by
    -- Write the index type as the finset `posSet w` itself to avoid rewriting the predicate.
    change finrank ℝ ((posSet (n := n) w) → ℝ) = (posSet (n := n) w).card
    calc
      finrank ℝ ((posSet (n := n) w) → ℝ) = Fintype.card (posSet (n := n) w) := by
        simp [Module.finrank_fintype_fun_eq_card]
      _ = (posSet (n := n) w).card := by
        simp
  -- Convert the `LinearEquiv` finrank equality using the computation of the codomain finrank.
  simpa [h] using (LinearEquiv.finrank_eq (supportedOnPosEquiv (n := n) w))

theorem posIndex_diag_signType (w : Fin n → SignType) :
    posIndex (V := Fin n → ℝ) (diagForm (n := n) w) = (posSet (n := n) w).card := by
  -- lower bound: exhibit the supported-on-positive submodule
  have h_lower :
      (posSet (n := n) w).card ≤ posIndex (V := Fin n → ℝ) (diagForm (n := n) w) := by
    have hk :
        ∃ W' : Submodule ℝ (Fin n → ℝ),
          finrank ℝ W' = (posSet (n := n) w).card ∧
            IsPosDefOn (V := Fin n → ℝ) (diagForm (n := n) w) W' := by
      refine ⟨supportedOnPos (n := n) w, finrank_supportedOnPos (n := n) w,
        isPosDefOn_diagForm_supportedOnPos (n := n) w⟩
    exact le_posIndex_of_exists (V := Fin n → ℝ) (Q := diagForm (n := n) w) hk
  -- upper bound: any positive definite subspace injects into the positive coordinates
  have h_upper :
      posIndex (V := Fin n → ℝ) (diagForm (n := n) w) ≤ (posSet (n := n) w).card := by
    rcases posIndex_spec (Q := diagForm (n := n) w) with ⟨W, hW, hWpos⟩
    let f := restrictPos (n := n) w
    let g : W →ₗ[ℝ] ({i // i ∈ posSet (n := n) w} → ℝ) := f.comp W.subtype
    have hg_inj : Function.Injective g := by
      intro x y hxy
      have : g (x - y) = 0 := by
        simpa [g, map_sub] using congrArg (fun z => z - g y) hxy
      have hvanish : ∀ i, w i = SignType.pos → ((x - y : W) : (Fin n → ℝ)) i = 0 := by
        intro i hi
        have : (g (x - y)) ⟨i, (mem_posSet (n := n) (w := w)).2 hi⟩ = 0 := by
          simp [this]
        simpa [g, f, restrictPos_apply] using this
      have hnonpos :
          diagForm (n := n) w ((x - y : W) : (Fin n → ℝ)) ≤ 0 :=
        diagForm_nonpos_of_no_pos (n := n) (w := w) hvanish
      by_cases hxy0 : x - y = 0
      · have : x = y := sub_eq_zero.mp hxy0
        exact this
      · have hpos : 0 < (diagForm (n := n) w).comp W.subtype (x - y) := hWpos _ hxy0
        have : ¬ (0 < (diagForm (n := n) w).comp W.subtype (x - y)) :=
          not_lt_of_ge (by simpa [QuadraticMap.comp_apply] using hnonpos)
        exact (this hpos).elim
    have hfin_le :
        finrank ℝ W ≤ (posSet (n := n) w).card := by
      let eW : W ≃ₗ[ℝ] LinearMap.range g := LinearEquiv.ofInjective g hg_inj
      have hWrange : finrank ℝ W = finrank ℝ (LinearMap.range g) := LinearEquiv.finrank_eq eW
      have hrange_le :
          finrank ℝ (LinearMap.range g) ≤ finrank ℝ ({i // i ∈ posSet (n := n) w} → ℝ) :=
        Submodule.finrank_le (R := ℝ) (M := ({i // i ∈ posSet (n := n) w} → ℝ)) (LinearMap.range g)
      have htarget :
          finrank ℝ ({i // i ∈ posSet (n := n) w} → ℝ) = (posSet (n := n) w).card := by
        change finrank ℝ ((posSet (n := n) w) → ℝ) = (posSet (n := n) w).card
        calc
          finrank ℝ ((posSet (n := n) w) → ℝ) = Fintype.card (posSet (n := n) w) := by
            simp [Module.finrank_fintype_fun_eq_card]
          _ = (posSet (n := n) w).card := by
            simp
      simpa [hWrange, htarget] using hrange_le
    simpa [hW] using hfin_le
  exact le_antisymm h_upper h_lower

theorem posIndex_weightedSumSquares_signType (w : Fin n → SignType) :
    posIndex (V := Fin n → ℝ)
        (QuadraticMap.weightedSumSquares ℝ fun i : Fin n => (w i : ℝ)) =
      (Finset.univ.filter fun i : Fin n => w i = SignType.pos).card := by
  simpa [diagForm, posSet] using (posIndex_diag_signType (n := n) w)

theorem posIndex_diagForm (w : Fin n → SignType) :
    posIndex (V := Fin n → ℝ) (diagForm (n := n) w) = (posSet (n := n) w).card := by
  simpa [diagForm, posSet, signSet] using (posIndex_weightedSumSquares_signType (n := n) w)

theorem posDim_weightedSumSquares_signType (w : Fin n → SignType) :
    QuadraticForm.posDim (E := Fin n → ℝ)
        ((QuadraticMap.weightedSumSquares ℝ fun i : Fin n => (w i : ℝ)) :
          QuadraticForm ℝ (Fin n → ℝ)) =
      (Finset.univ.filter fun i : Fin n => w i = SignType.pos).card := by
  simp [QuadraticForm.posDim, posIndex_weightedSumSquares_signType (n := n) w]

theorem posDim_diagForm (w : Fin n → SignType) :
    QuadraticForm.posDim (E := Fin n → ℝ) (diagForm (n := n) w) = (posSet (n := n) w).card := by
  simp [QuadraticForm.posDim, posIndex_diagForm (n := n) w]

theorem negDim_weightedSumSquares_signType (w : Fin n → SignType) :
    QuadraticForm.negDim (E := Fin n → ℝ)
        ((QuadraticMap.weightedSumSquares ℝ fun i : Fin n => (w i : ℝ)) :
          QuadraticForm ℝ (Fin n → ℝ)) =
      (Finset.univ.filter fun i : Fin n => w i = SignType.neg).card := by
  classical
  set Q : QuadraticForm ℝ (Fin n → ℝ) :=
    (QuadraticMap.weightedSumSquares ℝ fun i : Fin n => (w i : ℝ))
  have hneg : -Q = diagForm (n := n) (fun i => -w i) := by
    ext v
    simp [Q, diagForm, QuadraticMap.weightedSumSquares_apply]
  have hpos : posIndex (V := Fin n → ℝ) (-Q) = (posSet (n := n) (fun i => -w i)).card := by
    simpa [hneg] using (posIndex_diag_signType (n := n) (w := fun i => -w i))
  -- `negDim Q = posIndex (-Q)` and `posSet (-w) = negSet w`.
  simp [QuadraticForm.negDim, Q, hpos, posSet_neg (n := n) w, negSet, signSet]

theorem negDim_diagForm (w : Fin n → SignType) :
    QuadraticForm.negDim (E := Fin n → ℝ) (diagForm (n := n) w) = (negSet (n := n) w).card := by
  -- This is exactly the filter-card theorem, restated via `negSet`.
  simpa [diagForm, negSet, signSet] using (negDim_weightedSumSquares_signType (n := n) w)

lemma card_posSet_add_card_negSet_add_card_zeroSet (w : Fin n → SignType) :
    (posSet (n := n) w).card + (negSet (n := n) w).card + (zeroSet (n := n) w).card =
      Fintype.card (Fin n) := by
  classical
  let A : Finset (Fin n) := posSet (n := n) w
  let B : Finset (Fin n) := negSet (n := n) w
  let C : Finset (Fin n) := zeroSet (n := n) w
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.2 ?_
    intro i hiA hiB
    have hiPos : w i = SignType.pos := (mem_posSet (n := n) (w := w)).1 hiA
    have hiNeg : w i = SignType.neg := (mem_negSet (n := n) (w := w)).1 hiB
    have : (SignType.pos : SignType) = SignType.neg := hiPos.symm.trans hiNeg
    cases this
  have hABC : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.2 ?_
    intro i hiAB hiC
    have hiC' : w i = 0 := (mem_zeroSet (n := n) (w := w)).1 hiC
    rcases Finset.mem_union.1 hiAB with hiA | hiB
    · have hiPos : w i = SignType.pos := (mem_posSet (n := n) (w := w)).1 hiA
      have : (SignType.pos : SignType) = 0 := hiPos.symm.trans hiC'
      cases this
    · have hiNeg : w i = SignType.neg := (mem_negSet (n := n) (w := w)).1 hiB
      have : (SignType.neg : SignType) = 0 := hiNeg.symm.trans hiC'
      cases this
  have hunion : (A ∪ B) ∪ C = Finset.univ := by
    ext i
    cases hi : w i <;> simp [A, B, C, signSet, hi]
  have hcardAB : (A ∪ B).card = A.card + B.card :=
    Finset.card_union_of_disjoint hAB
  have hcardABC : ((A ∪ B) ∪ C).card = (A ∪ B).card + C.card :=
    Finset.card_union_of_disjoint hABC
  have hcard : ((A ∪ B) ∪ C).card = A.card + B.card + C.card := by
    calc
      ((A ∪ B) ∪ C).card = (A ∪ B).card + C.card := hcardABC
      _ = (A.card + B.card) + C.card := by simp [hcardAB, Nat.add_assoc]
      _ = A.card + B.card + C.card := by simp [Nat.add_assoc]
  have huniv : ((A ∪ B) ∪ C).card = Fintype.card (Fin n) := by
    have : ((A ∪ B) ∪ C).card = (Finset.univ : Finset (Fin n)).card :=
      congrArg Finset.card hunion
    simpa using this
  have : A.card + B.card + C.card = Fintype.card (Fin n) := by
    calc
      A.card + B.card + C.card = ((A ∪ B) ∪ C).card := by simpa [hcard] using hcard.symm
      _ = Fintype.card (Fin n) := huniv
  simpa [A, B, C, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

theorem zeroDim_weightedSumSquares_signType (w : Fin n → SignType) :
    QuadraticForm.zeroDim (E := Fin n → ℝ)
        ((QuadraticMap.weightedSumSquares ℝ fun i : Fin n => (w i : ℝ)) :
          QuadraticForm ℝ (Fin n → ℝ)) =
      (Finset.univ.filter fun i : Fin n => w i = 0).card := by
  have hfin : finrank ℝ (Fin n → ℝ) = Fintype.card (Fin n) := by simp
  have hpos := posDim_weightedSumSquares_signType (n := n) w
  have hneg := negDim_weightedSumSquares_signType (n := n) w
  have hsum := card_posSet_add_card_negSet_add_card_zeroSet (n := n) w
  let A : ℕ := (posSet (n := n) w).card
  let B : ℕ := (negSet (n := n) w).card
  let C : ℕ := (zeroSet (n := n) w).card
  have hsum' : A + B + C = Fintype.card (Fin n) := by simpa [A, B, C] using hsum
  have hz0 : Fintype.card (Fin n) - A - B = C := by
    have hn : Fintype.card (Fin n) = A + (B + C) := by
      simpa [Nat.add_assoc] using hsum'.symm
    have h1 : Fintype.card (Fin n) - A = B + C := by
      simp [hn]
    calc
      Fintype.card (Fin n) - A - B = (Fintype.card (Fin n) - A) - B := rfl
      _ = (B + C) - B := by
        simpa using congrArg (fun t => t - B) h1
      _ = C := by simp
  set Q : QuadraticForm ℝ (Fin n → ℝ) :=
    (QuadraticMap.weightedSumSquares ℝ fun i : Fin n => (w i : ℝ))
  have hposI : posIndex (V := Fin n → ℝ) Q = A := by
    simpa [Q, A, posSet, signSet] using (posIndex_weightedSumSquares_signType (n := n) w)
  have hnegI : posIndex (V := Fin n → ℝ) (-Q) = B := by
    -- `negDim Q = posIndex (-Q)` and `negDim Q = card (negSet w)`.
    simpa [QuadraticForm.negDim, Q, B, negSet, signSet] using hneg
  have : QuadraticForm.zeroDim (E := Fin n → ℝ) Q = C := by
    dsimp [QuadraticForm.zeroDim, QuadraticForm.posDim, QuadraticForm.negDim]
    rw [hfin, hposI, hnegI]
    simpa using hz0
  simpa [C, zeroSet, signSet, Q] using this

theorem zeroDim_diagForm (w : Fin n → SignType) :
    QuadraticForm.zeroDim (E := Fin n → ℝ) (diagForm (n := n) w) = (zeroSet (n := n) w).card := by
  simpa [diagForm, zeroSet, signSet] using (zeroDim_weightedSumSquares_signType (n := n) w)

end

end Diagonal

/-!
### Canonical signature equals Sylvester choice

Using the diagonal computation for `weightedSumSquares` and the Sylvester diagonalization existence
theorem, we show that the canonical signature defined via `posIndex` agrees with the previously
defined `signatureChoice`. In particular, `signatureChoice` becomes an invariant of the quadratic
form (independent of the chosen diagonalization witness).
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
