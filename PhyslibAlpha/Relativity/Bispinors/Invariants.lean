/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic
public import PhyslibAlpha.Relativity.Fermions.Weyl.FourIndex
public import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint
/-!
# Invariants of bispinor indices

Two bispinor indices carry one invariant and four carry four, and the Pauli matrices carry
four-vector indices to bispinor indices.

## i. Overview

A bispinor index `(α, α̇)` is a left-handed and a right-handed Weyl index side by side, on which
`M ∈ SL(2, ℂ)` acts by `M_{αβ} conj(M_{α̇β̇})` (`bispinorMatrix`). The action of `SL(2, ℂ)` on the
left-handed indices is holomorphic in `M` and that on the right-handed ones antiholomorphic. Along
the unipotent line `1 + z E` the derivative in the real direction is the sum of the infinitesimal
actions of `E` on the two chiralities, and in the imaginary direction `i` times their difference.
So a coefficient function of bispinor indices fixed by `SL(2, ℂ)` is killed by `E` and by `F` on
each chirality separately (A). The invariants then factor into those of the left-handed indices
and those of the right-handed ones, by `PhyslibAlpha.Relativity.Fermions.Weyl.FourIndex` applied
to one chirality with the other held fixed.

With two bispinor indices this leaves the line through `ε ⊗ ε̄` (B). With four it leaves the span
of the four products `pairingBasis i ⊗ pairingBasis j` of two pairings of each chirality,
`bispinorPairing`, and these four are invariant and linearly independent (C).

The covariant Pauli matrices change a four-vector index `μ` into a bispinor index,
`μ ↦ (σ_μ)_{αα̇}`. On every index of a coefficient tensor this is `pauliTransform`. As
`M σ_μ Mᴴ = Σ_ν Λ_{νμ} σ_ν`, it carries the action of the Lorentz matrix `Λ` of `M` to that of
`M` on bispinor indices, and by the trace orthogonality of the Pauli matrices it is injective. It
sends the Minkowski metric to `2 ε ⊗ ε̄`, the Fierz identity, matching the single invariant of
two four-vector indices with that of two bispinor indices (D).

## ii. Key results

- `Lorentz.bispinorMatrix` : the action of `SL(2, ℂ)` on one bispinor index.
- `Lorentz.infAct_eq_zero_of_bispinor_invariant` : an invariant is killed by a real nilpotent
  generator on each chirality separately.
- `Lorentz.mem_span_bispinorMetric_iff` : the invariants of two bispinor indices are the multiples
  of `ε ⊗ ε̄`.
- `Lorentz.mem_span_bispinorPairing_iff` : the invariants of four bispinor indices are the span
  of the four products of pairings.
- `Lorentz.linearIndependent_bispinorPairing` : the four products are linearly independent.
- `Lorentz.pauliTransform` : the change from four-vector indices to bispinor indices.
- `Lorentz.act_bispinorMatrix_pauliTransform` : it intertwines the two actions.
- `Lorentz.pauliTransform_injective` : it is injective.
- `Lorentz.pauliTransform_minkowskiMatrix` : it sends the Minkowski metric to `2 ε ⊗ ε̄`.

## iii. Table of contents

- A. Separating the two chiralities
- B. Two bispinor indices
- C. Four bispinor indices
- D. From four-vector indices to bispinor indices

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SlotAction Fermion

/-- The matrix by which `M ∈ SL(2, ℂ)` acts on one bispinor index `(α, α̇)`, a left-handed and a
  right-handed Weyl index, `M_{αβ} conj(M_{α̇β̇})`. -/
def bispinorMatrix (M : SL(2,ℂ)) : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ :=
  pairMatrix M.1 fun p q => star (M.1 p q)

/-!

## A. Separating the two chiralities

-/

/-- Along the line `t ↦ 1 + c t G` through the identity, the infinitesimal actions of `c G` on
  the left-handed indices and of its conjugate on the right-handed ones add up to zero on an
  invariant. -/
lemma infAct_add_infAct_eq_zero {n : ℕ} {C : (Fin n → Fin 2 × Fin 2) → ℂ}
    (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : ∀ z : ℂ, (1 + z • G).det = 1)
    (hC : ∀ M : SL(2,ℂ), act (bispinorMatrix M) C = C) (c : ℂ) (x y : Fin n → Fin 2) :
    infAct (fun p q => c * G p q) (fun x' => C (zip x' y)) x
      + infAct (fun p q => star (c * G p q)) (fun y' => C (zip x y')) y = 0 := by
  have h₂ : ∀ p q, star ((1 + (c * ((0 : ℝ) : ℂ)) • G) p q) = if p = q then 1 else 0 :=
    fun p q => by rw [one_add_smul_zero_apply]; split_ifs <;> simp
  have h := infAct_eq_zero_of_act_eq (ι := Fin n)
    (K := fun t : ℝ => bispinorMatrix ⟨1 + (c * t) • G, hG _⟩)
    (fun p q => by
      simp only [bispinorMatrix, pairMatrix]
      rw [one_add_smul_zero_apply, h₂]
      by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [Prod.ext_iff, h1, h2])
    (hasDerivAt_pairMatrix (one_add_smul_zero_apply G c) h₂ (hasDerivAt_one_add_smul G c)
      fun p q => (hasDerivAt_one_add_smul G c p q).star)
    fun t => hC ⟨1 + (c * t) • G, hG _⟩
  have hN : pairMatrix (fun p q => c * G p q) (fun p q => if p = q then 1 else 0)
      + pairMatrix (fun p q => if p = q then 1 else 0) (fun p q => star (c * G p q))
      = fun p q => pairMatrix (c • G) (fun p q => if p = q then 1 else 0) p q
        + pairMatrix (fun p q => if p = q then 1 else 0) (fun p q => star ((c • G) p q)) p q := by
    funext p q
    simp [pairMatrix]
  rw [← infAct_pair, hN]
  exact congrFun h (zip x y)

/-- On an invariant of bispinor indices a real generator `G` of a unipotent line, such as `E` or
  `F`, acts trivially on each chirality separately. The real direction of the line gives the sum
  of the two infinitesimal actions and the imaginary direction `i` times their difference. -/
lemma infAct_eq_zero_of_bispinor_invariant {n : ℕ} {C : (Fin n → Fin 2 × Fin 2) → ℂ}
    (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : ∀ z : ℂ, (1 + z • G).det = 1)
    (hGr : ∀ p q, star (G p q) = G p q)
    (hC : ∀ M : SL(2,ℂ), act (bispinorMatrix M) C = C) (x y : Fin n → Fin 2) :
    infAct G (fun x' => C (zip x' y)) x = 0 ∧ infAct G (fun y' => C (zip x y')) y = 0 := by
  have key : ∀ c : ℂ, c * infAct (fun p q => G p q) (fun x' => C (zip x' y)) x
      + star c * infAct (fun p q => G p q) (fun y' => C (zip x y')) y = 0 := fun c => by
    have h := infAct_add_infAct_eq_zero G hG hC c x y
    rw [show (fun p q => c * G p q) = c • fun p q : Fin 2 => G p q from rfl,
      show (fun p q => star (c * G p q)) = star c • fun p q : Fin 2 => G p q from by
        funext p q; simp [hGr], infAct_smul, infAct_smul] at h
    simpa only [Pi.smul_apply, smul_eq_mul] using h
  have h1 := key 1
  have hI := key Complex.I
  simp only [star_one, one_mul, Complex.star_def, Complex.conj_I] at h1 hI
  have hAB : infAct (fun p q => G p q) (fun x' => C (zip x' y)) x
      - infAct (fun p q => G p q) (fun y' => C (zip x y')) y = 0 :=
    (mul_eq_zero.1 (by linear_combination hI)).resolve_left Complex.I_ne_zero
  exact ⟨by linear_combination (h1 + hAB) / 2, by linear_combination (h1 - hAB) / 2⟩

/-!

## B. Two bispinor indices

-/

/-- The product `ε_{α₀α₁} ε_{α̇₀α̇₁}` of the Weyl metrics of the two chiralities on two bispinor
  indices. -/
def bispinorMetric (α : Fin 2 → Fin 2 × Fin 2) : ℂ :=
  metricCoeff (fun s => (α s).1) * metricCoeff (fun s => (α s).2)

/-- An invariant of two bispinor indices is a multiple of `ε ⊗ ε̄`, by the classification of two
  Weyl indices applied to each chirality in turn. -/
lemma eq_smul_bispinorMetric_of_invariant {C : (Fin 2 → Fin 2 × Fin 2) → ℂ}
    (hC : ∀ M : SL(2,ℂ), act (bispinorMatrix M) C = C) :
    C = C (zip ![0, 1] ![0, 1]) • bispinorMetric := by
  have hE := infAct_eq_zero_of_bispinor_invariant !![0, 1; 0, 0] (fun z => (upperUnipotent z).2)
    (fun p q => by fin_cases p <;> fin_cases q <;> simp) hC
  have hF := infAct_eq_zero_of_bispinor_invariant !![0, 0; 1, 0] (fun z => (lowerUnipotent z).2)
    (fun p q => by fin_cases p <;> fin_cases q <;> simp) hC
  have hL : ∀ y, (fun x => C (zip x y)) = C (zip ![0, 1] y) • metricCoeff :=
    fun y => eq_smul_metricCoeff_of_infAct_eq_zero (funext fun x => (hE x y).1)
      (funext fun x => (hF x y).1)
  have hR : (fun y => C (zip ![0, 1] y)) = C (zip ![0, 1] ![0, 1]) • metricCoeff :=
    eq_smul_metricCoeff_of_infAct_eq_zero (funext fun y => (hE _ y).2)
      (funext fun y => (hF _ y).2)
  funext α
  have h := congrFun (hL fun s => (α s).2) fun s => (α s).1
  have h' := congrFun hR fun s => (α s).2
  simp only [Pi.smul_apply, smul_eq_mul] at h h' ⊢
  rw [show C α = C (zip (fun s => (α s).1) fun s => (α s).2) from rfl, h, h', bispinorMetric]
  ring

/-- `ε ⊗ ε̄` is invariant, each factor being invariant. -/
lemma act_bispinorMetric (M : SL(2,ℂ)) :
    act (bispinorMatrix M) bispinorMetric = bispinorMetric := by
  funext α
  have h := act_pairMatrix M.1 (fun p q => star (M.1 p q)) metricCoeff metricCoeff
    (fun s => (α s).1) (fun s => (α s).2)
  rw [act_metricCoeff, show (fun p q => star (M.1 p q))
    = (SpecialLinearGroup.map (starRingEnd ℂ) M).1 from rfl, act_metricCoeff] at h
  exact h

/-- The invariants of two bispinor indices are the multiples of `ε ⊗ ε̄`. -/
lemma mem_span_bispinorMetric_iff (C : (Fin 2 → Fin 2 × Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act (bispinorMatrix M) C = C) ↔ C ∈ ℂ ∙ bispinorMetric := by
  constructor
  · intro hC
    rw [eq_smul_bispinorMetric_of_invariant hC]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hC M
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hC
    funext a
    have ha := congrFun (act_bispinorMetric M) a
    simp only [act, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at ha ⊢
    rw [ha]

/-!

## C. Four bispinor indices

-/

/-- The four products of a pairing of the left-handed indices and a pairing of the right-handed
  indices of four bispinor indices, `ε ε ⊗ ε̄ ε̄`. -/
def bispinorPairing (ij : Fin 2 × Fin 2) (α : Fin 4 → Fin 2 × Fin 2) : ℂ :=
  pairingBasis ij.1 (fun s => (α s).1) * pairingBasis ij.2 (fun s => (α s).2)

/-- An invariant of four bispinor indices is a combination of the four products of pairings,
  by the classification of four Weyl indices applied to each chirality in turn. -/
lemma mem_span_bispinorPairing_of_invariant {C : (Fin 4 → Fin 2 × Fin 2) → ℂ}
    (hC : ∀ M : SL(2,ℂ), act (bispinorMatrix M) C = C) :
    C ∈ Submodule.span ℂ (Set.range bispinorPairing) := by
  have hE := infAct_eq_zero_of_bispinor_invariant !![0, 1; 0, 0] (fun z => (upperUnipotent z).2)
    (fun p q => by fin_cases p <;> fin_cases q <;> simp) hC
  have hF := infAct_eq_zero_of_bispinor_invariant !![0, 0; 1, 0] (fun z => (lowerUnipotent z).2)
    (fun p q => by fin_cases p <;> fin_cases q <;> simp) hC
  have hL : ∀ y, (fun x => C (zip x y)) = ∑ i, C (zip (pairingPoint i) y) • pairingBasis i :=
    fun y => eq_sum_pairingBasis_of_infAct_eq_zero (funext fun x => (hE x y).1)
      (funext fun x => (hF x y).1)
  have hR : ∀ i, (fun y => C (zip (pairingPoint i) y))
      = ∑ j, C (zip (pairingPoint i) (pairingPoint j)) • pairingBasis j :=
    fun i => eq_sum_pairingBasis_of_infAct_eq_zero (funext fun y => (hE _ y).2)
      (funext fun y => (hF _ y).2)
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).2
    ⟨fun ij => C (zip (pairingPoint ij.1) (pairingPoint ij.2)), funext fun α => ?_⟩
  have h := congrFun (hL fun s => (α s).2) fun s => (α s).1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [show C α = C (zip (fun s => (α s).1) fun s => (α s).2) from rfl, h,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h' := congrFun (hR i) fun s => (α s).2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h'
  rw [h', Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [bispinorPairing]
  ring

/-- The four products of pairings are invariant, each factor being invariant. -/
lemma act_bispinorPairing (M : SL(2,ℂ)) (ij : Fin 2 × Fin 2) :
    act (bispinorMatrix M) (bispinorPairing ij) = bispinorPairing ij := by
  have hW : ∀ (N : SL(2,ℂ)) (i : Fin 2), act N.1 (pairingBasis i) = pairingBasis i :=
    fun N i => (mem_span_pairingBasis_iff _).2 (Submodule.subset_span ⟨i, rfl⟩) N
  funext α
  have h := act_pairMatrix M.1 (fun p q => star (M.1 p q)) (pairingBasis ij.1)
    (pairingBasis ij.2) (fun s => (α s).1) (fun s => (α s).2)
  rw [hW, show (fun p q => star (M.1 p q))
    = (SpecialLinearGroup.map (starRingEnd ℂ) M).1 from rfl, hW] at h
  exact h

/-- The invariants of four bispinor indices are the span of the four products of pairings. -/
lemma mem_span_bispinorPairing_iff (C : (Fin 4 → Fin 2 × Fin 2) → ℂ) :
    (∀ M : SL(2,ℂ), act (bispinorMatrix M) C = C)
      ↔ C ∈ Submodule.span ℂ (Set.range bispinorPairing) := by
  refine ⟨mem_span_bispinorPairing_of_invariant, fun hC M => ?_⟩
  obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hC
  rw [act_eq_transform, map_sum]
  simp only [map_smul, ← act_eq_transform, act_bispinorPairing]

/-- The four products of pairings are linearly independent. At the points
  `zip (pairingPoint k) (pairingPoint l)` they form the unit matrix. -/
lemma linearIndependent_bispinorPairing : LinearIndependent ℂ bispinorPairing := by
  refine Fintype.linearIndependent_iff.2 fun g hg ij => ?_
  have h := congrFun hg (zip (pairingPoint ij.1) (pairingPoint ij.2))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, bispinorPairing,
    zip, pairingBasis_pairingPoint, mul_ite, mul_one, mul_zero] at h
  rw [Fintype.sum_prod_type] at h
  simpa [Prod.ext_iff] using h

/-!

## D. From four-vector indices to bispinor indices

-/

/-- The change from a four-vector index to a bispinor index by the covariant Pauli matrices,
  `μ ↦ (σ_μ)_{αα̇}`, on every index of a coefficient tensor. -/
def pauliTransform {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ((ι → Fin 1 ⊕ Fin 3) → ℂ) →ₗ[ℂ] ((ι → Fin 2 × Fin 2) → ℂ) :=
  transform fun μ p => PauliMatrix.pauliLower μ p.1 p.2

/-- The covariant Pauli matrices move as a covector, `M σ_μ Mᴴ = Σ_ν Λ_{νμ} σ_ν`, written
  entrywise against the action on a bispinor index. -/
lemma sum_pauliLower_mul_bispinorMatrix (M : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (q : Fin 2 × Fin 2) :
    ∑ p : Fin 2 × Fin 2, PauliMatrix.pauliLower μ p.1 p.2 * bispinorMatrix M q p
      = ∑ ν, (((SL2C.toLorentzGroup M).1 ν μ : ℝ) : ℂ) * PauliMatrix.pauliLower ν q.1 q.2 := by
  have h := congrArg (fun A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) => A.1 q.1 q.2)
    (SL2C.toSelfAdjointMap_basis (M := M) μ)
  simp only [SL2C.toSelfAdjointMap_apply, PauliMatrix.pauliBasis'_coe, AddSubgroup.val_finsetSum,
    selfAdjoint.val_smul, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul] at h
  rw [← h, Fintype.sum_prod_type]
  simp only [mul_apply, conjTranspose_apply, Finset.sum_mul, bispinorMatrix, pairMatrix]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- The Pauli change of indices carries the action of the Lorentz matrix of `M` on four-vector
  indices to the action of `M` on bispinor indices. -/
lemma act_bispinorMatrix_pauliTransform {ι : Type*} [Fintype ι] [DecidableEq ι] (M : SL(2,ℂ))
    (c : (ι → Fin 1 ⊕ Fin 3) → ℂ) :
    act (bispinorMatrix M) (pauliTransform c)
      = pauliTransform (act (fun a b => (((SL2C.toLorentzGroup M).1 a b : ℝ) : ℂ)) c) :=
  act_transform (sum_pauliLower_mul_bispinorMatrix M) c

/-- The trace orthogonality of the covariant Pauli matrices, `tr (σ_μ σ_ν) = 2 δ_{μν}`. -/
lemma sum_pauliLower_mul_pauliLower_swap (μ ν : Fin 1 ⊕ Fin 3) :
    ∑ p : Fin 2 × Fin 2, PauliMatrix.pauliLower μ p.1 p.2 * PauliMatrix.pauliLower ν p.2 p.1
      = 2 * if μ = ν then 1 else 0 := by
  rcases μ with μ | μ <;> rcases ν with ν | ν <;> fin_cases μ <;> fin_cases ν <;>
    simp [PauliMatrix.pauliLower, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Fintype.sum_prod_type] <;> norm_num [Complex.ext_iff]

/-- The Pauli change of indices is injective. Half the transposed Pauli matrices undo it. -/
lemma pauliTransform_injective {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective (pauliTransform (ι := ι)) :=
  transform_injective (T' := fun p ν => 2⁻¹ * PauliMatrix.pauliLower ν p.2 p.1) fun μ ν => by
    simp_rw [mul_left_comm _ (2⁻¹ : ℂ), ← Finset.mul_sum, sum_pauliLower_mul_pauliLower_swap]
    split_ifs <;> norm_num


/-- Through the Pauli matrices the Minkowski metric is twice `ε ⊗ ε̄`, the Fierz identity
  `η^{μν} (σ_μ)_{αα̇} (σ_ν)_{ββ̇} = 2 ε_{αβ} ε_{α̇β̇}`. -/
lemma pauliTransform_minkowskiMatrix :
    pauliTransform (fun d : Fin 2 → Fin 1 ⊕ Fin 3 => ((minkowskiMatrixZ (d 0) (d 1) : ℤ) : ℂ))
      = (2 : ℂ) • bispinorMetric := by
  funext α
  obtain ⟨⟨a, a'⟩, ⟨b, b'⟩, rfl⟩ : ∃ p q, α = ![p, q] :=
    ⟨α 0, α 1, by funext i; fin_cases i <;> rfl⟩
  rw [pauliTransform, transform_apply, Physlib.Fin.sum_fin_two_arrow]
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_three, minkowskiMatrixZ, PauliMatrix.pauliLower,
      PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix, bispinorMetric, metricCoeff,
      metricRaw] <;> norm_num [Complex.ext_iff]

end Lorentz
