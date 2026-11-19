/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.Bispinors.Invariants
public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.LorentzCovariance
public import PhyslibAlpha.Mathematics.LeviCivita.Basic
/-!
# Lorentz invariants of a rank-four tensor

The Lorentz invariants of four four-vector indices are spanned by the three pairings of the
metric and the Levi-Civita symbol.

## i. Overview

A rank-four tensor `T^{μνρσ}` has `4 ^ 4 = 256` components, and four invariant tensors can be
contracted with it:

* `η_{μν} η_{ρσ}`, `η_{μρ} η_{νσ}` and `η_{μσ} η_{νρ}`, the three pairings of the metric,
* `ε_{μνρσ}`, the Levi-Civita symbol.

These are the tensors `contractionTensor i`. There are no others: for an equivariant map
`f : ℂT(fun _ : Fin 4 => .up) →ₗ[ℂ] B`, `IsLorentzCovariant 4`, a vector of `LinearMap.range f ⊔ S`,
for `S` a Lorentz-stable submodule, is invariant exactly when it is a combination of the four
images `f (contractionTensor i)` plus an invariant of `S`, `mem_range_sup_invariant_iff` (H), and
`reducesInvariantsTo_span_contractionTensor` reads the left-to-right direction as a reduction.
The fourth tensor is a pseudoscalar, so it would drop out if reflections were allowed;
independence is not proved, and for a given `f` the four images may be dependent or zero.
When `f` is antisymmetric under exchanging its last two slots, two images already span: that
of `η_{μρ} η_{νσ}` and that of `ε_{μνρσ}` (B.4). When `f` is moreover symmetric under exchanging
its first two slots, both of those vanish too (B.5).

The four tensors are invariant, by `Λ η Λᵀ = η` and `det Λ = 1` (D, E). An invariant of the range
of `f` is the image of an invariant tensor, whose coefficient tensor is invariant (H). Such a
coefficient tensor is a combination of the four, which is seen through Weyl spinors (I to K). The
Pauli matrices change each four-vector index into a bispinor index, a left-handed and a
right-handed Weyl index, and carry the Lorentz action to the action of `SL(2, ℂ)` on bispinors.
There the invariants factor into those of the four left-handed and of the four right-handed
indices, two pairings `ε ε` for each chirality, so four bispinor indices carry exactly four
invariants (`Lorentz.mem_span_bispinorPairing_iff`). The Pauli change is injective and the four
tensors are independent, so they span every invariant.

## ii. Key results

- `Lorentz.RankFour.contractionTensor` : the four invariant tensors.
- `Lorentz.RankFour.exists_eq_sum` : an invariant coefficient tensor is a combination of them.
- `Lorentz.RankFour.mem_range_sup_invariant_iff` : the classification of the invariants.
- `Lorentz.RankFour.reducesInvariantsTo_span_contractionTensor` : the same as a reduction.
- `Lorentz.RankFour.span_range_contractionTensor_of_antisymm` : for a map antisymmetric in its
  last two slots, two of the four images span.
- `Lorentz.RankFour.apply_contractionTensor_one_of_symm_of_antisymm`,
  `Lorentz.RankFour.apply_contractionTensor_three_of_symm` : symmetry in the first two slots
  kills those two images.

## iii. Table of contents

- A. Coefficient tensors
- B. The four invariant tensors
- C. The metric, the Levi-Civita symbol and the invariant tensors
- D. The four coefficient tensors are invariant
- E. The four tensors are Lorentz invariant
- F. Exchanging the last two slots
- G. Exchanging the first two slots
- H. Invariants of the range come from invariant coefficient tensors
- I. The Pauli change of indices
- J. The four coefficient tensors are independent
- K. The classification of the invariant coefficient tensors
- L. The classification of the invariants of an equivariant map

## iv. References

* None.
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants complexLorentzTensor

/-!

## A. Coefficient tensors

A direction is an element of `Fin 1 ⊕ Fin 3`, time or one of the three axes; an index vector
`d : Fin 4 → Fin 1 ⊕ Fin 3` puts one in each slot, and a coefficient tensor `c` assigns a
number to each. The components of a tensor, relabelled this way, are its coefficient tensor,
`coeffEquiv 4`, on which `g` acts by

`(act Λ c) a = ∑_d c_d Λ_{a₀ d₀} ⋯ Λ_{a₃ d₃}`,

with `a` free and `d` summed (`coeffEquiv_smul`), and a tensor is invariant exactly when its
coefficient tensor is `IsInvariantCoeff` (`invariant_iff_isInvariantCoeff`). Everything in this
paragraph is stated for any number of slots in
`PhyslibAlpha.Relativity.LorentzGroup.Invariants.Basic` and
`PhyslibAlpha.Relativity.LorentzGroup.Invariants.LorentzCovariance`, and used here at four.
-/

namespace RankFour

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-!

## B. The four invariant tensors

## C. The metric, the Levi-Civita symbol and the invariant tensors

The metric is `minkowskiMatrixZ`, the integer form of `minkowskiMatrix`, and the symbol is
`leviCivitaSymbol`, read on an index vector through `finSumFinEquiv`. Both are integer valued.
The metric pairings use the slots `(0,1)(2,3)`, `(0,2)(1,3)` and `(0,3)(1,2)`;
`contractionCoeff` holds the four coefficient tensors and `contractionTensor` the four tensors
with those coefficients, in that order.
-/

/-- The four coefficient tensors, the three metric pairings, then the Levi-Civita symbol. -/
def contractionCoeff : Fin 4 → (Fin 4 → Fin 1 ⊕ Fin 3) → ℤ :=
  ![fun d => minkowskiMatrixZ (d 0) (d 1) * minkowskiMatrixZ (d 2) (d 3),
    fun d => minkowskiMatrixZ (d 0) (d 2) * minkowskiMatrixZ (d 1) (d 3),
    fun d => minkowskiMatrixZ (d 0) (d 3) * minkowskiMatrixZ (d 1) (d 2),
    fun d => leviCivitaSymbol fun μ => d (finSumFinEquiv μ)]

/-- The four invariant tensors with four contravariant indices, `η_{μν} η_{ρσ}`,
  `η_{μρ} η_{νσ}`, `η_{μσ} η_{νρ}` and `ε_{μνρσ}`. -/
noncomputable def contractionTensor (i : Fin 4) : ℂT(fun _ : Fin 4 => Color.up) :=
  (coeffEquiv 4).symm fun d => ((contractionCoeff i d : ℤ) : ℂ)

/-- `ofComponents T` sends each invariant tensor to the contraction of `T` with its
  coefficients. -/
lemma ofComponents_contractionTensor (T : (Fin 4 → Fin 1 ⊕ Fin 3) → B) (i : Fin 4) :
    ofComponents T (contractionTensor i) = ∑ d, ((contractionCoeff i d : ℤ) : ℂ) • T d :=
  ofComponents_coeffEquiv_symm T _

/-!

## D. The four coefficient tensors are invariant

`Λ η Λᵀ = η` defines the Lorentz group; entry by entry it is
`LorentzGroup.sum_minkowskiMatrixZ_mul`, and a pair of metrics is two copies of it, one per
pair of slots (`act_outerPair`). The inner and split pairings are the outer one with the slots
permuted (`act_outerPair_comp`). The symbol against
four rows of `M` gives `det M` times the symbol of those rows (`sum_leviCivitaSymbol_mul_prod`),
and `det Λ = 1` here: the only use of the determinant, and the reason there are four invariants
and not three, a reflection having `det = -1`. `sum_pi_four` is bookkeeping.
-/

/-- A sum over index vectors is a fourfold sum over directions. -/
lemma sum_pi_four {M : Type*} [AddCommMonoid M] (F : (Fin 4 → Fin 1 ⊕ Fin 3) → M) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, F d
      = ∑ x : Fin 1 ⊕ Fin 3, ∑ y : Fin 1 ⊕ Fin 3, ∑ z : Fin 1 ⊕ Fin 3,
        ∑ w : Fin 1 ⊕ Fin 3, F ![x, y, z, w] := by
  rw [show (∑ d : Fin 4 → Fin 1 ⊕ Fin 3, F d)
      = ∑ p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
        F ![p.1, p.2.1, p.2.2.1, p.2.2.2] from
      Fintype.sum_equiv
        { toFun := fun d => (d 0, d 1, d 2, d 3)
          invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
          left_inv := fun d => by funext i; fin_cases i <;> simp
          right_inv := fun p => by simp } _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp]
  simp only [Fintype.sum_prod_type]

/-- The pairing of slots `(0,1)` and `(2,3)` is fixed, by two copies of
  `LorentzGroup.sum_minkowskiMatrixZ_mul`. -/
lemma act_outerPair (Λ : LorentzGroup 3) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((minkowskiMatrixZ (d 0) (d 1) * minkowskiMatrixZ (d 2) (d 3) : ℤ) : ℂ)) a
      = ((minkowskiMatrixZ (a 0) (a 1) * minkowskiMatrixZ (a 2) (a 3) : ℤ) : ℂ) := by
  have h : ∀ x y z w : Fin 1 ⊕ Fin 3,
      ((minkowskiMatrixZ (![x, y, z, w] 0) (![x, y, z, w] 1)
          * minkowskiMatrixZ (![x, y, z, w] 2) (![x, y, z, w] 3) : ℤ) : ℂ)
        * ∏ s, ((Λ.1 (a s) (![x, y, z, w] s) : ℝ) : ℂ)
      = (((minkowskiMatrixZ x y : ℤ) : ℂ)
          * (((Λ.1 (a 0) x : ℝ) : ℂ) * ((Λ.1 (a 1) y : ℝ) : ℂ)))
        * (((minkowskiMatrixZ z w : ℤ) : ℂ)
          * (((Λ.1 (a 2) z : ℝ) : ℂ) * ((Λ.1 (a 3) w : ℝ) : ℂ))) := by
    intro x y z w
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    push_cast
    ring
  rw [act, sum_pi_four]
  simp only [h, ← Finset.mul_sum, ← Finset.sum_mul, LorentzGroup.sum_minkowskiMatrixZ_mul]
  push_cast
  ring

/-- The same for the slots permuted by `σ`, by renaming the summation variable. -/
lemma act_outerPair_comp (σ : Equiv.Perm (Fin 4)) (Λ : LorentzGroup 3)
    (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((minkowskiMatrixZ (d (σ 0)) (d (σ 1))
        * minkowskiMatrixZ (d (σ 2)) (d (σ 3)) : ℤ) : ℂ)) a
      = ((minkowskiMatrixZ (a (σ 0)) (a (σ 1))
        * minkowskiMatrixZ (a (σ 2)) (a (σ 3)) : ℤ) : ℂ) := by
  have h := act_outerPair Λ (a ∘ σ)
  rw [act, ← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 1 ⊕ Fin 3)))] at h
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_def,
    id] at h
  rw [← h, act]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Equiv.prod_comp σ fun i => ((Λ.1 (a i) (d i) : ℝ) : ℂ)]

/-- The symbol is fixed by a Lorentz matrix of determinant `1`; in general it picks up `det Λ`,
  by `sum_leviCivitaSymbol_mul_prod`. -/
lemma act_leviCivitaSymbol (Λ : LorentzGroup 3) (hΛ : Λ.1.det = 1) (a : Fin 4 → Fin 1 ⊕ Fin 3) :
    act Λ.1 (fun d => ((leviCivitaSymbol fun μ => d (finSumFinEquiv μ) : ℤ) : ℂ)) a
      = ((leviCivitaSymbol fun μ => a (finSumFinEquiv μ) : ℤ) : ℂ) := by
  have hdet : (Complex.ofRealHom.mapMatrix Λ.1).det = 1 := by
    rw [← RingHom.map_det, hΛ]
    simp
  have h := sum_leviCivitaSymbol_mul_prod (Complex.ofRealHom.mapMatrix Λ.1)
    (fun μ => a (finSumFinEquiv μ))
  rw [hdet, one_mul] at h
  rw [act, ← h, ← Equiv.sum_comp
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin 1 ⊕ Fin 3)))]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_def, id]
  congr 1

/-- The four coefficient tensors are invariant. -/
lemma isInvariantCoeff_contractionCoeff (i : Fin 4) :
    IsInvariantCoeff fun d => ((contractionCoeff i d : ℤ) : ℂ) := by
  intro g
  funext a
  fin_cases i
  · exact act_outerPair _ a
  · simpa [contractionCoeff, Equiv.swap_apply_def] using
      act_outerPair_comp (Equiv.swap 1 2) (SL2C.toLorentzGroup g) a
  · simpa [contractionCoeff, Equiv.swap_apply_def, Equiv.trans_apply] using
      act_outerPair_comp ((Equiv.swap 1 3).trans (Equiv.swap 1 2)) (SL2C.toLorentzGroup g) a
  · exact act_leviCivitaSymbol _ (SL2C.toLorentzGroup_det_one g) a

/-!

## E. The four tensors are Lorentz invariant

-/

/-- Each of the four tensors is Lorentz invariant, its coefficient tensor being invariant. -/
lemma contractionTensor_invariant (i : Fin 4) (g : SL(2,ℂ)) :
    g • contractionTensor i = contractionTensor i := by
  refine (invariant_iff_isInvariantCoeff _).2 ?_ g
  rw [contractionTensor, LinearEquiv.apply_symm_apply]
  exact isInvariantCoeff_contractionCoeff i

/-!

## F. Exchanging the last two slots

Exchanging the slots `2` and `3`, `permT (Equiv.swap 2 3)`, fixes `η_{μν} η_{ρσ}`, the metric
being symmetric, and exchanges `η_{μρ} η_{νσ}` with `η_{μσ} η_{νρ}`. So a linear map `f` out of
the tensors with `f ∘ₗ permT (Equiv.swap 2 3) = -f` sends the first tensor to zero and the
third to minus the second, and the four images span what the second and the Levi-Civita image
span. Neither equivariance of `f` nor any structure on `B` beyond a complex module is used; the
two remaining images may still be dependent or zero.
-/

section SwapTwoThree

open TensorSpecies

/-- Exchanging the last two of four contravariant slots is a reindexing. -/
lemma isReindexing_swap_two_three :
    Tensor.IsReindexing (fun _ : Fin 4 => Color.up) (fun _ => Color.up)
      ⇑(Equiv.swap (2 : Fin 4) 3) :=
  ⟨(Equiv.swap 2 3).bijective, fun _ => rfl⟩

/-- `η_{μν} η_{ρσ}` is unchanged by exchanging its last two slots. -/
lemma permT_swap_two_three_contractionTensor_zero :
    Tensor.permT _ isReindexing_swap_two_three (contractionTensor 0) = contractionTensor 0 := by
  rw [contractionTensor, permT_coeffEquiv_symm, Equiv.symm_swap]
  refine congrArg _ (funext fun d => ?_)
  simp [contractionCoeff, Equiv.swap_apply_def, minkowskiMatrixZ.comm (d 3) (d 2)]

/-- Exchanging the last two slots of `η_{μρ} η_{νσ}` gives `η_{μσ} η_{νρ}`. -/
lemma permT_swap_two_three_contractionTensor_one :
    Tensor.permT _ isReindexing_swap_two_three (contractionTensor 1) = contractionTensor 2 := by
  rw [contractionTensor, contractionTensor, permT_coeffEquiv_symm, Equiv.symm_swap]
  refine congrArg _ (funext fun d => ?_)
  simp [contractionCoeff, Equiv.swap_apply_def]

variable {f : ℂT(fun _ : Fin 4 => Color.up) →ₗ[ℂ] B}

/-- A map antisymmetric in the last two slots sends `η_{μν} η_{ρσ}` to zero. -/
lemma apply_contractionTensor_zero_of_antisymm
    (hf : f ∘ₗ Tensor.permT _ isReindexing_swap_two_three = -f) :
    f (contractionTensor 0) = 0 := by
  have h := LinearMap.congr_fun hf (contractionTensor 0)
  rw [LinearMap.comp_apply, permT_swap_two_three_contractionTensor_zero,
    LinearMap.neg_apply] at h
  have h2 : (2 : ℂ) • f (contractionTensor 0) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.2 h
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- A map antisymmetric in the last two slots sends `η_{μσ} η_{νρ}` to minus the image of
  `η_{μρ} η_{νσ}`. -/
lemma apply_contractionTensor_two_of_antisymm
    (hf : f ∘ₗ Tensor.permT _ isReindexing_swap_two_three = -f) :
    f (contractionTensor 2) = -f (contractionTensor 1) := by
  have h := LinearMap.congr_fun hf (contractionTensor 1)
  rwa [LinearMap.comp_apply, permT_swap_two_three_contractionTensor_one,
    LinearMap.neg_apply] at h

/-- For a map antisymmetric in the last two slots, the images of the four invariant tensors
  span the same as the images of `η_{μρ} η_{νσ}` and `ε_{μνρσ}`. -/
lemma span_range_contractionTensor_of_antisymm
    (hf : f ∘ₗ Tensor.permT _ isReindexing_swap_two_three = -f) :
    Submodule.span ℂ (Set.range fun i => f (contractionTensor i))
      = Submodule.span ℂ {f (contractionTensor 1), f (contractionTensor 3)} := by
  refine le_antisymm (Submodule.span_le.2 <| Set.range_subset_iff.2 fun i => ?_)
    (Submodule.span_mono <| Set.insert_subset_iff.2
      ⟨⟨1, rfl⟩, Set.singleton_subset_iff.2 ⟨3, rfl⟩⟩)
  fin_cases i
  · simp [apply_contractionTensor_zero_of_antisymm hf]
  · exact Submodule.subset_span (Set.mem_insert _ _)
  · simp only [Fin.reduceFinMk, Fin.isValue, SetLike.mem_coe]
    rw [apply_contractionTensor_two_of_antisymm hf]
    exact neg_mem (Submodule.subset_span (Set.mem_insert _ _))
  · exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

end SwapTwoThree

/-!

## G. Exchanging the first two slots

Exchanging the slots `0` and `1`, `permT (Equiv.swap 0 1)`, exchanges `η_{μρ} η_{νσ}` with
`η_{μσ} η_{νρ}` and negates `ε_{μνρσ}`. So a linear map `f` out of the tensors with
`f ∘ₗ permT (Equiv.swap 0 1) = f` sends `ε_{μνρσ}` to zero, and if `f` is also antisymmetric in
its last two slots it sends `η_{μρ} η_{νσ}` to zero as well: in both a symmetric pair of slots
is contracted against an antisymmetric one. As in B.4 nothing beyond a complex module is used.
-/

section SwapZeroOne

open TensorSpecies

/-- Exchanging the first two of four contravariant slots is a reindexing. -/
lemma isReindexing_swap_zero_one :
    Tensor.IsReindexing (fun _ : Fin 4 => Color.up) (fun _ => Color.up)
      ⇑(Equiv.swap (0 : Fin 4) 1) :=
  ⟨(Equiv.swap 0 1).bijective, fun _ => rfl⟩

/-- Exchanging the first two slots of `η_{μρ} η_{νσ}` gives `η_{μσ} η_{νρ}`. -/
lemma permT_swap_zero_one_contractionTensor_one :
    Tensor.permT _ isReindexing_swap_zero_one (contractionTensor 1) = contractionTensor 2 := by
  rw [contractionTensor, contractionTensor, permT_coeffEquiv_symm, Equiv.symm_swap]
  refine congrArg _ (funext fun d => ?_)
  simp [contractionCoeff, Equiv.swap_apply_def, mul_comm]

/-- Exchanging the first two slots negates `ε_{μνρσ}`. -/
lemma permT_swap_zero_one_contractionTensor_three :
    Tensor.permT _ isReindexing_swap_zero_one (contractionTensor 3) = -contractionTensor 3 := by
  rw [contractionTensor, permT_coeffEquiv_symm, Equiv.symm_swap, ← map_neg]
  refine congrArg _ (funext fun d => ?_)
  have he : (fun μ : Fin 1 ⊕ Fin 3 => (d ∘ Equiv.swap (0 : Fin 4) 1) (finSumFinEquiv μ))
      = (fun μ : Fin 1 ⊕ Fin 3 => d (finSumFinEquiv μ)) ∘ Equiv.swap (Sum.inl 0) (Sum.inr 0) := by
    funext μ
    rcases μ with μ | μ <;> fin_cases μ <;> rfl
  simp only [contractionCoeff, Matrix.cons_val, Pi.neg_apply]
  rw [he, leviCivitaSymbol_comp_swap _ Sum.inl_ne_inr, Int.cast_neg]

variable {f : ℂT(fun _ : Fin 4 => Color.up) →ₗ[ℂ] B}

/-- A map symmetric in the first two slots and antisymmetric in the last two sends
  `η_{μρ} η_{νσ}` to zero. -/
lemma apply_contractionTensor_one_of_symm_of_antisymm
    (hs : f ∘ₗ Tensor.permT _ isReindexing_swap_zero_one = f)
    (ha : f ∘ₗ Tensor.permT _ isReindexing_swap_two_three = -f) :
    f (contractionTensor 1) = 0 := by
  have h := LinearMap.congr_fun hs (contractionTensor 1)
  rw [LinearMap.comp_apply, permT_swap_zero_one_contractionTensor_one,
    apply_contractionTensor_two_of_antisymm ha] at h
  have h2 : (2 : ℂ) • f (contractionTensor 1) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.2 h.symm
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- A map symmetric in the first two slots sends `ε_{μνρσ}` to zero. -/
lemma apply_contractionTensor_three_of_symm
    (hs : f ∘ₗ Tensor.permT _ isReindexing_swap_zero_one = f) :
    f (contractionTensor 3) = 0 := by
  have h := LinearMap.congr_fun hs (contractionTensor 3)
  rw [LinearMap.comp_apply, permT_swap_zero_one_contractionTensor_three, map_neg] at h
  have h2 : (2 : ℂ) • f (contractionTensor 3) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.2 h.symm
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

end SwapZeroOne

/-!

## H. Invariants of the range come from invariant coefficient tensors

An invariant of the range of `f` is the image of an invariant tensor
(`TensorSpecies.IsEquivariant.exists_invariant_add_of_mem_sup`): the adjoint of the action of
`g` on the coefficients is the action of `g†`. The coefficient tensor of an invariant tensor is
invariant, so what remains is to classify the invariant coefficient tensors, sections D to G.
-/

/-!

## I. The Pauli change of indices

The covariant Pauli matrices change each four-vector index into a bispinor index, a left-handed
and a right-handed Weyl index (`Lorentz.pauliTransform`). This carries the action of the Lorentz
matrix of `g` to the action of `g` on bispinor indices
(`Lorentz.act_bispinorMatrix_pauliTransform`), so it carries an invariant coefficient tensor to
an invariant of four bispinor indices. Those are the span of the four products of pairings
`ε ε ⊗ ε̄ ε̄` (`Lorentz.mem_span_bispinorPairing_iff`).
-/

/-- The Pauli change of indices of an invariant coefficient tensor is a combination of the four
  products of pairings. -/
lemma pauliTransform_mem_span {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) :
    pauliTransform c ∈ Submodule.span ℂ (Set.range bispinorPairing) :=
  mem_span_bispinorPairing_of_invariant fun M => by
    rw [act_bispinorMatrix_pauliTransform]
    exact congrArg pauliTransform (hc M)

/-!

## J. The four coefficient tensors are independent

At `t t x x`, `t x t x`, `t x x t` and `t x y z` exactly one of the four coefficient tensors is
nonzero.
-/

/-- The four coefficient tensors are linearly independent. -/
lemma linearIndependent_contractionCoeff :
    LinearIndependent ℂ fun i d => ((contractionCoeff i d : ℤ) : ℂ) := by
  have hε : ∀ (d : Fin 4 → Fin 1 ⊕ Fin 3) (k : Fin 3), d 0 = d (Fin.natAdd 1 k) →
      leviCivitaSymbol (fun μ => d (finSumFinEquiv μ)) = 0 := fun d k h =>
    leviCivitaSymbol_eq_zero_of_eq (i := Sum.inl 0) (j := Sum.inr k) Sum.inl_ne_inr
      (by simpa [finSumFinEquiv] using h)
  have hid : (fun μ => (![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2] : Fin 4 → Fin 1 ⊕ Fin 3)
      (finSumFinEquiv μ)) = id := by
    funext μ
    rcases μ with μ | μ <;> fin_cases μ <;> rfl
  refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
  have h := fun d => congrFun hg d
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.sum_univ_four,
    contractionCoeff] at h
  have hk : ∀ (k : Fin 3) (d : Fin 4 → Fin 1 ⊕ Fin 3), d 0 = d (Fin.natAdd 1 k) →
      g 0 * ((minkowskiMatrixZ (d 0) (d 1) * minkowskiMatrixZ (d 2) (d 3) : ℤ) : ℂ)
        + g 1 * ((minkowskiMatrixZ (d 0) (d 2) * minkowskiMatrixZ (d 1) (d 3) : ℤ) : ℂ)
        + g 2 * ((minkowskiMatrixZ (d 0) (d 3) * minkowskiMatrixZ (d 1) (d 2) : ℤ) : ℂ) = 0 :=
    fun k d hd => by simpa [hε d k hd] using h d
  fin_cases i
  · simpa [minkowskiMatrixZ] using hk 0 ![Sum.inl 0, Sum.inl 0, Sum.inr 0, Sum.inr 0] rfl
  · simpa [minkowskiMatrixZ] using hk 1 ![Sum.inl 0, Sum.inr 0, Sum.inl 0, Sum.inr 0] rfl
  · simpa [minkowskiMatrixZ] using hk 2 ![Sum.inl 0, Sum.inr 0, Sum.inr 0, Sum.inl 0] rfl
  · simpa [minkowskiMatrixZ, hid] using h ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2]

/-!

## K. The classification of the invariant coefficient tensors

The Pauli change of indices is injective (`Lorentz.pauliTransform_injective`), so it carries the
four coefficient tensors to four linearly independent invariants of four bispinor indices. These
lie in the span of the four products of pairings, of dimension at most four, so they span it. The
change of an invariant coefficient tensor lies in that span, so it is the change of a combination
of the four, and by injectivity the tensor is that combination.
-/

/-- An invariant coefficient tensor is a combination of the four. -/
lemma exists_eq_sum {c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) :
    ∃ a : Fin 4 → ℂ, c = fun d => ∑ i, a i * ((contractionCoeff i d : ℤ) : ℂ) := by
  have hind := linearIndependent_contractionCoeff.map' pauliTransform
    (LinearMap.ker_eq_bot.2 pauliTransform_injective)
  have hle : Submodule.span ℂ (Set.range (pauliTransform ∘ fun i d =>
      ((contractionCoeff i d : ℤ) : ℂ))) ≤ Submodule.span ℂ (Set.range bispinorPairing) :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun i =>
      pauliTransform_mem_span (isInvariantCoeff_contractionCoeff i)
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [finrank_span_eq_card hind]
    exact (finrank_range_le_card _).trans (by simp))
  have hm := pauliTransform_mem_span hc
  rw [← heq] at hm
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hm
  refine ⟨a, pauliTransform_injective ?_⟩
  rw [← ha]
  simp only [Function.comp_apply, ← map_smul, ← map_sum]
  congr 1

/-!

## L. The classification of the invariants of an equivariant map

H to K reduce the invariants of `LinearMap.range f ⊔ S` to the span of the four images
`f (contractionTensor i)`; conversely those images are invariant, so a combination of them plus
an invariant of `S` is an invariant of `LinearMap.range f ⊔ S`.
-/

variable {f : ℂT(fun _ : Fin 4 => Color.up) →ₗ[ℂ] B}

/-- The invariants of the range of `f` reduce to the span of the images of the four invariant
  tensors. -/
lemma reducesInvariantsTo_span_contractionTensor (hf : IsLorentzCovariant 4 B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f)
      (Submodule.span ℂ (Set.range fun i => f (contractionTensor i))) :=
  hf.reducesInvariantsTo_span (fun i d => ((contractionCoeff i d : ℤ) : ℂ)) fun c hc => by
    obtain ⟨a, rfl⟩ := exists_eq_sum hc
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨a, funext fun d => ?_⟩
    simp [Finset.sum_apply]

/-- A vector of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is invariant exactly
  when it is a combination of the images of the four invariant tensors plus an invariant of
  `S`. `hS` is used only left to right. -/
lemma mem_range_sup_invariant_iff (hf : IsLorentzCovariant 4 B repLorentz f) (x : B)
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    (x ∈ LinearMap.range f ⊔ S ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ a : Fin 4 → ℂ, ∃ y ∈ S, x = ∑ i, a i • f (contractionTensor i) + y
        ∧ ∀ g : SL(2,ℂ), repLorentz g y = y := by
  have hfix : ∀ (a : Fin 4 → ℂ) (g : SL(2,ℂ)),
      repLorentz g (∑ i, a i • f (contractionTensor i)) = ∑ i, a i • f (contractionTensor i) :=
    fun a g => by
      simp only [map_sum, map_smul, hf.rep_map_of_invariant (contractionTensor_invariant _)]
  constructor
  · rintro ⟨hx, hinv⟩
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1
      (reducesInvariantsTo_span_contractionTensor hf S hS x hx hinv)
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw
    refine ⟨a, y, hy, rfl, fun g => ?_⟩
    have h := hinv g
    rw [map_add, hfix] at h
    exact add_left_cancel h
  · rintro ⟨a, y, hyS, rfl, hyinv⟩
    refine ⟨add_mem (Submodule.mem_sup_left (sum_mem fun i _ =>
      Submodule.smul_mem _ _ (LinearMap.mem_range_self f _))) (Submodule.mem_sup_right hyS),
      fun g => ?_⟩
    rw [map_add, hfix, hyinv g]

end RankFour

end Lorentz
