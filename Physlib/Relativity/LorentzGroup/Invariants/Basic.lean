/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LightConeDeriv
/-!
# Invariant coefficient tensors on spacetime indices

## i. Overview

The invariants in the range of an equivariant map out of the complex Lorentz tensors with `n`
contravariant indices are the images of invariant tensors, and the components of a tensor,
relabelled by `Fin 1 ⊕ Fin 3` in each slot, are a coefficient tensor on which `SL(2,ℂ)` acts by
`act` (`Invariants.LorentzCovariance`). This file holds the machinery the rank-specific files use
to classify the invariant coefficient tensors, `IsInvariantCoeff`.

A matrix `M` acts on coefficient functions by `actMat M`, and a covector that the transposed
matrix reproduces up to a scalar reads off a component that `actMat M` scales by that scalar, so
an invariant coefficient function has no such component unless the scalar is `1` (A). Writing
each slot of a coefficient tensor in the light-cone basis of an axis splits it into pieces that
a boost scales by powers of its parameter, and an invariant keeps only the piece of weight zero:
`IsInvariantCoeff.lightConeComponent_eq_zero` (B). Section C records what the half turns about the
axes and the cyclic rotation of the axes force on an invariant coefficient tensor, for any number
of slots.

The conjugate transpose `dagger g` of an element of `SL(2,ℂ)`, whose Lorentz matrix is the
transpose of that of `g`, also lives here; it makes the colours of complex Lorentz tensors closed
under adjoints (`Invariants.AdjointClosed`).

## ii. Key results

- `Lorentz.Invariants.IsInvariantCoeff` : invariant coefficient tensors.
- `Lorentz.Invariants.IsInvariantCoeff.lightConeComponent_eq_zero` : the boost kills the
  light-cone components of nonzero weight.
- `Lorentz.Invariants.dagger` : the conjugate transpose in `SL(2,ℂ)`.

## iii. Table of contents

- A. Coefficient functions moved by a matrix
- B. Coefficient tensors on spacetime indices
- C. The half turns and the cyclic rotation

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C

namespace Invariants

/-!

## A. Coefficient functions moved by a matrix

A matrix `M` acts on coefficient functions by `actMat M`. The weight argument is generic: a
covector that the transposed matrix reproduces up to a scalar reads off a component that
`actMat M` scales by that scalar, so an invariant coefficient function has no such component
unless the scalar is `1`.

-/

section Mat

variable {ι : Type} [Fintype ι]

/-- The action on coefficient functions of a matrix moving the components:
  `(actMat M c) a = ∑_d c_d M_{a d}`, with `a` free and `d` summed. -/
def actMat (M : ι → ι → ℂ) (c : ι → ℂ) (a : ι) : ℂ := ∑ d, c d * M a d

/-- A covector `P` that the transposed matrix reproduces up to a scalar `k` reads off a
  component of the coefficients that `actMat M` scales by `k`. -/
lemma sum_mul_actMat (M : ι → ι → ℂ) (P c : ι → ℂ) (k : ℂ)
    (hP : ∀ d, ∑ a, P a * M a d = k * P d) :
    ∑ a, P a * actMat M c a = k * ∑ a, P a * c a := by
  simp only [actMat, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← mul_assoc, mul_comm _ (c d), ← hP d, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- A coefficient function fixed by `actMat M` has no component along a covector that the
  transposed matrix scales by an eigenvalue other than `1`. -/
lemma sum_mul_eq_zero_of_actMat_eq (M : ι → ι → ℂ) {P c : ι → ℂ} (hc : actMat M c = c) {k : ℂ}
    (hP : ∀ d, ∑ a, P a * M a d = k * P d) (hk : k ≠ 1) :
    ∑ a, P a * c a = 0 := by
  have h := sum_mul_actMat M P c k hP
  rw [hc] at h
  exact (mul_left_eq_self₀.1 h.symm).resolve_left hk

/-- The boost with parameter `2` distinguishes every nonzero weight: `2 ^ w ≠ 1` for `w ≠ 0`. -/
lemma two_zpow_ne_one {w : ℤ} (hw : w ≠ 0) : ((2 : ℝ) : ℂ) ^ w ≠ 1 := by
  rw [← Complex.ofReal_zpow, Ne, Complex.ofReal_eq_one,
    zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)]
  exact hw

end Mat

/-!

## B. Coefficient tensors on spacetime indices

-/

section Spacetime

variable {n : ℕ}

/-- The conjugate transpose `g†` of an element of `SL(2,ℂ)`, again in `SL(2,ℂ)`. -/
def dagger (g : SL(2,ℂ)) : SL(2,ℂ) := ⟨g.1ᴴ, by rw [Matrix.det_conjTranspose, g.2, star_one]⟩

/-- The Lorentz matrix of `g†` is the transpose of that of `g`, so these matrices are closed
  under transposition. -/
lemma toLorentzGroup_dagger (g : SL(2,ℂ)) :
    (SL2C.toLorentzGroup (dagger g)).1 = (SL2C.toLorentzGroup g).1ᵀ :=
  SL2C.toLorentzGroup_conjTranspose rfl

/-- The action of a real `4 × 4` matrix on coefficient tensors, one factor per slot:
  `(act Λ c) a = ∑_d c_d Λ_{a₀ d₀} ⋯`, with `a` free and `d` summed. -/
def act (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin n → Fin 1 ⊕ Fin 3) : ℂ :=
  ∑ d, c d * ∏ s, ((Λ (a s) (d s) : ℝ) : ℂ)

/-- The action on coefficient tensors is that of the matrix of products, one factor per slot. -/
lemma act_eq_actMat (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) :
    act Λ c = actMat (fun a d => ∏ i, ((Λ (a i) (d i) : ℝ) : ℂ)) c := rfl

/-- A coefficient tensor fixed by `act` of the Lorentz matrix of every `g : SL(2,ℂ)`. -/
def IsInvariantCoeff (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) : Prop :=
  ∀ g : SL(2,ℂ), act (SL2C.toLorentzGroup g).1 c = c

/-- A light-cone component of a coefficient tensor along axis `i`: the multi-index `κ` picks
  one light-cone direction per slot and `c` is contracted against that choice. -/
def lightConeComponent (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) : ℂ :=
  ∑ a, (∏ s, lightConeCoeff i (κ s) (a s)) * c a

/-- A light-cone multi-index that `Λ` reproduces up to a scalar `k` has its light-cone
  component scaled by `k`. The hypothesis is the eigenvector equation for the covector
  `∏ₛ lightConeCoeff i (κ s) (·)` under the transposed action, which is the form the light-cone
  directions of an axis satisfy for the transformations diagonal in that basis: the boost along
  the axis, with `k` a power of its parameter, and the half turn about it, with `k` the product
  of the signs of the slots. -/
lemma lightConeComponent_act (i : Fin 3) (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) (k : ℂ)
    (hΛ : ∀ d : Fin n → Fin 1 ⊕ Fin 3,
      ∑ a : Fin n → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (κ s) (a s))
          * ∏ s, ((Λ (a s) (d s) : ℝ) : ℂ)
        = k * ∏ s, lightConeCoeff i (κ s) (d s)) :
    lightConeComponent i (act Λ c) κ = k * lightConeComponent i c κ :=
  sum_mul_actMat _ _ c k hΛ

/-- The Lorentz matrix of a boost is symmetric. -/
lemma toLorentzGroup_boostAxis_symm (i : Fin 3) {t : ℝ} (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 a b
      = (SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 b a :=
  congrFun (congrFun
    (SL2C.toLorentzGroup_conjTranspose (SL2C.boostAxis_conjTranspose i t ht).symm) a) b

/-- An invariant coefficient tensor has no light-cone component of nonzero weight: the boost at
  `t = 2` would rescale such a component by a factor other than `1`. -/
lemma IsInvariantCoeff.lightConeComponent_eq_zero {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (i : Fin 3) {κ : Fin n → Fin 4}
    (hκ : ∑ s, lightConeWeight (κ s) ≠ 0) :
    lightConeComponent i c κ = 0 :=
  sum_mul_eq_zero_of_actMat_eq _ (hc (SL2C.boostAxis i 2 two_ne_zero))
    (fun d => by
      simpa only [toLorentzGroup_boostAxis_symm i two_ne_zero (d _)] using
        sum_prod_lightConeCoeff i κ d two_ne_zero)
    (two_zpow_ne_one hκ)

/-- A coefficient tensor is recovered from its light-cone components. -/
lemma eq_sum_lightConeComponent (i : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ)
    (d : Fin n → Fin 1 ⊕ Fin 3) :
    c d = ∑ κ, (∏ s, lightConeCoeffInv i (d s) (κ s)) * lightConeComponent i c κ := by
  simp only [lightConeComponent, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_prod_lightConeCoeffInv, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-!

## C. The half turns and the cyclic rotation

The half turn `SL2C.halfTurn k` has a diagonal Lorentz matrix with the signs `halfTurnSign k`,
so it multiplies the coefficient at `d` by the product of the signs of the slots of `d`. That
product is `1` or `-1`, and where it is `-1` invariance forces the coefficient to vanish.

The cyclic rotation `SL2C.rotationCycle` has the permutation matrix of `cycDir`, so it moves
coefficients rather than rescaling them, and invariance says that a coefficient tensor takes
the same value at `d` and at `cycIdx d`, the index vector with every slot rotated.

-/

/-- The half turn about the axis `k` multiplies the coefficient at `a` by the product of the
  signs `halfTurnSign k` of the slots of `a`. -/
lemma act_halfTurn (k : Fin 3) (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin n → Fin 1 ⊕ Fin 3) :
    act (SL2C.toLorentzGroup (SL2C.halfTurn k)).1 c a
      = ((∏ s, halfTurnSign k (a s) : ℤ) : ℂ) * c a := by
  rw [act, Finset.sum_eq_single a]
  · rw [mul_comm]
    push_cast
    congr 1
    exact Finset.prod_congr rfl fun s _ => by
      rw [SL2C.toLorentzGroup_halfTurn_apply, ite_eq_left rfl, Complex.ofReal_intCast]
  · intro d _ hd
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hd.symm
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    rw [SL2C.toLorentzGroup_halfTurn_apply, ite_eq_right hs, Complex.ofReal_zero]
  · exact fun h => absurd (Finset.mem_univ a) h

/-- The sign a half turn attaches to a coefficient is `1` or `-1`, being a product of such
  signs. -/
lemma prod_halfTurnSign_eq_one_or (k : Fin 3) (d : Fin n → Fin 1 ⊕ Fin 3) :
    ∏ s, halfTurnSign k (d s) = 1 ∨ ∏ s, halfTurnSign k (d s) = -1 := by
  refine Finset.prod_induction _ (fun m : ℤ => m = 1 ∨ m = -1) ?_ (Or.inl rfl) fun s _ => ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · unfold halfTurnSign
    split_ifs <;> simp

/-- An invariant coefficient tensor vanishes at every index vector that some half turn
  negates. -/
lemma IsInvariantCoeff.eq_zero_of_prod_halfTurnSign_ne_one {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) {k : Fin 3} {d : Fin n → Fin 1 ⊕ Fin 3}
    (hd : ∏ s, halfTurnSign k (d s) ≠ 1) : c d = 0 := by
  have h := congrFun (hc (SL2C.halfTurn k)) d
  rw [act_halfTurn, (prod_halfTurnSign_eq_one_or k d).resolve_left hd] at h
  push_cast at h
  linear_combination (-2⁻¹ : ℂ) * h

/-- The relabelling `cycDir`, which fixes time and sends `x → y → z → x`, applied in every
  slot. -/
def cycIdx (d : Fin n → Fin 1 ⊕ Fin 3) : Fin n → Fin 1 ⊕ Fin 3 := fun s => cycDir (d s)

/-- Cycling the axes three times is the identity. -/
lemma cycIdx_cycIdx_cycIdx (d : Fin n → Fin 1 ⊕ Fin 3) : cycIdx (cycIdx (cycIdx d)) = d :=
  funext fun s => cycDir_cycDir_cycDir (d s)

/-- The cyclic rotation permutes coefficients: the new coefficient at `a` is the old one at `a`
  cycled back. -/
lemma act_rotationCycle (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (a : Fin n → Fin 1 ⊕ Fin 3) :
    act (SL2C.toLorentzGroup SL2C.rotationCycle).1 c a = c (cycIdx (cycIdx a)) := by
  rw [act, Finset.sum_eq_single (cycIdx (cycIdx a))]
  · rw [Finset.prod_eq_one fun s _ => ?_, mul_one]
    rw [SL2C.toLorentzGroup_rotationCycle_apply, ite_eq_left, Complex.ofReal_one]
    exact (congrFun (cycIdx_cycIdx_cycIdx a) s).symm
  · intro d _ hd
    have hne : cycIdx d ≠ a := fun h => hd (by rw [← h, cycIdx_cycIdx_cycIdx])
    obtain ⟨s, hs⟩ := Function.ne_iff.1 hne
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    rw [SL2C.toLorentzGroup_rotationCycle_apply,
      ite_eq_right fun h : a s = cycDir (d s) => hs h.symm, Complex.ofReal_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- An invariant coefficient tensor is constant on the orbits of the cyclic rotation. -/
lemma IsInvariantCoeff.apply_cycIdx {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c)
    (d : Fin n → Fin 1 ⊕ Fin 3) : c (cycIdx d) = c d := by
  have h := congrFun (hc SL2C.rotationCycle) (cycIdx d)
  rw [act_rotationCycle, cycIdx_cycIdx_cycIdx] at h
  exact h.symm

end Spacetime

end Invariants

end Lorentz
