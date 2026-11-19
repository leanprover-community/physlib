/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Relativity.LorentzGroup.Invariants.LorentzCovariance
/-!
# Lorentz invariants of an odd number of four-vector indices

An odd number of four-vector indices carries no Lorentz invariant but zero.

## i. Overview

A tensor `T^{μ₁⋯μₙ}` with `n` odd has no Lorentz invariant but `0`. Nothing ties an odd number of
indices, as the metric takes two and the Levi-Civita symbol four. For an equivariant map
`f : ℂT(fun _ : Fin n => .up) →ₗ[ℂ] B`, `IsLorentzCovariant n`, that is `eq_zero_of_invariant`.
Its form modulo a Lorentz-stable submodule `S` is `reducesInvariantsTo_bot`, which the Standard
Model files use at one and three indices.

The invariants of the range of `f` are the images of invariant tensors, so it is enough that an
invariant coefficient tensor `c`, in the sense of
`PhyslibAlpha.Relativity.LorentzGroup.Invariants.Basic`, vanishes. One axis then does all the work,
with a parity argument. Along a spatial axis the four light-cone directions carry boost weights `2`,
`-2`, `0`, `0`, and an invariant `c` has no light-cone component of nonzero weight. In a multi-index
of total weight `0` the `+2` and `-2` slots pair off, leaving an odd number of the `n` slots
transverse. The half turn about the axis, the rotation by `π`, fixes time and the axis and negates
the two transverse directions (A). So it multiplies each weight-zero component by `-1` to an odd
power, that is by `-1`, and an invariant component both fixed and negated is `0` (B). Every
light-cone component of `c` vanishes, so `c` does, and with it the invariant. Section C applies this
to `f`.

The parity count is one identity. The sign of a light-cone direction is `-i ^ w`, `w` its weight,
so the sign of a multi-index is `(-1) ^ n i ^ W`, `W` its total weight
(`prod_lightConeSign_eq`).

## ii. Key results

- `prod_lightConeSign_of_sum_lightConeWeight_eq_zero` : the half turn negates every light-cone
  component of total weight zero with an odd number of slots
- `OddRank.eq_zero_of_isInvariantCoeff` : an invariant coefficient tensor with an odd number of
  slots is zero
- `OddRank.eq_zero_of_invariant` : every Lorentz invariant in the range of `f` is zero
- `OddRank.reducesInvariantsTo_bot` : the range of `f` reduces to `⊥`, so a Lorentz invariant of
  `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, lies in `S`

## iii. Table of contents

- A. The half turn about a spatial axis
- B. The classification of the Lorentz invariants
- C. The invariants of an equivariant map

## iv. References

* None.

-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants complexLorentzTensor

/-!

## A. The half turn about a spatial axis

The half turn about the axis `i` is the rotation by `π` about it, `SL2C.halfTurn i` from
`PhyslibAlpha.Relativity.SL2C.AxisRotations`. Its Lorentz matrix is diagonal, fixing time and the
axis and negating the two transverse directions. So on the light-cone directions of that axis it is
`1` on the two of weight `±2` and `-1` on the two transverse ones (`lightConeSign`). That sign is
`-i ^ w` for the weight `w`, which turns the count of transverse slots into a sum of weights.

-/

/-- The sign the half turn about an axis gives each light-cone direction of that axis, `1` on
  the two of weight `±2`, `-1` on the two transverse ones. -/
def lightConeSign (κ : Fin 4) : ℤ := if κ = 0 ∨ κ = 1 then 1 else -1

/-- The half turn about the axis `i` acts on each light-cone direction along that axis
  by its sign. -/
lemma sum_halfTurn_lightConeCoeff (i : Fin 3) (κ : Fin 4) (ν : Fin 1 ⊕ Fin 3) :
    ∑ μ : Fin 1 ⊕ Fin 3, lightConeCoeff i κ μ *
        (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 ν μ : ℝ) : ℂ)
      = ((lightConeSign κ : ℤ) : ℂ) * lightConeCoeff i κ ν := by
  simp only [SL2C.toLorentzGroup_halfTurn_apply]
  rcases ν with a | j
  · rw [Subsingleton.elim a 0]
    fin_cases i <;> fin_cases κ <;>
      simp [lightConeCoeff, lightConeSign, halfTurnSign, Fintype.sum_sum_type]
  · fin_cases i <;> fin_cases j <;> fin_cases κ <;>
      simp [lightConeCoeff, lightConeSign, halfTurnSign, Fintype.sum_sum_type]

/-- The scalar behind the action of the half turn on a light-cone multi-index. The half
  turn acts slot by slot, so the product of the per-slot signs factors out. -/
lemma sum_prod_halfTurn_lightConeCoeff (i : Fin 3) {n : ℕ} (c : Fin n → Fin 4)
    (a : Fin n → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) *
        (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ))
      = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) * ∏ j, lightConeCoeff i (c j) (a j) := by
  calc ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) *
        (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ))
      = ∑ d : Fin n → Fin 1 ⊕ Fin 3, ∏ j, (lightConeCoeff i (c j) (d j) *
          (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ)) :=
        Finset.sum_congr rfl fun d _ => (Finset.prod_mul_distrib).symm
    _ = ∏ j, ∑ μ : Fin 1 ⊕ Fin 3, (lightConeCoeff i (c j) μ *
          (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) μ : ℝ) : ℂ)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ j, (((lightConeSign (c j) : ℤ) : ℂ) * lightConeCoeff i (c j) (a j)) :=
        Finset.prod_congr rfl fun j _ => sum_halfTurn_lightConeCoeff i (c j) (a j)
    _ = (∏ j, ((lightConeSign (c j) : ℤ) : ℂ)) * ∏ j, lightConeCoeff i (c j) (a j) :=
        Finset.prod_mul_distrib
    _ = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) * ∏ j, lightConeCoeff i (c j) (a j) := by
        push_cast
        rfl

/-- The sign of a light-cone direction is `-i ^ w`, `w` its boost weight. -/
lemma lightConeSign_eq_neg_I_zpow (κ : Fin 4) :
    ((lightConeSign κ : ℤ) : ℂ) = -Complex.I ^ lightConeWeight κ := by
  fin_cases κ <;> simp [lightConeSign, lightConeWeight, _root_.zpow_neg]

/-- The sign of a light-cone multi-index of `n` slots is `(-1) ^ n i ^ W`, `W` its total boost
  weight. -/
lemma prod_lightConeSign_eq {n : ℕ} (c : Fin n → Fin 4) :
    ((∏ j, lightConeSign (c j) : ℤ) : ℂ)
      = (-1) ^ n * Complex.I ^ (∑ j, lightConeWeight (c j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, Int.cast_mul, ih (fun j => c j.succ),
      lightConeSign_eq_neg_I_zpow, zpow_add₀ Complex.I_ne_zero, pow_succ]
    ring

/-- A light-cone multi-index of an odd number of slots and total boost weight zero has an odd
  number of transverse slots, so the half turn acts on it by `-1`. -/
lemma prod_lightConeSign_of_sum_lightConeWeight_eq_zero {n : ℕ} (hn : Odd n)
    (c : Fin n → Fin 4) (hc : ∑ j, lightConeWeight (c j) = 0) :
    ((∏ j, lightConeSign (c j) : ℤ) : ℂ) = -1 := by
  rw [prod_lightConeSign_eq, hc, zpow_zero, mul_one, hn.neg_one_pow]

namespace OddRank

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B} {n : ℕ}

/-!

## B. The classification of the Lorentz invariants

Writing a coefficient tensor in the light-cone basis of one axis leaves only the multi-indices
of total weight zero, the others being killed by the boost. With an odd number of slots the half
turn about that axis negates exactly those, so they vanish too and nothing is left.

-/

/-- The half turn multiplies a light-cone component by the product of the signs of its slots. -/
lemma lightConeComponent_act_halfTurn (i : Fin 3)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) :
    lightConeComponent i (act (SL2C.toLorentzGroup (SL2C.halfTurn i)).1 c) κ
      = ((∏ s, lightConeSign (κ s) : ℤ) : ℂ) * lightConeComponent i c κ :=
  lightConeComponent_act i _ c κ _ fun d => by
    simpa only [SL2C.toLorentzGroup_halfTurn_symm i (d _)] using
      sum_prod_halfTurn_lightConeCoeff i κ d

/-- An invariant coefficient tensor with an odd number of slots has no weight-zero light-cone
  component either, the half turn negating those. -/
lemma lightConeComponent_eq_zero_of_weight_zero (hn : Odd n)
    {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ} (hc : IsInvariantCoeff c) (i : Fin 3)
    {κ : Fin n → Fin 4} (hκ : ∑ s, lightConeWeight (κ s) = 0) :
    lightConeComponent i c κ = 0 := by
  have h := lightConeComponent_act_halfTurn i c κ
  rw [hc, prod_lightConeSign_of_sum_lightConeWeight_eq_zero hn κ hκ] at h
  linear_combination h / 2

/-- An invariant coefficient tensor with an odd number of slots is zero. No light-cone
  component of it survives. -/
lemma eq_zero_of_isInvariantCoeff (hn : Odd n) {c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) : c = 0 := by
  funext d
  show c d = 0
  rw [eq_sum_lightConeComponent 2 c d]
  refine Finset.sum_eq_zero fun κ _ => ?_
  by_cases hκ : ∑ s, lightConeWeight (κ s) = 0
  · rw [lightConeComponent_eq_zero_of_weight_zero hn hc 2 hκ, mul_zero]
  · rw [hc.lightConeComponent_eq_zero 2 hκ, mul_zero]

/-!

## C. The invariants of an equivariant map

The invariants of the range of an equivariant map come from invariant tensors, whose coefficient
tensors are invariant, so section B leaves none of them.

-/

variable {f : ℂT(fun _ : Fin n => Color.up) →ₗ[ℂ] B}

/-- Every Lorentz invariant in the range of `f` is zero. An odd number of indices carries no
  invariant contraction. -/
lemma eq_zero_of_invariant (hn : Odd n) (hf : IsLorentzCovariant n B repLorentz f) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 :=
  hf.eq_zero_of_isInvariantCoeff (fun _ hc => eq_zero_of_isInvariantCoeff hn hc) hx hinv

/-- The range of `f` reduces to `⊥`. A Lorentz invariant of `LinearMap.range f ⊔ S`, for `S` a
  Lorentz-stable submodule, lies in `S`. -/
lemma reducesInvariantsTo_bot (hn : Odd n) (hf : IsLorentzCovariant n B repLorentz f) :
    ReducesInvariantsTo (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) ⊥ :=
  hf.reducesInvariantsTo_bot_of_isInvariantCoeff fun _ hc => eq_zero_of_isInvariantCoeff hn hc

end OddRank

end Lorentz
