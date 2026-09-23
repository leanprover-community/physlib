/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Data.Fintype.Pi
/-!
# Lorentz invariants of three four-vector indices

A rank-three tensor `T^{μνρ}` has no Lorentz invariant built from its components but `0`.
Nothing ties three indices: the metric takes two and the Levi-Civita symbol four, and an
odd number is left over either way. That is `eq_zero_of_invariant`, and
`mem_of_invariant_of_mem_sup` is the same statement modulo a Lorentz-stable subspace `S`,
the form the Standard Model files use.

The components are vectors `T d` of a complex vector space `B` carrying a representation
`repLorentz` of `SL(2,ℂ)`, indexed by three directions, and `IsLorentzCovariant 3` says the
group moves them with one factor of the Lorentz matrix per slot. `componentSpan T` is the set
of their combinations.

An invariant of the span is `∑_d c_d • T d` for a coefficient tensor `c` that the Lorentz
matrices themselves fix (from `Invariants.Basic`). One axis then does all the work, with a
parity argument in place of a certificate. Along a spatial axis the four light-cone directions
carry boost weights `2`, `-2`, `0`, `0`, and an invariant `c` has no light-cone component of
nonzero weight. In a multi-index of total weight `0` the `+2` and `-2` slots pair off, leaving
an odd number of the three slots transverse. The half turn about the axis, the rotation by `π`,
fixes time and the axis and negates the two transverse directions (A), so it multiplies each
weight-zero component by `-1` to an odd power, that is by `-1`, and an invariant component both
fixed and negated is `0` (B). Every light-cone component of `c` vanishes, so `c` does, and with
it the invariant. Section C divides out `S`.
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C Invariants

/-!

## A. The half turn about a spatial axis

The half turn about the axis `i` is the rotation by `π` about it, `SL2C.halfTurn i`. Its
Lorentz matrix is diagonal, fixing time and the axis and negating the two transverse
directions, so on the light-cone directions of that axis it is `1` on the two of weight
`±2` and `-1` on the two transverse ones (`lightConeSign`).

-/

namespace SL2C

/-- The half turn about the axis `i`: the rotation by `π` about the `i`-th spatial
  axis, written in `SL(2,ℂ)`. -/
noncomputable def halfTurn : Fin 3 → SL(2,ℂ)
  | 0 => ⟨!![0, -Complex.I; -Complex.I, 0], by
      rw [Matrix.det_fin_two_of]
      simp [Complex.I_mul_I]⟩
  | 1 => ⟨!![0, -1; 1, 0], by
      rw [Matrix.det_fin_two_of]
      simp⟩
  | 2 => ⟨!![-Complex.I, 0; 0, Complex.I], by
      rw [Matrix.det_fin_two_of]
      simp [Complex.I_mul_I]⟩

/-- The matrix entries of the half turn about the `x`-axis. -/
@[simp] lemma halfTurn_zero_apply (j k : Fin 2) :
    (halfTurn 0).1 j k = (!![0, -Complex.I; -Complex.I, 0]) j k := rfl

/-- The matrix entries of the half turn about the `y`-axis. -/
@[simp] lemma halfTurn_one_apply (j k : Fin 2) :
    (halfTurn 1).1 j k = (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) j k := rfl

/-- The matrix entries of the half turn about the `z`-axis. -/
@[simp] lemma halfTurn_two_apply (j k : Fin 2) :
    (halfTurn 2).1 j k = (!![-Complex.I, 0; 0, Complex.I]) j k := rfl

/-- The Lorentz matrix of the half turn about the axis `i` is diagonal: it fixes the
  time direction and the axis, and negates the two transverse directions. -/
lemma toLorentzGroup_halfTurn_apply (i : Fin 3) (a b : Fin 1 ⊕ Fin 3) :
    (toLorentzGroup (halfTurn i)).1 a b =
      if a = b then (if b = Sum.inl 0 ∨ b = Sum.inr i then 1 else -1) else 0 := by
  refine Complex.ofReal_injective ?_
  rw [toLorentzGroup_eq_trace, PauliMatrix.trace_pauliSelfAdjoint'_mul_apply]
  fin_cases i <;>
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.ext_iff]

end SL2C

/-- The sign the half turn about an axis gives each light-cone direction of that axis: `1` on
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
      simp [lightConeCoeff, lightConeSign, Fintype.sum_sum_type]
  · fin_cases i <;> fin_cases j <;> fin_cases κ <;>
      simp [lightConeCoeff, lightConeSign, Fintype.sum_sum_type]

/-- The scalar behind the action of the half turn on a light-cone multi-index: the half
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

/-- A light-cone multi-index of three slots and total boost weight zero has an odd
  number of transverse slots, so the half turn acts on it by `-1`. -/
lemma prod_lightConeSign_of_sum_lightConeWeight_eq_zero (c : Fin 3 → Fin 4)
    (hc : (∑ j, lightConeWeight (c j)) = 0) : ∏ j, lightConeSign (c j) = -1 := by
  revert c
  decide

namespace RankThree

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 3 → (Fin 1 ⊕ Fin 3)) → B}

/-!

## B. The classification of the Lorentz invariants

Writing a coefficient tensor in the light-cone basis of one axis leaves only the multi-indices
of total weight zero, the others being killed by the boost. The half turn about that axis
negates exactly those, so they vanish too and nothing is left.

-/

/-- The Lorentz matrix of the half turn is diagonal, hence symmetric. -/
lemma toLorentzGroup_halfTurn_symm (i : Fin 3) (a b : Fin 1 ⊕ Fin 3) :
    (SL2C.toLorentzGroup (SL2C.halfTurn i)).1 a b
      = (SL2C.toLorentzGroup (SL2C.halfTurn i)).1 b a := by
  rw [SL2C.toLorentzGroup_halfTurn_apply, SL2C.toLorentzGroup_halfTurn_apply]
  by_cases h : a = b
  · rw [h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- The half turn multiplies a light-cone component by the product of the signs of its slots. -/
lemma lightConeComponent_act_halfTurn {n : ℕ} (i : Fin 3)
    (c : (Fin n → Fin 1 ⊕ Fin 3) → ℂ) (κ : Fin n → Fin 4) :
    lightConeComponent i (act (SL2C.toLorentzGroup (SL2C.halfTurn i)).1 c) κ
      = ((∏ s, lightConeSign (κ s) : ℤ) : ℂ) * lightConeComponent i c κ :=
  lightConeComponent_act i _ c κ _ fun d => by
    simpa only [toLorentzGroup_halfTurn_symm i (d _)] using
      sum_prod_halfTurn_lightConeCoeff i κ d

/-- An invariant coefficient tensor has no weight-zero light-cone component either, the half
  turn negating those. -/
lemma lightConeComponent_eq_zero_of_weight_zero {c : (Fin 3 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) (i : Fin 3) {κ : Fin 3 → Fin 4}
    (hκ : ∑ s, lightConeWeight (κ s) = 0) : lightConeComponent i c κ = 0 := by
  have h := lightConeComponent_act_halfTurn i c κ
  rw [hc, prod_lightConeSign_of_sum_lightConeWeight_eq_zero κ hκ] at h
  push_cast at h
  linear_combination h / 2

/-- An invariant coefficient tensor is zero: no light-cone component of it survives. -/
lemma eq_zero_of_isInvariantCoeff {c : (Fin 3 → Fin 1 ⊕ Fin 3) → ℂ}
    (hc : IsInvariantCoeff c) : c = 0 := by
  funext d
  show c d = 0
  rw [eq_sum_lightConeComponent 2 c d]
  refine Finset.sum_eq_zero fun κ _ => ?_
  by_cases hκ : ∑ s, lightConeWeight (κ s) = 0
  · rw [lightConeComponent_eq_zero_of_weight_zero hc 2 hκ, mul_zero]
  · rw [hc.lightConeComponent_eq_zero 2 hκ, mul_zero]

/-- Every Lorentz invariant in the span of the components is zero: three indices carry no
  invariant contraction. -/
theorem eq_zero_of_invariant (hT : IsLorentzCovariant 3 B repLorentz T) {x : B}
    (hx : x ∈ componentSpan T) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc, rfl⟩ := hT.exists_isInvariantCoeff_of_mem_componentSpan hx hinv
  simp [eq_zero_of_isInvariantCoeff hc]

/-!

## C. The classification modulo a Lorentz-stable submodule

A stable subspace `S` is divided out by passing to the quotient `B ⧸ S`, that is `B` with
`S` declared zero: the classes of the components again form a triple Lorentz tensor, so
section B applies there and an invariant of `componentSpan T ⊔ S` lies in `S`.

-/

/-- A Lorentz invariant of `componentSpan T ⊔ S`, for a Lorentz-stable subspace `S`, already
  lies in `S`. -/
lemma mem_of_invariant_of_mem_sup (hT : IsLorentzCovariant 3 B repLorentz T) {x : B}
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ componentSpan T ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hzero := eq_zero_of_invariant (hT.quotient S hS) (mkQ_mem_componentSpan T S hx)
    fun g => by rw [quotient_apply_mkQ, hinv g]
  rwa [← Submodule.ker_mkQ S, LinearMap.mem_ker]

end RankThree

end Lorentz
