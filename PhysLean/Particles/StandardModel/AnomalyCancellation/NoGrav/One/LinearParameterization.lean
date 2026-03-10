/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.StandardModel.AnomalyCancellation.NoGrav.Basic
public import Mathlib.NumberTheory.FLT.Three
/-!
# Parameterizations for solutions to the linear ACCs for 1 family

In this file we give two parameterizations
- `linearParameters` of solutions to the linear ACCs for 1 family
- `linearParametersQENeqZero` of solutions to the linear ACCs for 1 family with Q and E non-zero

These parameterizations are based on:
https://arxiv.org/abs/1907.00514
-/

@[expose] public section

namespace SM
namespace SMNoGrav
namespace One

open SMCharges
open SMACCs
open BigOperators

/-- The parameters for a linear parameterization to the solution of the linear ACCs. -/
structure linearParameters where
  /-- The parameter `Q'`. -/
  Q' : ℚ
  /-- The parameter `Y`. -/
  Y : ℚ
  /-- The parameter `E'`. -/
  E' : ℚ

namespace linearParameters

@[ext]
lemma ext {S T : linearParameters} (hQ : S.Q' = T.Q') (hY : S.Y = T.Y) (hE : S.E' = T.E') :
    S = T := by
  cases' S
  simp_all only

/-- The map from the linear parameters to elements of `(SMNoGrav 1).charges`. -/
@[simp]
def asCharges (S : linearParameters) : (SMNoGrav 1).Charges := fun i =>
  match i with
  | (0 : Fin 5) => S.Q'
  | (1 : Fin 5) => S.Y - S.Q'
  | (2 : Fin 5) => - (S.Y + S.Q')
  | (3: Fin 5) => - 3 * S.Q'
  | (4 : Fin 5) => S.E'

lemma speciesVal (S : linearParameters) :
    (toSpecies i) S.asCharges (0 : Fin 1) = S.asCharges i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl

/-- The map from the linear parameters to elements of `(SMNoGrav 1).LinSols`. -/
def asLinear (S : linearParameters) : (SMNoGrav 1).LinSols :=
  chargeToLinear S.asCharges (by
    simp only [accSU2, SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
    erw [speciesVal, speciesVal]
    simp)
    (by
    simp only [accSU3, SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
    repeat erw [speciesVal]
    simp only [asCharges, neg_add_rev]
    ring)

lemma asLinear_val (S : linearParameters) : S.asLinear.val = S.asCharges := by
  rfl

lemma cubic (S : linearParameters) :
    accCube (S.asCharges) = - 54 * S.Q'^3 - 18 * S.Q' * S.Y ^ 2 + S.E'^3 := by
  simp only [HomogeneousCubic, accCube, cubeTriLin, TriLinearSymm.toCubic_apply,
    TriLinearSymm.mk₃_toFun_apply_apply]
  simp only [SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton]
  repeat erw [speciesVal]
  simp only [asCharges, neg_add_rev, neg_mul, mul_neg, neg_neg]
  ring

lemma cubic_zero_Q'_zero (S : linearParameters) (hc : accCube (S.asCharges) = 0)
    (h : S.Q' = 0) : S.E' = 0 := by
  rw [cubic, h] at hc
  simpa using hc

lemma cubic_zero_E'_zero (S : linearParameters) (hc : accCube (S.asCharges) = 0)
    (h : S.E' = 0) : S.Q' = 0 := by
  rw [cubic, h] at hc
  simp only [neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hc
  have h1 : -(54 * S.Q' ^ 3) - 18 * S.Q' * S.Y ^ 2 = - 18 * (3 * S.Q' ^ 2 + S.Y ^ 2) * S.Q' := by
    ring
  rw [h1] at hc
  simp only [neg_mul, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hc
  cases' hc with hc hc
  · have h2 := (add_eq_zero_iff_of_nonneg (by nlinarith) (sq_nonneg S.Y)).mp hc
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff,
      false_or] at h2
    exact h2.1
  · exact hc

/-- The bijection between the type of linear parameters and `(SMNoGrav 1).LinSols`. -/
def bijection : linearParameters ≃ (SMNoGrav 1).LinSols where
  toFun S := S.asLinear
  invFun S := ⟨SMCharges.Q S.val (0 : Fin 1), (SMCharges.U S.val (0 : Fin 1) -
      SMCharges.D S.val (0 : Fin 1))/2,
      SMCharges.E S.val (0 : Fin 1)⟩
  left_inv S := by
    apply linearParameters.ext
    · rfl
    · simp only [Fin.isValue]
      repeat erw [speciesVal]
      simp only [asCharges, neg_add_rev]
      ring
    · rfl
  right_inv S := by
    simp only [Fin.isValue, toSpecies_apply]
    apply ACCSystemLinear.LinSols.ext
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [asLinear_val]
    funext j
    have hj : j = (0 : Fin 1) := by
      simp only [SMSpecies_numberCharges, Fin.isValue]
      ext
      simp
    subst hj
    erw [speciesVal]
    have h1 := SU3Sol S
    simp only [accSU3, SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, toSpecies_apply, Nat.reduceMul, Finset.sum_singleton, Prod.mk_zero_zero,
      LinearMap.coe_mk, AddHom.coe_mk] at h1
    have h2 := SU2Sol S
    simp only [accSU2, SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, toSpecies_apply, Nat.reduceMul, Finset.sum_singleton, Prod.mk_zero_zero,
      LinearMap.coe_mk, AddHom.coe_mk] at h2
    match i with
    | 0 => rfl
    | 1 =>
      simp only [asCharges, Nat.reduceMul, Fin.isValue, toSpecies_apply]
      field_simp
      linear_combination -(1 * h1)
    | 2 =>
      simp only [asCharges, Nat.reduceMul, Fin.isValue, neg_add_rev, toSpecies_apply]
      field_simp
      linear_combination -(1 * h1)
    | 3 =>
      simp only [asCharges, Nat.reduceMul, Fin.isValue, neg_mul, toSpecies_apply]
      field_simp
      linear_combination -(1 * h2)
    | 4 => rfl

/-- The bijection between the linear parameters and `(SMNoGrav 1).LinSols` in the special
case when Q and E are both not zero. -/
def bijectionQEZero : {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} ≃
    {S : (SMNoGrav 1).LinSols // Q S.val (0 : Fin 1) ≠ 0 ∧ E S.val (0 : Fin 1) ≠ 0} where
  toFun S := ⟨bijection S, S.2⟩
  invFun S := ⟨bijection.symm S, S.2⟩
  left_inv S := Subtype.ext (bijection.left_inv S.1)
  right_inv S := Subtype.ext (bijection.right_inv S.1)

lemma grav (S : linearParameters) :
    accGrav S.asCharges = 0 ↔ S.E' = 6 * S.Q' := by
  rw [accGrav]
  simp only [SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
  repeat erw [speciesVal]
  simp only [asCharges, neg_add_rev, neg_mul, mul_neg]
  ring_nf
  rw [add_comm, add_eq_zero_iff_eq_neg]
  simp

end linearParameters

/-- The parameters for solutions to the linear ACCs with the condition that Q and E are
  non-zero. -/
structure linearParametersQENeqZero where
  /-- The parameter `x`. -/
  x : ℚ
  /-- The parameter `v`. -/
  v : ℚ
  /-- The parameter `w`. -/
  w : ℚ
  hx : x ≠ 0
  hvw : v + w ≠ 0

namespace linearParametersQENeqZero

@[ext]
lemma ext {S T : linearParametersQENeqZero} (hx : S.x = T.x) (hv : S.v = T.v)
    (hw : S.w = T.w) : S = T := by
  cases' S
  simp_all only

/-- A map from `linearParametersQENeqZero` to `linearParameters`. -/
@[simps!]
def toLinearParameters (S : linearParametersQENeqZero) :
    {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} :=
  ⟨⟨S.x, 3 * S.x * (S.v - S.w) / (S.v + S.w), - 6 * S.x / (S.v + S.w)⟩,
    by
      apply And.intro S.hx
      simp only [neg_mul, ne_eq, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
        false_or]
      rw [not_or]
      exact And.intro S.hx S.hvw⟩

/-- A map from `linearParameters` to `linearParametersQENeqZero` in the special case when
`Q'` and `E'` of the linear parameters are non-zero. -/
@[simps!]
def tolinearParametersQNeqZero (S : {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0}) :
    linearParametersQENeqZero :=
  ⟨S.1.Q', - (3 * S.1.Q' + S.1.Y) / S.1.E', - (3 * S.1.Q' - S.1.Y)/ S.1.E', S.2.1,
    by
      simp only [ne_eq, neg_add_rev, neg_sub]
      field_simp
      ring_nf
      simp only [neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, or_false]
      simpa using S.2⟩

/-- A bijection between the type `linearParametersQENeqZero` and linear parameters
  with `Q'` and `E'` non-zero. -/
@[simps!]
def bijectionLinearParameters :
    linearParametersQENeqZero ≃ {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} where
  toFun := toLinearParameters
  invFun := tolinearParametersQNeqZero
  left_inv S := by
    have hvw := S.hvw
    have hQ := S.hx
    apply linearParametersQENeqZero.ext
    · rfl
    · simp only [tolinearParametersQNeqZero_v, toLinearParameters_coe_Y, toLinearParameters_coe_Q',
      toLinearParameters_coe_E']
      field_simp
      ring
    · simp only [tolinearParametersQNeqZero_w, toLinearParameters_coe_Y, toLinearParameters_coe_Q',
        toLinearParameters_coe_E']
      field_simp
      ring
  right_inv S := by
    apply Subtype.ext
    have hQ := S.2.1
    have hE := S.2.2
    apply linearParameters.ext
    · rfl
    · simp only [ne_eq, toLinearParameters_coe_Y, tolinearParametersQNeqZero_x,
      tolinearParametersQNeqZero_v, tolinearParametersQNeqZero_w]
      field_simp
      ring_nf
      field_simp [hQ, hE]
    · simp only [ne_eq, toLinearParameters_coe_E', tolinearParametersQNeqZero_x,
      tolinearParametersQNeqZero_v, tolinearParametersQNeqZero_w]
      field_simp
      ring_nf
      field_simp [hQ, hE]

/-- The bijection between `linearParametersQENeqZero` and `LinSols` with `Q` and `E` non-zero. -/
def bijection : linearParametersQENeqZero ≃
    {S : (SMNoGrav 1).LinSols // Q S.val (0 : Fin 1) ≠ 0 ∧ E S.val (0 : Fin 1) ≠ 0} :=
  bijectionLinearParameters.trans (linearParameters.bijectionQEZero)

lemma cubic (S : linearParametersQENeqZero) :
    accCube (bijection S).1.val = 0 ↔ S.v ^ 3 + S.w ^ 3 = -1 := by
  erw [linearParameters.cubic]
  simp only [ne_eq, bijectionLinearParameters_apply_coe_Q', neg_mul,
    bijectionLinearParameters_apply_coe_Y, div_pow, bijectionLinearParameters_apply_coe_E']
  have hvw := S.hvw
  have hQ := S.hx
  field_simp
  simp [hQ]
  ring_nf
  have h1 : -216 + (-(S.v ^ 3 * 216) - S.w ^ 3 * 216) = - 216 *(S.v ^3 + S.w ^3 +1) := by
    ring
  rw [h1]
  simp_all
  exact add_eq_zero_iff_eq_neg

lemma cubic_v_or_w_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0) :
    S.v = 0 ∨ S.w = 0 := by
  rw [S.cubic] at h
  have h1 : (-1)^3 = (-1 : ℚ) := by rfl
  rw [← h1] at h
  by_contra hn
  rw [not_or] at hn
  have FLTThree := fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree
  have h2 := FLTThree S.v S.w (-1) hn.1 hn.2 (Ne.symm (ne_of_beq_false (by rfl)))
  exact h2 h

lemma cubic_v_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (hv : S.v = 0) : S.w = -1 := by
  rw [S.cubic, hv] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  have h' : (S.w + 1) * (1 * S.w * S.w + (-1) * S.w + 1) = 0 := by
    ring_nf
    exact add_eq_zero_iff_neg_eq.mpr (id (Eq.symm h))
  have h'' : (1 * (S.w * S.w) + (-1) * S.w + 1) ≠ 0 := by
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ S.w
    intro s
    by_contra hn
    have h : s ^ 2 < 0 := by
      rw [← hn]
      with_unfolding_all rfl
    nlinarith
  simp_all
  exact eq_neg_of_add_eq_zero_left h'

lemma cube_w_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (hw : S.w = 0) : S.v = -1 := by
  rw [S.cubic, hw] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  have h' : (S.v + 1) * (1 * S.v * S.v + (-1) * S.v + 1) = 0 := by
    ring_nf
    exact add_eq_zero_iff_neg_eq.mpr (id (Eq.symm h))
  have h'' : (1 * (S.v * S.v) + (-1) * S.v + 1) ≠ 0 := by
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ S.v
    intro s
    by_contra hn
    have h : s ^ 2 < 0 := by
      rw [← hn]
      with_unfolding_all rfl
    nlinarith
  simp_all only [one_mul, neg_mul, mul_eq_zero, ne_eq, or_false]
  exact eq_neg_of_add_eq_zero_left h'

lemma cube_w_v (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0) :
    (S.v = -1 ∧ S.w = 0) ∨ (S.v = 0 ∧ S.w = -1) := by
  have h' := cubic_v_or_w_zero S h
  cases' h' with hx hx
  · simpa [hx] using cubic_v_zero S h hx
  · simpa [hx] using cube_w_zero S h hx

lemma grav (S : linearParametersQENeqZero) : accGrav (bijection S).1.val = 0 ↔ S.v + S.w = -1 := by
  erw [linearParameters.grav]
  have hvw := S.hvw
  have hQ := S.hx
  field_simp
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · apply (mul_right_inj' hQ).mp
    simp at h
    field_simp at h
    rw [← h]
  · simp [h]

lemma grav_of_cubic (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0) :
    accGrav (bijection S).1.val = 0 := by
  rw [grav]
  have h' := cube_w_v S h
  cases' h' with h h
  · rw [h.1, h.2]
    exact Rat.add_zero (-1)
  · rw [h.1, h.2]
    exact Rat.zero_add (-1)

end linearParametersQENeqZero

end One
end SMNoGrav
end SM
