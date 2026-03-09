/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.Basic
/-!
# Dimension 7 plane

We work here in the three family case.
We give an example of a 7 dimensional plane on which every point satisfies the ACCs.

The main result of this file is `seven_dim_plane_exists` which states that there exists a
7 dimensional plane of charges on which every point satisfies the ACCs.
-/

@[expose] public section

namespace SMRHN
namespace SM
open SMνCharges
open SMνACCs
open BigOperators

namespace PlaneSeven

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₀ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 0, 0 => 1
  | 0, 1 => - 1
  | _, _ => 0)

lemma B₀_cubic (S T : (SM 3).Charges) : cubeTriLin B₀ S T =
    6 * (S (0 : Fin 18) * T (0 : Fin 18) - S (1 : Fin 18) * T (1 : Fin 18)) := by
  simp only [B₀, Equiv.invFun_as_coe, cubeTriLin_toFun_apply_apply, Nat.reduceMul, finProdFinEquiv,
    Fin.divNat, Fin.modNat, Fin.isValue, Equiv.coe_fn_mk, Fin.val_zero, mul_zero, add_zero,
    toSpeciesEquiv_symm_apply, Fin.val_one, mul_one, Nat.ofNat_pos, Nat.add_div_right,
    Nat.add_mod_right, Fin.val_two, Nat.add_mul_mod_self_left, Fin.sum_univ_three, Fin.zero_eta,
    one_mul, zero_add, Fin.reduceFinMk, zero_mul, Fin.mk_one, neg_mul, mul_neg, Nat.reduceAdd]
  ring

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₁ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 1, 0 => 1
  | 1, 1 => - 1
  | _, _ => 0)

lemma B₁_cubic (S T : (SM 3).Charges) : cubeTriLin B₁ S T =
    3 * (S (3 : Fin 18) * T (3 : Fin 18) - S (4 : Fin 18) * T (4 : Fin 18)) := by
  simp only [B₁, Equiv.invFun_as_coe, cubeTriLin_toFun_apply_apply, Nat.reduceMul, finProdFinEquiv,
    Fin.divNat, Fin.modNat, Fin.isValue, Equiv.coe_fn_mk, Fin.val_zero, mul_zero, add_zero,
    toSpeciesEquiv_symm_apply, Fin.val_one, mul_one, Nat.ofNat_pos, Nat.add_div_right,
    Nat.add_mod_right, Fin.val_two, Nat.add_mul_mod_self_left, Fin.sum_univ_three, Fin.zero_eta,
    zero_mul, zero_add, Fin.reduceFinMk, one_mul, Fin.mk_one, Nat.reduceAdd, neg_mul, mul_neg]
  ring

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₂ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 2, 0 => 1
  | 2, 1 => - 1
  | _, _ => 0)

lemma B₂_cubic (S T : (SM 3).Charges) : cubeTriLin B₂ S T =
    3 * (S (6 : Fin 18) * T (6 : Fin 18) - S (7 : Fin 18) * T (7 : Fin 18)) := by
  simp only [B₂, Equiv.invFun_as_coe, cubeTriLin_toFun_apply_apply, Nat.reduceMul, finProdFinEquiv,
    Fin.divNat, Fin.modNat, Fin.isValue, Equiv.coe_fn_mk, Fin.val_zero, mul_zero, add_zero,
    toSpeciesEquiv_symm_apply, Fin.val_one, mul_one, Nat.ofNat_pos, Nat.add_div_right,
    Nat.add_mod_right, Fin.val_two, Nat.add_mul_mod_self_left, Fin.sum_univ_three, Fin.zero_eta,
    zero_mul, zero_add, Fin.reduceFinMk, one_mul, Fin.mk_one, Nat.reduceAdd, neg_mul, mul_neg]
  ring

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₃ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 3, 0 => 1
  | 3, 1 => - 1
  | _, _ => 0)

lemma B₃_cubic (S T : (SM 3).Charges) : cubeTriLin B₃ S T =
    2 * (S (9 : Fin 18) * T (9 : Fin 18) - S (10 : Fin 18) * T (10 : Fin 18)) := by
  simp only [B₃, Equiv.invFun_as_coe, cubeTriLin_toFun_apply_apply, Nat.reduceMul, finProdFinEquiv,
    Fin.divNat, Fin.modNat, Fin.isValue, Equiv.coe_fn_mk, Fin.val_zero, mul_zero, add_zero,
    toSpeciesEquiv_symm_apply, Fin.val_one, mul_one, Nat.ofNat_pos, Nat.add_div_right,
    Nat.add_mod_right, Fin.val_two, Nat.add_mul_mod_self_left, Fin.sum_univ_three, Fin.zero_eta,
    zero_mul, zero_add, Fin.reduceFinMk, one_mul, Fin.mk_one, Nat.reduceAdd, neg_mul, mul_neg]
  ring_nf
  rfl

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₄ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 4, 0 => 1
  | 4, 1 => - 1
  | _, _ => 0)

lemma B₄_cubic (S T : (SM 3).Charges) : cubeTriLin B₄ S T =
    (S (12 : Fin 18) * T (12 : Fin 18) - S (13 : Fin 18) * T (13 : Fin 18)) := by
  simp only [B₄, Equiv.invFun_as_coe, cubeTriLin_toFun_apply_apply, Nat.reduceMul, finProdFinEquiv,
    Fin.divNat, Fin.modNat, Fin.isValue, Equiv.coe_fn_mk, Fin.val_zero, mul_zero, add_zero,
    toSpeciesEquiv_symm_apply, Fin.val_one, mul_one, Nat.ofNat_pos, Nat.add_div_right,
    Nat.add_mod_right, Fin.val_two, Nat.add_mul_mod_self_left, Fin.sum_univ_three, Fin.zero_eta,
    zero_mul, zero_add, Fin.reduceFinMk, one_mul, Fin.mk_one, Nat.reduceAdd, neg_mul]
  ring_nf
  rfl

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₅ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 5, 0 => 1
  | 5, 1 => - 1
  | _, _ => 0)

lemma B₅_cubic (S T : (SM 3).Charges) : cubeTriLin B₅ S T =
    (S (15 : Fin 18) * T (15 : Fin 18) - S (16 : Fin 18) * T (16 : Fin 18)) := by
  simp only [B₅, Equiv.invFun_as_coe, cubeTriLin_toFun_apply_apply, Nat.reduceMul, finProdFinEquiv,
    Fin.divNat, Fin.modNat, Fin.isValue, Equiv.coe_fn_mk, Fin.val_zero, mul_zero, add_zero,
    toSpeciesEquiv_symm_apply, Fin.val_one, mul_one, Nat.ofNat_pos, Nat.add_div_right,
    Nat.add_mod_right, Fin.val_two, Nat.add_mul_mod_self_left, Fin.sum_univ_three, Fin.zero_eta,
    zero_mul, zero_add, Fin.reduceFinMk, one_mul, Fin.mk_one, Nat.reduceAdd, neg_mul]
  ring_nf
  rfl

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₆ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 1, 2 => 1
  | 2, 2 => -1
  | _, _ => 0)

lemma B₆_cubic (S T : (SM 3).Charges) : cubeTriLin B₆ S T =
    3 * (S (5 : Fin 18) * T (5 : Fin 18) - S (8 : Fin 18) * T (8 : Fin 18)) := by
  simp only [B₆, Equiv.invFun_as_coe, cubeTriLin_toFun_apply_apply, Nat.reduceMul, finProdFinEquiv,
    Fin.divNat, Fin.modNat, Fin.isValue, Equiv.coe_fn_mk, Fin.val_zero, mul_zero, add_zero,
    toSpeciesEquiv_symm_apply, Fin.val_one, mul_one, Nat.ofNat_pos, Nat.add_div_right,
    Nat.add_mod_right, Fin.val_two, Nat.add_mul_mod_self_left, Fin.sum_univ_three, Fin.zero_eta,
    zero_mul, zero_add, Fin.reduceFinMk, Fin.mk_one, Nat.reduceAdd, one_mul, neg_mul, mul_neg]
  ring_nf

TODO "7SQUT" "Remove the definitions of elements `(SM 3).Charges` B₀, B₁ etc, here are
  use only `B : Fin 7 → (SM 3).Charges`. "
/-- The charge assignments forming a basis of the plane. -/
@[simp]
abbrev B : Fin 7 → (SM 3).Charges := fun i =>
  match i with
  | 0 => B₀
  | 1 => B₁
  | 2 => B₂
  | 3 => B₃
  | 4 => B₄
  | 5 => B₅
  | 6 => B₆

lemma B₀_Bi_cubic {i : Fin 7} (hi : 0 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 0) (B i) S = 0 := by
  change cubeTriLin B₀ (B i) S = 0
  rw [B₀_cubic]
  norm_num
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.mk_one,
      Fin.reduceFinMk, not_true_eq_false] at hi <;>
    simp [B₁, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat]

lemma B₁_Bi_cubic {i : Fin 7} (hi : 1 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 1) (B i) S = 0 := by
  change cubeTriLin B₁ (B i) S = 0
  rw [B₁_cubic]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.mk_one,
      Fin.reduceFinMk, not_true_eq_false] at hi <;>
    simp [B₀, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat]

lemma B₂_Bi_cubic {i : Fin 7} (hi : 2 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 2) (B i) S = 0 := by
  change cubeTriLin B₂ (B i) S = 0
  rw [B₂_cubic]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.mk_one,
      Fin.reduceFinMk, not_true_eq_false] at hi <;>
    simp [B₀, B₁, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat]

lemma B₃_Bi_cubic {i : Fin 7} (hi : 3 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 3) (B i) S = 0 := by
  change cubeTriLin (B₃) (B i) S = 0
  rw [B₃_cubic]
  fin_cases i <;>
  simp only [Fin.isValue, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.mk_one,
    Fin.reduceFinMk, not_true_eq_false] at hi <;>
  simp [B₀, B₁, B₂, B₄, B₅, B₆, Fin.divNat, Fin.modNat]

lemma B₄_Bi_cubic {i : Fin 7} (hi : 4 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 4) (B i) S = 0 := by
  change cubeTriLin (B₄) (B i) S = 0
  rw [B₄_cubic]
  fin_cases i <;>
  simp only [Fin.isValue, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.mk_one,
    Fin.reduceFinMk, not_true_eq_false] at hi <;>
  simp [B₀, B₁, B₂, B₃, B₅, B₆, Fin.divNat, Fin.modNat]

lemma B₅_Bi_cubic {i : Fin 7} (hi : 5 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 5) (B i) S = 0 := by
  change cubeTriLin (B₅) (B i) S = 0
  rw [B₅_cubic]
  fin_cases i <;>
  simp only [Fin.isValue, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.mk_one,
    Fin.reduceFinMk, not_true_eq_false] at hi <;>
  simp [B₀, B₁, B₂, B₃, B₄, B₆, Fin.divNat, Fin.modNat]

lemma B₆_Bi_cubic {i : Fin 7} (hi : 6 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 6) (B i) S = 0 := by
  change cubeTriLin (B₆) (B i) S = 0
  rw [B₆_cubic]
  fin_cases i <;>
  simp only [Fin.isValue, Fin.zero_eta, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.mk_one,
    Fin.reduceFinMk, not_true_eq_false] at hi <;>
  simp [B₀, B₁, B₂, B₃, B₄, B₅, Fin.divNat, Fin.modNat]

lemma Bi_Bj_ne_cubic {i j : Fin 7} (h : i ≠ j) (S : (SM 3).Charges) :
    cubeTriLin (B i) (B j) S = 0 := by
  fin_cases i
  · exact B₀_Bi_cubic h S
  · exact B₁_Bi_cubic h S
  · exact B₂_Bi_cubic h S
  · exact B₃_Bi_cubic h S
  · exact B₄_Bi_cubic h S
  · exact B₅_Bi_cubic h S
  · exact B₆_Bi_cubic h S

lemma Bi_Bi_Bj_cubic (i j : Fin 7) :
    cubeTriLin (B i) (B i) (B j) = 0 := by
  with_unfolding_all decide +revert

lemma Bi_Bj_Bk_cubic (i j k : Fin 7) :
    cubeTriLin (B i) (B j) (B k) = 0 := by
  by_cases hij : i ≠ j
  · exact Bi_Bj_ne_cubic hij (B k)
  · simp only [ne_eq, Decidable.not_not] at hij
    rw [hij]
    exact Bi_Bi_Bj_cubic j k

theorem B_in_accCube (f : Fin 7 → ℚ) : accCube (∑ i, f i • B i) = 0 := by
  change cubeTriLin _ _ _ = 0
  rw [cubeTriLin.map_sum₁₂₃]
  apply Fintype.sum_eq_zero _ fun i ↦ Fintype.sum_eq_zero _ fun k ↦ Fintype.sum_eq_zero _ fun l ↦ ?_
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃, Bi_Bj_Bk_cubic]
  simp

lemma B_sum_is_sol (f : Fin 7 → ℚ) : (SM 3).IsSolution (∑ i, f i • B i) := by
  let X := chargeToAF (∑ i, f i • B i) (by
    rw [map_sum]
    apply Fintype.sum_eq_zero _ fun i ↦ ?_
    rw [map_smul]
    refine smul_eq_zero_of_right (f i) ?_
    with_unfolding_all decide +revert)
    (by
      rw [map_sum]
      apply Fintype.sum_eq_zero _ fun i ↦ ?_
      rw [map_smul]
      refine smul_eq_zero_of_right (f i) ?_
      with_unfolding_all decide +revert)
    (by
      rw [map_sum]
      apply Fintype.sum_eq_zero _ fun i ↦ ?_
      rw [map_smul]
      refine smul_eq_zero_of_right (f i) ?_
      with_unfolding_all decide +revert)
    (B_in_accCube f)
  use X
  rfl

theorem basis_linear_independent : LinearIndependent ℚ B := by
  refine Fintype.linearIndependent_iff.mpr fun f h ↦ ?_
  have h0 := congrFun h (0 : Fin 18)
  have h1 := congrFun h (3 : Fin 18)
  have h2 := congrFun h (6 : Fin 18)
  have h3 := congrFun h (9 : Fin 18)
  have h4 := congrFun h (12 : Fin 18)
  have h5 := congrFun h (15 : Fin 18)
  have h6 := congrFun h (5 : Fin 18)
  rw [@Fin.sum_univ_seven] at h0 h1 h2 h3 h4 h5 h6
  simp only [HSMul.hSMul, Fin.isValue, B, ACCSystemCharges.chargesAddCommMonoid_add,
    ACCSystemCharges.chargesModule_smul] at h0 h1 h2 h3 h4 h5 h6
  rw [B₀, B₁, B₂, B₃, B₄, B₅, B₆] at h0 h1 h2 h3 h4 h5 h6
  simp only [Fin.isValue, Equiv.invFun_as_coe, toSpeciesEquiv_symm_apply, Fin.divNat, Nat.reduceMul,
    Fin.val_zero, Nat.zero_div, Fin.zero_eta, Fin.modNat, Nat.zero_mod, mul_one, mul_zero, add_zero,
    zero_add,] at h0 h1 h2 h3 h4 h5 h6
  intro i
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | 6 => exact h6

end PlaneSeven

theorem seven_dim_plane_exists : ∃ (B : Fin 7 → (SM 3).Charges),
    LinearIndependent ℚ B ∧ ∀ (f : Fin 7 → ℚ), (SM 3).IsSolution (∑ i, f i • B i) :=
  ⟨PlaneSeven.B, And.intro PlaneSeven.basis_linear_independent PlaneSeven.B_sum_is_sol⟩

end SM
end SMRHN
