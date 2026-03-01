/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic
import Mathlib.Tactic.LinearCombination
/-!
# Plane of non-solutions

Working in the three family case, we show that there exists an eleven dimensional plane in the
vector space of charges on which there are no solutions.

The main result of this file is `eleven_dim_plane_of_no_sols_exists`, which states that
an 11 dimensional plane of charges exists on which there are no solutions except the origin.
-/

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

namespace ElevenPlane

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₀ : (PlusU1 3).Charges := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₁ : (PlusU1 3).Charges := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₂ : (PlusU1 3).Charges := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₃ : (PlusU1 3).Charges := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₄ : (PlusU1 3).Charges := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₅ : (PlusU1 3).Charges := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₆ : (PlusU1 3).Charges := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₇ : (PlusU1 3).Charges := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₈ : (PlusU1 3).Charges := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₉ : (PlusU1 3).Charges := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0]

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₁₀ : (PlusU1 3).Charges := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The charge assignment forming a basis of the plane. -/
def B : Fin 11 → (PlusU1 3).Charges := fun i =>
  match i with
  | 0 => B₀
  | 1 => B₁
  | 2 => B₂
  | 3 => B₃
  | 4 => B₄
  | 5 => B₅
  | 6 => B₆
  | 7 => B₇
  | 8 => B₈
  | 9 => B₉
  | 10 => B₁₀

lemma Bi_Bj_quad {i j : Fin 11} (hi : i ≠ j) : quadBiLin (B i) (B j) = 0 := by
  fin_cases i <;> fin_cases j
  any_goals with_unfolding_all rfl
  all_goals simp at hi

lemma Bi_sum_quad (i : Fin 11) (f : Fin 11 → ℚ) :
    quadBiLin (B i) (∑ k, f k • B k) = f i * quadBiLin (B i) (B i) := by
  rw [quadBiLin.map_sum₂, Fintype.sum_eq_single i]
  · rw [quadBiLin.map_smul₂]
  · intro k hij
    rw [quadBiLin.map_smul₂, Bi_Bj_quad hij.symm]
    exact Rat.mul_zero (f k)

/-- The coefficients of the quadratic equation in our basis. -/
@[simp]
def quadCoeff : Fin 11 → ℚ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0]

lemma quadCoeff_eq_bilinear (i : Fin 11) : quadCoeff i = quadBiLin (B i) (B i) := by
  fin_cases i
  all_goals with_unfolding_all rfl

lemma on_accQuad (f : Fin 11 → ℚ) :
    accQuad (∑ i, f i • B i) = ∑ i, quadCoeff i * (f i)^2 := by
  change quadBiLin _ _ = _
  rw [quadBiLin.map_sum₁]
  refine Fintype.sum_congr _ _ fun i ↦ ?_
  rw [quadBiLin.map_smul₁, Bi_sum_quad, quadCoeff_eq_bilinear]
  ring

lemma isSolution_quadCoeff_f_sq_zero (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i))
    (k : Fin 11) : quadCoeff k * (f k)^2 = 0 := by
  obtain ⟨S, hS⟩ := hS
  have hQ := quadSol S.1
  rw [hS, on_accQuad, Fintype.sum_eq_zero_iff_of_nonneg] at hQ
  · exact congrFun hQ k
  · intro i
    simp only [Pi.zero_apply, quadCoeff]
    rw [mul_nonneg_iff]
    apply Or.inl (And.intro _ _)
    fin_cases i <;> rfl
    exact sq_nonneg (f i)

lemma isSolution_f0 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 0 = 0 := by
  simpa using (isSolution_quadCoeff_f_sq_zero f hS 0)

lemma isSolution_f1 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 1 = 0 := by
  simpa using (isSolution_quadCoeff_f_sq_zero f hS 1)

lemma isSolution_f2 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 2 = 0 := by
  simpa using (isSolution_quadCoeff_f_sq_zero f hS 2)

lemma isSolution_f3 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 3 = 0 := by
  simpa using (isSolution_quadCoeff_f_sq_zero f hS 3)

lemma isSolution_f4 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 4 = 0 := by
  simpa using (isSolution_quadCoeff_f_sq_zero f hS 4)

lemma isSolution_f5 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 5 = 0 := by
  have h := isSolution_quadCoeff_f_sq_zero f hS 5
  rw [mul_eq_zero] at h
  change 1 = 0 ∨ _ = _ at h
  simpa using h

lemma isSolution_f6 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 6 = 0 := by
  have h := isSolution_quadCoeff_f_sq_zero f hS 6
  rw [mul_eq_zero] at h
  change 1 = 0 ∨ _ = _ at h
  simpa using h

lemma isSolution_f7 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 7 = 0 := by
  have h := isSolution_quadCoeff_f_sq_zero f hS 7
  rw [mul_eq_zero] at h
  change 1 = 0 ∨ _ = _ at h
  simpa using h

lemma isSolution_f8 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) : f 8 = 0 := by
  have h := isSolution_quadCoeff_f_sq_zero f hS 8
  rw [mul_eq_zero] at h
  change 1 = 0 ∨ _ = _ at h
  simpa using h

lemma isSolution_sum_part (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) :
    ∑ i, f i • B i = f 9 • B₉ + f 10 • B₁₀ := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  change f 0 • B 0 + f 1 • B 1 + f 2 • B 2 + f 3 • B 3 + f 4 • B 4 + f 5 • B 5 + f 6 • B 6 +
  f 7 • B 7 + f 8 • B 8 + f 9 • B 9 + f 10 • B 10 = f 9 • B₉ + f 10 • B₁₀
  rw [isSolution_f0 f hS, isSolution_f1 f hS, isSolution_f2 f hS, isSolution_f3 f hS,
    isSolution_f4 f hS, isSolution_f5 f hS,
    isSolution_f6 f hS, isSolution_f7 f hS, isSolution_f8 f hS]
  simp only [Fin.isValue, zero_smul, add_zero, zero_add]
  rfl

lemma isSolution_grav (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) :
    f 10 = - 3 * f 9 := by
  have hx := isSolution_sum_part f hS
  obtain ⟨S, hS'⟩ := hS
  have hg := gravSol S.toLinSols
  rw [hS', hx, accGrav.map_add, accGrav.map_smul, accGrav.map_smul,
    show accGrav B₉ = 3 by with_unfolding_all rfl,
    show accGrav B₁₀ = 1 by with_unfolding_all rfl] at hg
  simp only [Fin.isValue, smul_eq_mul, mul_one] at hg
  linear_combination hg

lemma isSolution_sum_part' (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) :
    ∑ i, f i • B i = f 9 • B₉ + (- 3 * f 9) • B₁₀ := by
  rw [isSolution_sum_part f hS, isSolution_grav f hS]

lemma isSolution_f9 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) :
    f 9 = 0 := by
  have hx := isSolution_sum_part' f hS
  obtain ⟨S, hS'⟩ := hS
  have hc := cubeSol S
  rw [hS', hx] at hc
  change cubeTriLin.toCubic _ = _ at hc
  rw [cubeTriLin.toCubic_add] at hc
  erw [accCube.map_smul] at hc
  erw [accCube.map_smul (- 3 * f 9) B₁₀] at hc
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₂,
    cubeTriLin.map_smul₃, cubeTriLin.map_smul₃] at hc
  rw [show accCube B₉ = 9 by with_unfolding_all rfl,
    show accCube B₁₀ = 1 by with_unfolding_all rfl,
    show cubeTriLin B₉ B₉ B₁₀ = 0 by with_unfolding_all rfl,
    show cubeTriLin B₁₀ B₁₀ B₉ = 0 by with_unfolding_all rfl] at hc
  simp only [Fin.isValue, neg_mul, mul_one, mul_zero, add_zero] at hc
  have h1 : f 9 ^ 3 * 9 + (-(3 * f 9)) ^ 3 = - 18 * f 9 ^ 3 := by ring
  rw [h1] at hc
  simpa using hc

lemma isSolution_f10 (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) :
    f 10 = 0 := by
  rw [isSolution_grav f hS, isSolution_f9 f hS]
  with_unfolding_all rfl

lemma isSolution_f_zero (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i))
    (k : Fin 11) : f k = 0 := by
  fin_cases k
  · exact isSolution_f0 f hS
  · exact isSolution_f1 f hS
  · exact isSolution_f2 f hS
  · exact isSolution_f3 f hS
  · exact isSolution_f4 f hS
  · exact isSolution_f5 f hS
  · exact isSolution_f6 f hS
  · exact isSolution_f7 f hS
  · exact isSolution_f8 f hS
  · exact isSolution_f9 f hS
  · exact isSolution_f10 f hS

lemma isSolution_only_if_zero (f : Fin 11 → ℚ) (hS : (PlusU1 3).IsSolution (∑ i, f i • B i)) :
    ∑ i, f i • B i = 0 := by
  rw [isSolution_sum_part f hS, isSolution_grav f hS, isSolution_f9 f hS]
  simp

theorem basis_linear_independent : LinearIndependent ℚ B :=
  Fintype.linearIndependent_iff.mpr fun f h ↦ isSolution_f_zero f
    ⟨chargeToAF 0 (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
      (by with_unfolding_all rfl), id (Eq.symm h)⟩

end ElevenPlane

theorem eleven_dim_plane_of_no_sols_exists : ∃ (B : Fin 11 → (PlusU1 3).Charges),
    LinearIndependent ℚ B ∧
    ∀ (f : Fin 11 → ℚ), (PlusU1 3).IsSolution (∑ i, f i • B i) → ∑ i, f i • B i = 0 :=
  ⟨ElevenPlane.B, ElevenPlane.basis_linear_independent, ElevenPlane.isSolution_only_if_zero⟩

end PlusU1
end SMRHN
