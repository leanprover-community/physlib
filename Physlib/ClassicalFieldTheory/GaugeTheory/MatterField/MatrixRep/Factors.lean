/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Factor
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Constructions
public import Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.Charge
/-!
# The factors of a gauge group as matrix representations

## i. Overview

A model-building table assigns to each field one charge per factor of the gauge group: a
rational charge under a `U(1)` factor, a representation label under an `SU(n)` factor.
The factors themselves, `LocalGaugeData.U1Factor` and `LocalGaugeData.SUFactor`, are part
of the gauge data (`Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Factor`). This
file builds the representations they name: `U1Factor.charge n R` twists a matrix
representation `R` by the charge-`n` power of the unitary jet, and `SUFactor.fund` is the
fundamental representation. Together with `MatrixRep.trivial`, `MatrixRep.kron` and
`MatrixRep.conj`, every representation named in a table is assembled from these.

## ii. Key results

- `U1Factor.charge` : the charge twist of a matrix representation by a `U(1)` factor.
- `MatterField.pderiv_chargePow` : the derivative of a power of a unitary jet.
- `SUFactor.fund` : the fundamental representation of an `SU(n)` factor.

## iii. Table of contents

- A. Powers of a unitary jet
- B. The charge twist of a `U(1)` factor
- C. The fundamental representation of an `SU(n)` factor

-/

@[expose] public section

open TensorProduct MvPowerSeries

/-!

## A. Powers of a unitary jet

-/

namespace MatterField

/-- **The derivative of a power of a unitary jet**: `∂_μ (u ^ n) = n · u ^ n · (u⁻¹ ∂_μ u)`,
  for every integer `n`. -/
lemma pderiv_chargePow (n : ℤ) (w : unitary SpaceTimeAlgebra) (μ : Fin 1 ⊕ Fin 3) :
    pderiv μ (chargePow n w)
      = (n : ℂ) •
          (chargePow n w * (star (w : SpaceTimeAlgebra) * pderiv μ (w : SpaceTimeAlgebra))) := by
  have hws : (w : SpaceTimeAlgebra) * star (w : SpaceTimeAlgebra) = 1 :=
      Unitary.mul_star_self_of_mem w.2
  have hsw : star (w : SpaceTimeAlgebra) * (w : SpaceTimeAlgebra) = 1 :=
      Unitary.star_mul_self_of_mem w.2
  have hD : pderiv μ (star (w : SpaceTimeAlgebra))
      = -(star (w : SpaceTimeAlgebra)) ^ 2 • pderiv μ (w : SpaceTimeAlgebra) :=
    Derivation.leibniz_of_mul_eq_one _ hsw
  rcases n with k | k
  · rw [show chargePow (Int.ofNat k) w = (w : SpaceTimeAlgebra) ^ k from by simp [chargePow],
      Derivation.leibniz_pow]
    rcases k with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ, mul_assoc,
        ← mul_assoc (w : SpaceTimeAlgebra) (star _) _, hws, one_mul]
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast, smul_eq_mul, nsmul_eq_mul,
        Algebra.smul_def, map_natCast]
  · rw [show chargePow (Int.negSucc k) w = (star (w : SpaceTimeAlgebra)) ^ (k + 1) from by
        simp [chargePow, zpow_negSucc, ← Unitary.star_eq_inv],
      Derivation.leibniz_pow, hD, Nat.add_sub_cancel, Int.cast_negSucc]
    simp only [smul_eq_mul, nsmul_eq_mul, Algebra.smul_def, map_neg, map_natCast]
    ring

end MatterField

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]

/-!

## B. The charge twist of a `U(1)` factor

-/

namespace U1Factor

variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (F : U1Factor jets)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

open MatterField

/-- The derivative of the charge-`n` power of the unitary jet of a gauge jet, in terms of
  the Maurer–Cartan form: `∂_μ (u ^ n) = -(i n) φJ (ω_μ U) · u ^ n`. -/
lemma pderiv_chargePow_u (n : ℤ) (U : GJ) (μ : Fin 1 ⊕ Fin 3) :
    pderiv μ (chargePow n (F.u U))
      = -(((Complex.I * n) • F.φJ (jets.maurerCartan U μ)) * chargePow n (F.u U)) := by
  rw [pderiv_chargePow, F.φJ_maurerCartan, smul_smul,
    show Complex.I * n * Complex.I = -(n : ℂ) from by
      rw [mul_comm Complex.I, mul_assoc, Complex.I_mul_I, mul_neg_one],
    neg_smul, neg_mul, neg_neg,
    smul_mul_assoc]
  congr 1
  ring

/-- **The charge twist**: a matrix representation twisted by the charge-`n` power of the
  unitary jet of the `U(1)` factor. The gauge algebra acts by the original action plus
  `i n` times the `u(1)` component. -/
noncomputable def charge (n : ℤ) (R : MatrixRep jets ι) : MatrixRep jets ι where
  mat U := chargePow n (F.u U) • R.mat U
  mat_one := by rw [map_one, chargePow_one, one_smul, R.mat_one]
  mat_mul U V := by
    rw [map_mul, chargePow_mul, R.mat_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  act :=
    { toFun c := R.act c + (Complex.I * n * F.φ c) • (1 : Matrix ι ι ℂ)
      map_add' a b := by
        rw [map_add, map_add, mul_add, add_smul]
        abel
      map_smul' r c := by
        simp only [map_smul, RingHom.id_apply, smul_add]
        congr 1
        rw [Complex.real_smul, ← algebraMap_smul ℂ r ((Complex.I * n * F.φ c) • (1 : Matrix ι ι ℂ)),
          smul_smul]
        show (Complex.I * n * (r * F.φ c)) • (1 : Matrix ι ι ℂ)
          = ((r : ℂ) * (Complex.I * n * F.φ c)) • 1
        congr 1
        ring }
  jetAct a := R.jetAct a + ((Complex.I * n) • F.φJ a) • (1 : Matrix ι ι SpaceTimeAlgebra)
  jetAct_ofConstantLie c := by
    show R.jetAct _ + ((Complex.I * n) • F.φJ _) • 1
      = (R.act c + (Complex.I * n * F.φ c) • 1).map C
    rw [R.jetAct_ofConstantLie, F.φJ_ofConstantLie, Matrix.map_add _ (map_add C)]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [Algebra.smul_def, MvPowerSeries.algebraMap_apply]
  jetAct_map_cc_foldl p a := by
    show (R.jetAct a + ((Complex.I * n) • F.φJ a) • 1).map _
      = R.act _ + (Complex.I * n * F.φ _) • 1
    rw [Matrix.map_add _ (fun x y => by rw [SpaceTimeAlgebra.iteratedPDeriv_add, map_add]),
      R.jetAct_map_cc_foldl, ← F.φJ_cc_foldl]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_one, SpaceTimeAlgebra.iteratedPDeriv_smul,
        constantCoeff_smul, smul_eq_mul]
    · rw [mul_zero, mul_zero, SpaceTimeAlgebra.iteratedPDeriv_zero_apply, map_zero]
  mat_map_pderiv U μ := by
    show (chargePow n (F.u U) • R.mat U).map _
      = -((R.jetAct _ + ((Complex.I * n) • F.φJ _) • 1) * (chargePow n (F.u U) • R.mat U))
    have hleib : (chargePow n (F.u U) • R.mat U).map (fun f => pderiv μ f)
        = pderiv μ (chargePow n (F.u U)) • R.mat U
          + chargePow n (F.u U) • ((R.mat U).map fun f => pderiv μ f) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [hleib, F.pderiv_chargePow_u, R.mat_map_pderiv, Matrix.add_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_neg, neg_smul, neg_add,
      mul_comm (chargePow n (F.u U))]
    abel
  mat_mul_jetAct U c := by
    show chargePow n (F.u U) • R.mat U * (R.jetAct _ + ((Complex.I * n) • F.φJ _) • 1)
      = (R.jetAct _ + ((Complex.I * n) • F.φJ _) • 1) * (chargePow n (F.u U) • R.mat U)
    rw [F.φJ_adjoint, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, R.mat_mul_jetAct]

end U1Factor

/-!

## C. The fundamental representation of an `SU(n)` factor

-/

namespace SUFactor

variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {n : Type} [Fintype n] [DecidableEq n]
  (F : SUFactor jets n)

/-- **The fundamental representation** of an `SU(n)` factor: the gauge jets act by their
  unitary matrices of jets, the gauge algebra by `i` times its matrix component. -/
noncomputable def fund : MatrixRep jets n where
  mat := F.u
  mat_one := map_one F.u
  mat_mul := map_mul F.u
  act :=
    { toFun c := Complex.I • F.φ c
      map_add' a b := by rw [map_add, smul_add]
      map_smul' r c := by
        simp only [map_smul, RingHom.id_apply]
        rw [smul_comm] }
  jetAct a := Complex.I • F.φJ a
  jetAct_ofConstantLie c := by
    show Complex.I • F.φJ _ = (Complex.I • F.φ c).map C
    rw [F.φJ_ofConstantLie, Matrix.map_smul _ Complex.I (fun z => by
      rw [smul_eq_mul, map_mul, MatrixRep.C_mul_eq_smul])]
  jetAct_map_cc_foldl p a := by
    show (Complex.I • F.φJ a).map _ = Complex.I • F.φ _
    rw [Matrix.map_smul _ Complex.I (fun f => by
      rw [SpaceTimeAlgebra.iteratedPDeriv_smul, constantCoeff_smul]), F.φJ_cc_foldl]
  mat_map_pderiv U μ := by
    show (F.u U).map _ = -(Complex.I • F.φJ _ * F.u U)
    rw [F.φJ_maurerCartan, smul_smul, Complex.I_mul_I, neg_one_smul, Matrix.neg_mul, neg_neg,
      Matrix.mul_assoc, F.u_unitary, Matrix.mul_one]
  mat_mul_jetAct U c := by
    show F.u U * (Complex.I • F.φJ _) = (Complex.I • F.φJ _) * F.u U
    rw [F.φJ_adjoint, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc,
      F.u_unitary, Matrix.mul_one]

end SUFactor

end LocalGaugeData
