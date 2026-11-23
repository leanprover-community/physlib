/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.GaugeJetGroup
/-!
# The Maurer–Cartan form on the jet gauge group

The Lie algebra jet `(∂_μ U) U⁻¹` of a gauge jet `U`, and its transformation laws.

## i. Overview

Let `G` be a global gauge group. A gauge jet `U`, an element of the jet gauge group, is the
Taylor series at a point of a smooth map from spacetime into `G`. Its Maurer–Cartan form is
`ω_μ = (∂_μ U) U⁻¹`, the pull-back of the right-invariant Maurer–Cartan form of `G`. By the
definition of the jet gauge group it is a Lie algebra jet.

The Maurer–Cartan form vanishes on constant gauge jets. It obeys the cocycle law
`ω(U V) = ω(U) + U ω(V) U⁻¹` and the inversion law `ω(U⁻¹) = −U⁻¹ ω(U) U`. It also governs
how conjugation by `U` interacts with derivatives. For a matrix of jets `A`,
`∂_μ (U⁻¹ A U) = U⁻¹ (∂_μ A − [ω_μ, A]) U`.

A gauge jet with vanishing Maurer–Cartan form has vanishing derivatives, so it is the
constant jet of its value. Conversely every Lie algebra jet `A` vanishing at the base point
is the radial component `∑_μ x_μ ω_μ = −A` of the Maurer–Cartan form of a gauge jet. The jet
is the solution `V` of the radial system `E V = −A V` with `V(0) = 1`, where
`E = ∑_μ x_μ ∂_μ`. Its Maurer–Cartan form solves the linear radial system
`E ω_μ + ω_μ = −∂_μ A − A ω_μ + ω_μ A`, so it is a Lie algebra jet. This is the formal version
of integrating the infinitesimal gauge transformation `A` along rays from the base point.

## ii. Key results

- `GlobalGaugeGroup.maurerCartan` : the Maurer–Cartan form of a gauge jet.
- `GlobalGaugeGroup.map_pderiv_eq_maurerCartan_mul` : the derivative `∂_μ U = ω_μ U` of a gauge
  jet.
- `GlobalGaugeGroup.maurerCartan_mul` : the cocycle law.
- `GlobalGaugeGroup.maurerCartan_inv` : the inversion law.
- `GlobalGaugeGroup.map_pderiv_maurerCartan_sub` : the structure equation
  `∂_μ ω_ν − ∂_ν ω_μ = [ω_μ, ω_ν]`.
- `GlobalGaugeGroup.map_pderiv_inv_mul_mul` : the derivative of a conjugate.
- `GlobalGaugeGroup.eq_gaugeJetOfConstant_of_maurerCartan_eq_zero` : a gauge jet with vanishing
  Maurer–Cartan form is constant.
- `GlobalGaugeGroup.exists_sum_X_smul_maurerCartan_eq` : every Lie algebra jet vanishing at
  the base point is the radial component of the Maurer–Cartan form of a gauge jet.

## iii. Table of contents

- A. The Maurer–Cartan form
- B. Constant gauge jets
- C. The cocycle and inversion laws and the structure equation
- D. The derivative of a conjugate
- E. Gauge jets with vanishing Maurer–Cartan form
- F. Integrating a Lie algebra jet radially

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The Maurer–Cartan form

-/

/-- The Maurer–Cartan form `(∂_μ U) U⁻¹` of a gauge jet `U` in the spacetime direction `μ`,
  a Lie algebra jet. -/
noncomputable def maurerCartan (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    G.jetLieSubalgebra :=
  ⟨(U.1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) * (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra),
    U.2.2 μ⟩

@[simp]
lemma maurerCartan_val (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    (G.maurerCartan U μ : Matrix κ κ SpaceTimeAlgebra) =
      (U.1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) *
        (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra) := rfl

/-- The derivative of a gauge jet in terms of its Maurer–Cartan form, `∂_ρ U = ω_ρ(U) U`. -/
lemma map_pderiv_eq_maurerCartan_mul (U : G.gaugeJetGroup) (ρ : Fin 1 ⊕ Fin 3) :
    (U.1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv ρ) =
      (G.maurerCartan U ρ : Matrix κ κ SpaceTimeAlgebra) * U.1 := by
  rw [maurerCartan_val, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-!

## B. Constant gauge jets

-/

/-- A constant gauge jet has vanishing Maurer–Cartan form. -/
@[simp]
lemma maurerCartan_gaugeJetOfConstant (g : G.group) (μ : Fin 1 ⊕ Fin 3) :
    G.maurerCartan (G.gaugeJetOfConstant g) μ = 0 := by
  ext1
  rw [maurerCartan_val, gaugeJetOfConstant_val, map_pderiv_mapMatrix_C, zero_mul]
  rfl

@[simp]
lemma maurerCartan_one (μ : Fin 1 ⊕ Fin 3) : G.maurerCartan 1 μ = 0 := by
  simpa using G.maurerCartan_gaugeJetOfConstant 1 μ

/-!

## C. The cocycle and inversion laws and the structure equation

-/

/-- The cocycle law `ω(U V) = ω(U) + U ω(V) U⁻¹` of the Maurer–Cartan form `ω` on the
  product of two gauge jets `U` and `V`. -/
lemma maurerCartan_mul (U V : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    (G.maurerCartan (U * V) μ : Matrix κ κ SpaceTimeAlgebra) =
      G.maurerCartan U μ + (U.1 : Matrix κ κ SpaceTimeAlgebra) *
        G.maurerCartan V μ * (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra) := by
  simp only [maurerCartan_val, Subgroup.coe_mul]
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, map_pderiv_mul_mul_mul μ V.1.mul_inv]

/-- The inversion law `ω(U⁻¹) = −U⁻¹ ω(U) U` of the Maurer–Cartan form `ω` on the inverse
  of a gauge jet `U`. -/
lemma maurerCartan_inv (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    (G.maurerCartan U⁻¹ μ : Matrix κ κ SpaceTimeAlgebra) =
      -((↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra) * G.maurerCartan U μ * U.1) := by
  simp only [maurerCartan_val, InvMemClass.coe_inv]
  rw [inv_inv, map_pderiv_of_mul_eq_one μ U.1.mul_inv U.1.inv_mul, neg_mul,
    mul_assoc (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra)]

/-- The Maurer–Cartan structure equation `∂_μ ω_ν − ∂_ν ω_μ = [ω_μ, ω_ν]` for the
  Maurer–Cartan form `ω` of a gauge jet. The curl of `ω` is its commutator. -/
lemma map_pderiv_maurerCartan_sub (U : G.gaugeJetGroup) (μ ν : Fin 1 ⊕ Fin 3) :
    (G.maurerCartan U ν : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) -
        (G.maurerCartan U μ : Matrix κ κ SpaceTimeAlgebra).map (pderiv ν) =
      (G.maurerCartan U μ : Matrix κ κ SpaceTimeAlgebra) * G.maurerCartan U ν -
        (G.maurerCartan U ν : Matrix κ κ SpaceTimeAlgebra) * G.maurerCartan U μ := by
  simp only [maurerCartan_val]
  set A := (U.1 : Matrix κ κ SpaceTimeAlgebra)
  set B := (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra)
  have hAB : A * B = 1 := Units.mul_inv _
  have hBA : B * A = 1 := Units.inv_mul _
  rw [matrix_map_pderiv_mul, matrix_map_pderiv_mul,
    show (A.map (pderiv ν)).map (pderiv μ) = (A.map (pderiv μ)).map (pderiv ν)
      from Matrix.ext fun _ _ => SpaceTimeAlgebra.pderiv_comm μ ν _,
    map_pderiv_of_mul_eq_one μ hAB hBA, map_pderiv_of_mul_eq_one ν hAB hBA]
  simp only [mul_neg, ← mul_assoc]
  abel

/-!

## D. The derivative of a conjugate

-/

/-- The derivative of the conjugate `U⁻¹ A U` of a matrix of jets by a gauge jet, in terms of
  the Maurer–Cartan form `ω_μ` of `U`, `∂_μ (U⁻¹ A U) = U⁻¹ (∂_μ A − [ω_μ, A]) U`. -/
lemma map_pderiv_inv_mul_mul (U : G.gaugeJetGroup) (A : Matrix κ κ SpaceTimeAlgebra)
    (μ : Fin 1 ⊕ Fin 3) :
    ((↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra) * A * U.1).map (pderiv μ) =
      (↑U.1⁻¹ : Matrix κ κ SpaceTimeAlgebra) * (A.map (pderiv μ) -
        ((G.maurerCartan U μ : Matrix κ κ SpaceTimeAlgebra) * A -
          A * G.maurerCartan U μ)) * U.1 :=
  map_pderiv_conj_of_mul_eq_one μ U.1.mul_inv U.1.inv_mul A

/-!

## E. Gauge jets with vanishing Maurer–Cartan form

-/

/-- A gauge jet with vanishing Maurer–Cartan form is the constant gauge jet of its value, since
  its derivatives `∂_μ U = ω_μ U` vanish. -/
lemma eq_gaugeJetOfConstant_of_maurerCartan_eq_zero {U : G.gaugeJetGroup}
    (h : ∀ μ, G.maurerCartan U μ = 0) : U = G.gaugeJetOfConstant (G.evalGaugeJet U) := by
  have hd (μ : Fin 1 ⊕ Fin 3) : (U.1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) = 0 := by
    have h0 := congrArg Subtype.val (h μ)
    rw [maurerCartan_val] at h0
    calc (U.1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ)
        = (U.1 : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) * ((U.1⁻¹).1 * U.1.1) := by
          rw [Units.inv_mul, mul_one]
      _ = 0 := by rw [← mul_assoc, h0, ZeroMemClass.coe_zero, zero_mul]
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  show U.1.1 i j = C (constantCoeff (U.1.1 i j))
  exact SpaceTimeAlgebra.eq_C_of_pderiv_eq_zero fun μ => congrArg (fun M => M i j) (hd μ)

/-!

## F. Integrating a Lie algebra jet radially

-/

/-- Radially integrating a Lie algebra jet gives a gauge jet. An invertible matrix of jets with
  value one at the base point which solves the radial system `E V = −A V`, for a Lie algebra
  jet `A` vanishing at the base point, is a gauge jet. Here `E` is the Euler operator, which
  multiplies the part of each degree by that degree. -/
lemma mem_gaugeJetGroup_of_eulerTransport {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) (hA0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A = 0)
    {V : GeneralLinearGroup κ SpaceTimeAlgebra}
    (hV0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix (V : Matrix κ κ SpaceTimeAlgebra) = 1)
    (hEV : ∑ μ, (X μ : SpaceTimeAlgebra) • (V : Matrix κ κ SpaceTimeAlgebra).map (pderiv μ) =
      -A * V) :
    V ∈ G.gaugeJetGroup := by
  refine G.mem_gaugeJetGroup.2 ⟨?_, fun μ => ?_⟩
  · rw [show unitsEval V = 1 from Units.ext hV0]
    exact one_mem _
  · refine G.mem_jetLieAlgebra_of_euler (B := (-A).map (pderiv μ)) (R := -A)
      (G.map_pderiv_mem_jetLieAlgebra (neg_mem hA) μ) (neg_mem hA) (by rw [map_neg, hA0, neg_zero])
      ?_
    exact euler_map_pderiv_mul_inv_of_eulerTransport μ V.mul_inv V.inv_mul hEV

/-- Every Lie algebra jet vanishing at the base point is, up to sign, the radial component of
  the Maurer–Cartan form of a gauge jet with value one. In symbols, `∑_μ x_μ (∂_μ U) U⁻¹ = −A`
  for the Lie algebra jet `A`. The gauge jet is the solution `U` of the radial system
  `E U = −A U` with `U(0) = 1`, where `E` is the Euler operator. -/
lemma exists_sum_X_smul_maurerCartan_eq {A : Matrix κ κ SpaceTimeAlgebra}
    (hA : A ∈ G.jetLieAlgebra) (hA0 : (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A = 0) :
    ∃ U : G.gaugeJetGroup, G.evalGaugeJet U = 1 ∧
      ∑ μ, (X μ : SpaceTimeAlgebra) • (G.maurerCartan U μ : Matrix κ κ SpaceTimeAlgebra) = -A := by
  have hR0 : ∀ i j, constantCoeff ((-A) i j) = 0 := fun i j => by
    simpa [RingHom.mapMatrix_apply] using congrArg (fun M => -M i j) hA0
  obtain ⟨V, hV0, hEV⟩ := exists_matrix_eulerTransport (-A) hR0
  -- `V` is invertible, its determinant having constant coefficient `det 1 = 1`.
  have hV : IsUnit V := by
    rw [Matrix.isUnit_iff_isUnit_det, MvPowerSeries.isUnit_iff_constantCoeff,
      RingHom.map_det, hV0, det_one]
    exact isUnit_one
  refine ⟨⟨hV.unit, G.mem_gaugeJetGroup_of_eulerTransport hA hA0 hV0 hEV⟩,
    Subtype.ext (Units.ext hV0), ?_⟩
  simp only [maurerCartan_val]
  exact sum_X_smul_map_pderiv_mul_inv_of_eulerTransport hV.unit.mul_inv hEV

end GlobalGaugeGroup
