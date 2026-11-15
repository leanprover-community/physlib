/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.GaugeJetGroup
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets
/-!
# The local gauge data of a global gauge group

The jets of gauge transformations valued in a global gauge group, as local gauge data.

## i. Overview

A global gauge group `G` with Lie algebra `𝔤` gives local gauge data
`LocalGaugeData G 𝔤 GJ 𝔤J`, with `GJ` the gauge jets and `𝔤J` the Lie algebra jets.
Evaluation is the entrywise constant coefficient, constants embed entrywise, the derivative
and the coordinates act entrywise, the adjoint actions are conjugation `U A U⁻¹`, and the
Maurer–Cartan form is `−(∂_μ U) U⁻¹`.

Every structure map is the matrix one, so the package is a presentation by matrices of jets,
`GlobalGaugeGroup.matrixJets`, and the laws of `LocalGaugeData` and its faithfulness come
from `PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MatrixJets`. The
presentation sends a generator `X` to `−i X`, so that the commutator becomes the bracket
`i (a b − b a)` used throughout the gauge theory, and the Maurer–Cartan form `−(∂_μ U) U⁻¹`
becomes `i (∂_μ U) U⁻¹`. For a compact group inside the unitary group these are the
hermitian generators and the hermitian Maurer–Cartan form of physics.

## ii. Key results

- `GlobalGaugeGroup.matrixJets` : the presentation of the jets by matrices of jets.
- `GlobalGaugeGroup.localGaugeData` : the local gauge data of a global gauge group.

## iii. Table of contents

- A. The presentation by matrices of jets
- B. The local gauge data

## iv. References

* None.

-/

@[expose] public section

open Matrix MvPowerSeries SpaceTimeAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalGaugeGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ] (G : GlobalGaugeGroup κ)

/-!

## A. The presentation by matrices of jets

-/

/-- The presentation of the jets of a global gauge group by matrices of jets. A generator
  `X` of the Lie algebra is sent to `−i X`, so that the commutator becomes the bracket
  `i (a b − b a)`, and the Maurer–Cartan form `−(∂_μ U) U⁻¹` becomes `i (∂_μ U) U⁻¹`. -/
noncomputable def matrixJets :
    LocalGaugeData.MatrixJets κ G.group G.lieSubalgebra G.gaugeJetGroup G.jetLieSubalgebra where
  toMat₀ := (Units.coeHom (Matrix κ κ ℂ)).comp G.group.subtype
  toMat₀_injective := Units.val_injective.comp Subtype.val_injective
  toMatJ := (Units.coeHom (Matrix κ κ SpaceTimeAlgebra)).comp G.gaugeJetGroup.subtype
  toMatJ_injective := Units.val_injective.comp Subtype.val_injective
  lie₀ :=
    { toFun a := (-Complex.I) • (a : Matrix κ κ ℂ)
      map_add' a b := smul_add _ _ _
      map_smul' r a := smul_comm _ r _ }
  lie₀_injective a b h := Subtype.ext (smul_right_injective _ (by simp) h)
  lie₀_bracket a b := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LieSubalgebra.coe_bracket, Ring.lie_def,
      smul_mul_smul_comm, ← smul_sub, smul_smul]
    congr 1
    linear_combination (-Complex.I) * Complex.I_mul_I
  lieJ :=
    { toFun A := (-Complex.I) • (A : Matrix κ κ SpaceTimeAlgebra)
      map_add' A B := smul_add _ _ _
      map_smul' r A := smul_comm _ r _ }
  lieJ_injective A B h := Subtype.ext (smul_right_injective _ (by simp) h)
  lieJ_bracket A B := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LieSubalgebra.coe_bracket, Ring.lie_def,
      smul_mul_smul_comm, ← smul_sub, smul_smul]
    congr 1
    linear_combination (-Complex.I) * Complex.I_mul_I
  eval :=
    { toFun U := ⟨unitsEval U.1, U.2.1⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' U V := Subtype.ext (map_mul _ _ _) }
  toMat₀_eval _ := rfl
  ofConstant :=
    { toFun g := ⟨unitsOfConstant g.1, G.isGaugeJet_unitsOfConstant g.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' g h := Subtype.ext (map_mul _ _ _) }
  toMatJ_ofConstant _ := rfl
  evalLie :=
    { toFun A := ⟨(constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A.1, A.2 0⟩
      map_add' A B := Subtype.ext (map_add _ _ _)
      map_smul' r A := Subtype.ext (Matrix.ext fun i j => constantCoeff_real_smul r _) }
  lie₀_evalLie A := (mapMatrix_constantCoeff_smul _ _).symm
  ofConstantLie :=
    { toFun a := ⟨(C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1,
        G.mapMatrix_C_mem_jetLieAlgebra a.2⟩
      map_add' a b := Subtype.ext (map_add _ _ _)
      map_smul' r a := Subtype.ext (Matrix.ext fun i j => C_real_smul r _) }
  lieJ_ofConstantLie a := (mapMatrix_C_smul _ _).symm
  deriv μ :=
    { toFun A := ⟨A.1.map (pderiv μ), G.map_pderiv_mem_jetLieAlgebra A.2 μ⟩
      map_add' A B := Subtype.ext (Matrix.ext fun i j =>
        map_add (pderiv μ) (A.1 i j) (B.1 i j))
      map_smul' r A := Subtype.ext (Matrix.ext fun i j => pderiv_real_smul μ r _) }
  lieJ_deriv μ A := (map_pderiv_smul μ _ _).symm
  coord μ :=
    { toFun A := ⟨(X μ : SpaceTimeAlgebra) • A.1, G.X_smul_mem_jetLieAlgebra μ A.2⟩
      map_add' A B := Subtype.ext (smul_add _ _ _)
      map_smul' r A := Subtype.ext (smul_comm _ r _) }
  lieJ_coord μ A := smul_comm _ _ _
  adjoint :=
    { toFun U :=
        { toFun A := ⟨U.1.1 * A.1 * (U.1⁻¹).1, G.mul_mul_inv_mem_jetLieAlgebra U.2 A.2⟩
          map_add' A B := Subtype.ext (by simp [mul_add, add_mul])
          map_smul' r A := Subtype.ext (by simp) }
      map_one' := LinearMap.ext fun A => Subtype.ext (by simp)
      map_mul' U V := LinearMap.ext fun A => Subtype.ext (by
        simp [_root_.mul_inv_rev, mul_assoc]) }
  lieJ_adjoint U A := by simp
  adjointValue :=
    { toFun g :=
        { toFun a := ⟨g.1.1 * a.1 * (g.1⁻¹).1,
            conj_mem_lieAlgebraOfIsClosed (hH := G.isClosed) g a.2⟩
          map_add' a b := Subtype.ext (by simp [mul_add, add_mul])
          map_smul' r a := Subtype.ext (by simp) }
      map_one' := LinearMap.ext fun a => Subtype.ext (by simp)
      map_mul' g h := LinearMap.ext fun a => Subtype.ext (by
        simp [_root_.mul_inv_rev, mul_assoc]) }
  lie₀_adjointValue g a := by simp
  maurerCartan U μ := ⟨-(U.1.1.map (pderiv μ) * (U.1⁻¹).1), neg_mem (U.2.2 μ)⟩
  lieJ_maurerCartan U μ := by simp

/-!

## B. The local gauge data

-/

/-- The local gauge data of a global gauge group. The gauge jets are the invertible matrices
  of jets with value in the group and Maurer–Cartan form a Lie algebra jet, the Lie algebra
  jets are the matrices of jets with every base-point derivative in the Lie algebra, and
  every structure map is the matrix one. -/
noncomputable def localGaugeData :
    LocalGaugeData G.group G.lieSubalgebra G.gaugeJetGroup G.jetLieSubalgebra :=
  G.matrixJets.toLocalGaugeData

@[simp]
lemma localGaugeData_eval_val (U : G.gaugeJetGroup) :
    ((G.localGaugeData.eval U).1 : Matrix κ κ ℂ) =
      (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix U.1 := rfl

@[simp]
lemma localGaugeData_ofConstant_val (g : G.group) :
    ((G.localGaugeData.ofConstant g).1 : Matrix κ κ SpaceTimeAlgebra) =
      (C : ℂ →+* SpaceTimeAlgebra).mapMatrix g.1 := rfl

@[simp]
lemma localGaugeData_evalLie_val (A : G.jetLieSubalgebra) :
    (G.localGaugeData.evalLie A).1 = (constantCoeff : SpaceTimeAlgebra →+* ℂ).mapMatrix A.1 :=
  rfl

@[simp]
lemma localGaugeData_ofConstantLie_val (a : G.lieSubalgebra) :
    (G.localGaugeData.ofConstantLie a).1 = (C : ℂ →+* SpaceTimeAlgebra).mapMatrix a.1 := rfl

@[simp]
lemma localGaugeData_deriv_val (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    (G.localGaugeData.deriv μ A).1 = A.1.map (pderiv μ) := rfl

@[simp]
lemma localGaugeData_mulCoord_val (μ : Fin 1 ⊕ Fin 3) (A : G.jetLieSubalgebra) :
    (G.localGaugeData.mulCoord μ A).1 = (X μ : SpaceTimeAlgebra) • A.1 := rfl

@[simp]
lemma localGaugeData_adjointJ_val (U : G.gaugeJetGroup) (A : G.jetLieSubalgebra) :
    (G.localGaugeData.adjointJ U A).1 = U.1.1 * A.1 * (U.1⁻¹).1 := rfl

@[simp]
lemma localGaugeData_adjoint_val (g : G.group) (a : G.lieSubalgebra) :
    (G.localGaugeData.adjoint g a).1 = g.1.1 * a.1 * (g.1⁻¹).1 := rfl

/-- The Maurer–Cartan form of a gauge jet is `−(∂_μ U) U⁻¹`. -/
@[simp]
lemma localGaugeData_maurerCartan_val (U : G.gaugeJetGroup) (μ : Fin 1 ⊕ Fin 3) :
    (G.localGaugeData.maurerCartan U μ).1 = -(U.1.1.map (pderiv μ) * (U.1⁻¹).1) := rfl

/-- The local gauge data of a global gauge group is faithful. -/
instance : G.localGaugeData.Faithful := G.matrixJets.faithful

end GlobalGaugeGroup
