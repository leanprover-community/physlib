/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.Basic
/-!
# Plane Y₃ B₃ and an orthogonal third point

The plane spanned by Y₃, B₃ and third orthogonal point.

# References

- https://arxiv.org/pdf/2107.07926.pdf

-/

@[expose] public section

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- The plane of linear solutions spanned by `Y₃`, `B₃` and `R`, a point orthogonal
to `Y₃` and `B₃`. -/
def planeY₃B₃ (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) : MSSMACC.LinSols :=
  a • Y₃.1.1 + b • B₃.1.1 + c • R.1

lemma planeY₃B₃_val (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) :
    (planeY₃B₃ R a b c).val = a • Y₃.val + b • B₃.val + c • R.val := by
  rfl

lemma planeY₃B₃_smul (R : MSSMACC.AnomalyFreePerp) (a b c d : ℚ) :
    planeY₃B₃ R (d * a) (d * b) (d * c) = d • planeY₃B₃ R a b c := by
  apply ACCSystemLinear.LinSols.ext
  change _ = d • (planeY₃B₃ R a b c).val
  rw [planeY₃B₃_val, planeY₃B₃_val]
  rw [smul_add, smul_add]
  rw [smul_smul, smul_smul, smul_smul]

lemma planeY₃B₃_eq (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) (h : a = a' ∧ b = b' ∧ c = c') :
    (planeY₃B₃ R a b c) = (planeY₃B₃ R a' b' c') := by
  rw [h.1, h.2.1, h.2.2]

lemma planeY₃B₃_val_eq' (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) (hR' : R.val ≠ 0)
    (h : (planeY₃B₃ R a b c).val = (planeY₃B₃ R a' b' c').val) :
    a = a' ∧ b = b' ∧ c = c' := by
  rw [planeY₃B₃_val, planeY₃B₃_val] at h
  have h1 := congrArg (fun S => dot Y₃.val S) h
  have h2 := congrArg (fun S => dot B₃.val S) h
  simp only at h1 h2
  erw [dot.map_add₂, dot.map_add₂] at h1 h2
  erw [dot.map_add₂ Y₃.val (a' • Y₃.val + b' • B₃.val) (c' • R.val)] at h1
  erw [dot.map_add₂ B₃.val (a' • Y₃.val + b' • B₃.val) (c' • R.val)] at h2
  rw [dot.map_add₂] at h1 h2
  rw [dot.map_smul₂, dot.map_smul₂, dot.map_smul₂] at h1 h2
  rw [dot.map_smul₂, dot.map_smul₂, dot.map_smul₂] at h1 h2
  rw [R.perpY₃] at h1
  rw [R.perpB₃] at h2
  rw [show dot Y₃.val Y₃.val = 216 by with_unfolding_all rfl] at h1
  rw [show dot B₃.val B₃.val = 108 by with_unfolding_all rfl] at h2
  rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h1
  rw [show dot B₃.val Y₃.val = 108 by with_unfolding_all rfl] at h2
  simp_all
  have ha : a = a' := by
    linear_combination h1 / 108 + -1 * h2 / 108
  have hb : b = b' := by
    linear_combination -1 * h1 / 108 + h2 / 54
  rw [ha, hb] at h
  have h1 := add_left_cancel h
  have h1i : c • R.val + (- c') • R.val = 0 := by
    rw [h1]
    rw [← Module.add_smul]
    simp
  rw [← Module.add_smul] at h1i
  have hR : ∃ i, R.val i ≠ 0 := Function.ne_iff.mp hR'
  obtain ⟨i, hi⟩ := hR
  have h2 := congrArg (fun S => S i) h1i
  change _ = 0 at h2
  simp only [HSMul.hSMul, ACCSystemCharges.chargesModule_smul, mul_eq_zero] at h2
  have hc : c + -c' = 0 := by
    cases h2 <;> rename_i h2
    exact h2
    exact (hi h2).elim
  have hc : c = c' := by
    linear_combination hc
  rw [ha, hb, hc]
  simp

lemma planeY₃B₃_quad (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) :
    accQuad (planeY₃B₃ R a b c).val = c * (2 * a * quadBiLin Y₃.val R.val
    + 2 * b * quadBiLin B₃.val R.val + c * quadBiLin R.val R.val) := by
  rw [planeY₃B₃_val]
  rw [accQuad, BiLinearSymm.toHomogeneousQuad_add]
  erw [lineY₃B₃Charges_quad]
  rw [quadBiLin.toHomogeneousQuad.map_smul]
  rw [quadBiLin.map_add₁, quadBiLin.map_smul₁, quadBiLin.map_smul₁]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  rw [show (BiLinearSymm.toHomogeneousQuad quadBiLin) R.val = quadBiLin R.val R.val by rfl]
  ring

lemma planeY₃B₃_cubic (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) :
    accCube (planeY₃B₃ R a b c).val = c ^ 2 *
    (3 * a * cubeTriLin R.val R.val Y₃.val
    + 3 * b * cubeTriLin R.val R.val B₃.val + c * cubeTriLin R.val R.val R.val) := by
  rw [planeY₃B₃_val]
  rw [accCube, TriLinearSymm.toCubic_add]
  erw [lineY₃B₃Charges_cubic]
  erw [lineY₃B₃_doublePoint (c • R.1) a b]
  rw [cubeTriLin.toCubic.map_smul]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.map_add₃, cubeTriLin.map_smul₃, cubeTriLin.map_smul₃]
  rw [show (TriLinearSymm.toCubic cubeTriLin) R.val = cubeTriLin R.val R.val R.val by rfl]
  ring

/-- The line in the plane spanned by `Y₃`, `B₃` and `R` which is in the quadratic,
as `LinSols`. -/
def lineQuadAFL (R : MSSMACC.AnomalyFreePerp) (c1 c2 c3 : ℚ) : MSSMACC.LinSols :=
  planeY₃B₃ R (c2 * quadBiLin R.val R.val - 2 * c3 * quadBiLin B₃.val R.val)
  (2 * c3 * quadBiLin Y₃.val R.val - c1 * quadBiLin R.val R.val)
  (2 * c1 * quadBiLin B₃.val R.val - 2 * c2 * quadBiLin Y₃.val R.val)

lemma lineQuadAFL_quad (R : MSSMACC.AnomalyFreePerp) (c1 c2 c3 : ℚ) :
    accQuad (lineQuadAFL R c1 c2 c3).val = 0 := by
  rw [lineQuadAFL, planeY₃B₃_quad]
  rw [mul_eq_zero]
  apply Or.inr
  ring

/-- The line in the plane spanned by `Y₃`, `B₃` and `R` which is in the quadratic. -/
def lineQuad (R : MSSMACC.AnomalyFreePerp) (c1 c2 c3 : ℚ) : MSSMACC.QuadSols :=
  AnomalyFreeQuadMk' (lineQuadAFL R c1 c2 c3) (lineQuadAFL_quad R c1 c2 c3)

lemma lineQuad_val (R : MSSMACC.AnomalyFreePerp) (c1 c2 c3 : ℚ) :
    (lineQuad R c1 c2 c3).val = (planeY₃B₃ R
    (c2 * quadBiLin R.val R.val - 2 * c3 * quadBiLin B₃.val R.val)
    (2 * c3 * quadBiLin Y₃.val R.val - c1 * quadBiLin R.val R.val)
    (2 * c1 * quadBiLin B₃.val R.val - 2 * c2 * quadBiLin Y₃.val R.val)).val := by
  rfl

lemma lineQuad_smul (R : MSSMACC.AnomalyFreePerp) (a b c d : ℚ) :
    lineQuad R (d * a) (d * b) (d * c) = d • lineQuad R a b c := by
  apply ACCSystemQuad.QuadSols.ext
  change _ = (d • planeY₃B₃ R _ _ _).val
  rw [← planeY₃B₃_smul]
  rw [lineQuad_val]
  ring_nf

/-- A helper function to simplify following expressions. -/
def α₁ (T : MSSMACC.AnomalyFreePerp) : ℚ :=
  (3 * cubeTriLin T.val T.val B₃.val * quadBiLin T.val T.val -
    2 * cubeTriLin T.val T.val T.val * quadBiLin B₃.val T.val)

/-- A helper function to simplify following expressions. -/
def α₂ (T : MSSMACC.AnomalyFreePerp) : ℚ :=
  (2 * cubeTriLin T.val T.val T.val * quadBiLin Y₃.val T.val -
  3 * cubeTriLin T.val T.val Y₃.val * quadBiLin T.val T.val)

/-- A helper function to simplify following expressions. -/
def α₃ (T : MSSMACC.AnomalyFreePerp) : ℚ :=
  6 * ((cubeTriLin T.val T.val Y₃.val) * quadBiLin B₃.val T.val -
      (cubeTriLin T.val T.val B₃.val) * quadBiLin Y₃.val T.val)

lemma lineQuad_cube (R : MSSMACC.AnomalyFreePerp) (c₁ c₂ c₃ : ℚ) :
    accCube (lineQuad R c₁ c₂ c₃).val =
    - 4 * (c₁ * quadBiLin B₃.val R.val - c₂ * quadBiLin Y₃.val R.val) ^ 2 *
    (α₁ R * c₁ + α₂ R * c₂ + α₃ R * c₃) := by
  rw [lineQuad_val]
  rw [planeY₃B₃_cubic, α₁, α₂, α₃]
  ring

/-- The line in the plane spanned by `Y₃`, `B₃` and `R` which is in the cubic. -/
def lineCube (R : MSSMACC.AnomalyFreePerp) (a₁ a₂ a₃ : ℚ) :
    MSSMACC.LinSols :=
  planeY₃B₃ R
    (a₂ * cubeTriLin R.val R.val R.val - 3 * a₃ * cubeTriLin R.val R.val B₃.val)
    (3 * a₃ * cubeTriLin R.val R.val Y₃.val - a₁ * cubeTriLin R.val R.val R.val)
    (3 * (a₁ * cubeTriLin R.val R.val B₃.val - a₂ * cubeTriLin R.val R.val Y₃.val))

lemma lineCube_smul (R : MSSMACC.AnomalyFreePerp) (a b c d : ℚ) :
    lineCube R (d * a) (d * b) (d * c) = d • lineCube R a b c := by
  apply ACCSystemLinear.LinSols.ext
  change _ = (d • planeY₃B₃ R _ _ _).val
  rw [← planeY₃B₃_smul]
  change (planeY₃B₃ R _ _ _).val = (planeY₃B₃ R _ _ _).val
  ring_nf

lemma lineCube_cube (R : MSSMACC.AnomalyFreePerp) (a₁ a₂ a₃ : ℚ) :
    accCube (lineCube R a₁ a₂ a₃).val = 0 := by
  rw [lineCube, planeY₃B₃_cubic]
  ring_nf

lemma lineCube_quad (R : MSSMACC.AnomalyFreePerp) (a₁ a₂ a₃ : ℚ) :
    accQuad (lineCube R a₁ a₂ a₃).val =
    3 * (a₁ * cubeTriLin R.val R.val B₃.val - a₂ * cubeTriLin R.val R.val Y₃.val) *
    (α₁ R * a₁ + α₂ R * a₂ + α₃ R * a₃) := by
  rw [lineCube, planeY₃B₃_quad, α₁, α₂, α₃]
  ring

section proj

lemma α₃_proj (T : MSSMACC.Sols) : α₃ (proj T.1.1) =
    6 * dot Y₃.val B₃.val ^ 3 *
    (cubeTriLin T.val T.val Y₃.val * quadBiLin B₃.val T.val -
    cubeTriLin T.val T.val B₃.val * quadBiLin Y₃.val T.val) := by
  rw [α₃, cube_proj_proj_Y₃, cube_proj_proj_B₃, quad_B₃_proj, quad_Y₃_proj]
  ring

lemma α₂_proj (T : MSSMACC.Sols) : α₂ (proj T.1.1) =
    - α₃ (proj T.1.1) * (dot Y₃.val T.val - 2 * dot B₃.val T.val) := by
  rw [α₃_proj, α₂, cube_proj_proj_Y₃, quad_Y₃_proj, quad_proj, cube_proj]
  ring

lemma α₁_proj (T : MSSMACC.Sols) : α₁ (proj T.1.1) =
    - α₃ (proj T.1.1) * (dot B₃.val T.val - dot Y₃.val T.val) := by
  rw [α₃_proj, α₁]
  rw [cube_proj_proj_B₃, quad_B₃_proj, quad_proj, cube_proj]
  ring

lemma α₁_proj_zero (T : MSSMACC.Sols) (h1 : α₃ (proj T.1.1) = 0) :
    α₁ (proj T.1.1) = 0 := by
  rw [α₁_proj, h1]
  exact mul_eq_zero_of_left rfl ((dot B₃.val) T.val - (dot Y₃.val) T.val)

lemma α₂_proj_zero (T : MSSMACC.Sols) (h1 : α₃ (proj T.1.1) = 0) :
    α₂ (proj T.1.1) = 0 := by
  rw [α₂_proj, h1]
  exact mul_eq_zero_of_left rfl ((dot Y₃.val) T.val - 2 * (dot B₃.val) T.val)

end proj

end MSSMACC
