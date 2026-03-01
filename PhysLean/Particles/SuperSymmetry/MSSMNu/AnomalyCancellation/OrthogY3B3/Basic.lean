/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.LineY3B3
/-!
# The type of solutions perpendicular to `Y₃` and `B₃`

We define the type of solutions which are orthogonal to `Y₃` and `B₃` and prove some basic lemmas
about them.

# References

The main reference for the material in this file is:

- https://arxiv.org/pdf/2107.07926.pdf

-/

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- The type of linear solutions orthogonal to $Y_3$ and $B_3$. -/
structure AnomalyFreePerp extends MSSMACC.LinSols where
  perpY₃ : dot Y₃.val val = 0
  perpB₃ : dot B₃.val val = 0

/-- The projection of an object in `MSSMACC.AnomalyFreeLinear` onto the subspace
  orthogonal to `Y₃` and`B₃`. -/
def proj (T : MSSMACC.LinSols) : MSSMACC.AnomalyFreePerp :=
  ⟨(dot B₃.val T.val - dot Y₃.val T.val) • Y₃.1.1
  + (dot Y₃.val T.val - 2 * dot B₃.val T.val) • B₃.1.1
  + dot Y₃.val B₃.val • T,
  by
    change dot _ (_ • Y₃.val + _ • B₃.val + _ • T.val) = 0
    rw [dot.map_add₂, dot.map_add₂]
    rw [dot.map_smul₂, dot.map_smul₂, dot.map_smul₂]
    rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl]
    rw [show dot Y₃.val Y₃.val = 216 by with_unfolding_all rfl]
    ring,
  by
    change dot _ (_ • Y₃.val + _ • B₃.val + _ • T.val) = 0
    rw [dot.map_add₂, dot.map_add₂]
    rw [dot.map_smul₂, dot.map_smul₂, dot.map_smul₂]
    rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl]
    rw [show dot B₃.val Y₃.val = 108 by with_unfolding_all rfl]
    rw [show dot B₃.val B₃.val = 108 by with_unfolding_all rfl]
    ring⟩

lemma proj_val (T : MSSMACC.LinSols) :
    (proj T).val = (dot B₃.val T.val - dot Y₃.val T.val) • Y₃.val +
    (dot Y₃.val T.val - 2 * dot B₃.val T.val) • B₃.val +
    dot Y₃.val B₃.val • T.val := by
  rfl

lemma Y₃_plus_B₃_plus_proj (T : MSSMACC.LinSols) (a b c : ℚ) :
    a • Y₃.val + b • B₃.val + c • (proj T).val =
    (a + c * (dot B₃.val T.val - dot Y₃.val T.val)) • Y₃.val
    + (b + c * (dot Y₃.val T.val - 2 * dot B₃.val T.val)) • B₃.val
    + (dot Y₃.val B₃.val * c) • T.val:= by
  rw [proj_val]
  rw [DistribMulAction.smul_add, DistribMulAction.smul_add]
  module

lemma quad_Y₃_proj (T : MSSMACC.LinSols) :
    quadBiLin Y₃.val (proj T).val = dot Y₃.val B₃.val * quadBiLin Y₃.val T.val := by
  rw [proj_val]
  rw [quadBiLin.map_add₂, quadBiLin.map_add₂]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  rw [show quadBiLin Y₃.val B₃.val = 0 by with_unfolding_all rfl]
  rw [show quadBiLin Y₃.val Y₃.val = 0 by with_unfolding_all rfl]
  ring

lemma quad_B₃_proj (T : MSSMACC.LinSols) :
    quadBiLin B₃.val (proj T).val = dot Y₃.val B₃.val * quadBiLin B₃.val T.val := by
  rw [proj_val]
  rw [quadBiLin.map_add₂, quadBiLin.map_add₂]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  rw [show quadBiLin B₃.val Y₃.val = 0 by with_unfolding_all rfl]
  rw [show quadBiLin B₃.val B₃.val = 0 by with_unfolding_all rfl]
  ring

lemma quad_self_proj (T : MSSMACC.Sols) :
    quadBiLin T.val (proj T.1.1).val =
    (dot B₃.val T.val - dot Y₃.val T.val) * quadBiLin Y₃.val T.val +
    (dot Y₃.val T.val - 2 * dot B₃.val T.val) * quadBiLin B₃.val T.val := by
  rw [proj_val]
  rw [quadBiLin.map_add₂, quadBiLin.map_add₂]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  erw [quadSol T.1]
  rw [quadBiLin.swap T.val Y₃.val, quadBiLin.swap T.val B₃.val]
  ring

lemma quad_proj (T : MSSMACC.Sols) :
    quadBiLin (proj T.1.1).val (proj T.1.1).val = 2 * dot Y₃.val B₃.val *
    ((dot B₃.val T.val - dot Y₃.val T.val) * quadBiLin Y₃.val T.val +
    (dot Y₃.val T.val - 2 * dot B₃.val T.val) * quadBiLin B₃.val T.val) := by
  nth_rewrite 1 [proj_val]
  repeat rw [quadBiLin.map_add₁]
  repeat rw [quadBiLin.map_smul₁]
  rw [quad_Y₃_proj, quad_B₃_proj, quad_self_proj]
  ring

lemma cube_proj_proj_Y₃ (T : MSSMACC.LinSols) :
    cubeTriLin (proj T).val (proj T).val Y₃.val =
    (dot Y₃.val B₃.val)^2 * cubeTriLin T.val T.val Y₃.val := by
  rw [proj_val]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_add₂]
  conv_lhs =>
    enter [1, 1]
    change ((cubeTriLin (lineY₃B₃ _ _).val) (lineY₃B₃ _ _).val) _
    rw [lineY₃B₃_doublePoint]
  rw [cubeTriLin.map_add₂]
  rw [cubeTriLin.swap₂]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_smul₁, cubeTriLin.map_smul₃]
  rw [doublePoint_Y₃_Y₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₃, cubeTriLin.swap₁]
  rw [doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_add₂]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.swap₁, cubeTriLin.swap₂]
  rw [doublePoint_Y₃_Y₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.swap₁, cubeTriLin.swap₂, cubeTriLin.swap₁]
  rw [doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  ring

lemma cube_proj_proj_B₃ (T : MSSMACC.LinSols) :
    cubeTriLin (proj T).val (proj T).val B₃.val =
    (dot Y₃.val B₃.val)^2 * cubeTriLin T.val T.val B₃.val := by
  rw [proj_val]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_add₂]
  erw [lineY₃B₃_doublePoint]
  rw [cubeTriLin.map_add₂, cubeTriLin.swap₂, cubeTriLin.map_add₁, cubeTriLin.map_smul₁,
    cubeTriLin.map_smul₃, doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₃, cubeTriLin.swap₁, doublePoint_B₃_B₃]
  rw [cubeTriLin.map_add₂, cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.swap₁, cubeTriLin.swap₂, doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.swap₁, cubeTriLin.swap₂,
    cubeTriLin.swap₁, doublePoint_B₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  ring

lemma cube_proj_proj_self (T : MSSMACC.Sols) :
    cubeTriLin (proj T.1.1).val (proj T.1.1).val T.val =
    2 * dot Y₃.val B₃.val *
    ((dot B₃.val T.val - dot Y₃.val T.val) * cubeTriLin T.val T.val Y₃.val +
    (dot Y₃.val T.val - 2 * dot B₃.val T.val) * cubeTriLin T.val T.val B₃.val) := by
  rw [proj_val]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_add₂]
  erw [lineY₃B₃_doublePoint]
  repeat rw [cubeTriLin.map_add₁]
  repeat rw [cubeTriLin.map_smul₁]
  repeat rw [cubeTriLin.map_add₂]
  repeat rw [cubeTriLin.map_smul₂]
  erw [T.cubicSol]
  rw [cubeTriLin.swap₁ Y₃.val T.val T.val, cubeTriLin.swap₂ T.val Y₃.val T.val]
  rw [cubeTriLin.swap₁ B₃.val T.val T.val, cubeTriLin.swap₂ T.val B₃.val T.val]
  ring

lemma cube_proj (T : MSSMACC.Sols) :
    cubeTriLin (proj T.1.1).val (proj T.1.1).val (proj T.1.1).val =
    3 * dot Y₃.val B₃.val ^ 2 *
    ((dot B₃.val T.val - dot Y₃.val T.val) * cubeTriLin T.val T.val Y₃.val +
        (dot Y₃.val T.val - 2 * dot B₃.val T.val) * cubeTriLin T.val T.val B₃.val) := by
  nth_rewrite 3 [proj_val]
  repeat rw [cubeTriLin.map_add₃]
  repeat rw [cubeTriLin.map_smul₃]
  rw [cube_proj_proj_Y₃, cube_proj_proj_B₃, cube_proj_proj_self]
  ring

end MSSMACC
