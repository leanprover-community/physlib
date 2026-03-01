/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.PlaneWithY3B3
/-!
# From charges perpendicular to `Y₃` and `B₃` to solutions

The main aim of this file is to take charge assignments perpendicular to `Y₃` and `B₃` and
produce solutions to the anomaly cancellation conditions. In this regard we will define
a surjective map `toSol` from `MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ` to `MSSMACC.Sols`.

To define `toSols` we define a series of other maps from various subtypes of
`MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ` to `MSSMACC.Sols`. And show that these maps form a
surjection on certain subtypes of `MSSMACC.Sols`.

# References

The main reference for the material in this file is:

- https://arxiv.org/pdf/2107.07926.pdf

-/

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

namespace AnomalyFreePerp

/-- A condition for the quad line in the plane spanned by R, Y₃ and B₃ to sit in the cubic,
and for the cube line to sit in the quad. -/
def LineEqProp (R : MSSMACC.AnomalyFreePerp) : Prop := α₁ R = 0 ∧ α₂ R = 0 ∧ α₃ R = 0

/-- The proposition `LineEqProp` is decidable. -/
instance (R : MSSMACC.AnomalyFreePerp) : Decidable (LineEqProp R) := instDecidableAnd

/-- A condition on `Sols` which we will show in `linEqPropSol_iff_proj_linEqProp` that is equivalent
  to the condition that the `proj` of the solution satisfies `lineEqProp`. -/
def LineEqPropSol (R : MSSMACC.Sols) : Prop :=
  cubeTriLin R.val R.val Y₃.val * quadBiLin B₃.val R.val -
  cubeTriLin R.val R.val B₃.val * quadBiLin Y₃.val R.val = 0

/-- A rational which appears in `toSolNS` acting on sols, and which being zero is
equivalent to satisfying `lineEqPropSol`. -/
def lineEqCoeff (T : MSSMACC.Sols) : ℚ := dot Y₃.val B₃.val * α₃ (proj T.1.1)

lemma lineEqPropSol_iff_lineEqCoeff_zero (T : MSSMACC.Sols) :
    LineEqPropSol T ↔ lineEqCoeff T = 0 := by
  rw [LineEqPropSol, lineEqCoeff, α₃]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero,false_or]
  rw [cube_proj_proj_B₃, cube_proj_proj_Y₃, quad_B₃_proj, quad_Y₃_proj]
  rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl]
  simp only [OfNat.ofNat_ne_zero, false_or]
  ring_nf
  rw [mul_comm _ 1259712, mul_comm _ 1259712, ← mul_sub]
  simp

lemma linEqPropSol_iff_proj_linEqProp (R : MSSMACC.Sols) :
    LineEqPropSol R ↔ LineEqProp (proj R.1.1) := by
  rw [lineEqPropSol_iff_lineEqCoeff_zero, lineEqCoeff, LineEqProp]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h
    rw [α₁_proj, α₂_proj, h]
    simp only [neg_zero, zero_mul, and_self]
  · rw [h.2.2]
    exact Rat.mul_zero ((dot Y₃.val) B₃.val)

/-- A condition which is satisfied if the plane spanned by `R`, `Y₃` and `B₃` lies
entirely in the quadratic surface. -/
def InQuadProp (R : MSSMACC.AnomalyFreePerp) : Prop :=
    quadBiLin R.val R.val = 0 ∧ quadBiLin Y₃.val R.val = 0 ∧ quadBiLin B₃.val R.val = 0

/-- The proposition `InQuadProp` is decidable. -/
instance (R : MSSMACC.AnomalyFreePerp) : Decidable (InQuadProp R) := instDecidableAnd

/-- A condition which is satisfied if the plane spanned by the solutions `R`, `Y₃` and `B₃`
lies entirely in the quadratic surface. -/
def InQuadSolProp (R : MSSMACC.Sols) : Prop :=
    quadBiLin Y₃.val R.val = 0 ∧ quadBiLin B₃.val R.val = 0

/-- A rational which has two properties. It is zero for a solution `T` if and only if
that solution satisfies `inQuadSolProp`. It appears in the definition of `inQuadProj`. -/
def quadCoeff (T : MSSMACC.Sols) : ℚ :=
    2 * dot Y₃.val B₃.val ^ 2 *
    (quadBiLin Y₃.val T.val ^ 2 + quadBiLin B₃.val T.val ^ 2)

lemma inQuadSolProp_iff_quadCoeff_zero (T : MSSMACC.Sols) : InQuadSolProp T ↔ quadCoeff T = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [quadCoeff, h.1, h.2]
    with_unfolding_all rfl
  · rw [quadCoeff, show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
      not_false_eq_true, pow_eq_zero_iff, or_self, false_or] at h
    apply (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp at h
    simp only [ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at h
    exact h

/-- The conditions `inQuadSolProp R` and `inQuadProp (proj R.1.1)` are equivalent. This is to be
expected since both `R` and `proj R.1.1` define the same plane with `Y₃` and `B₃`. -/
lemma inQuadSolProp_iff_proj_inQuadProp (R : MSSMACC.Sols) :
    InQuadSolProp R ↔ InQuadProp (proj R.1.1) := by
  rw [InQuadSolProp, InQuadProp, quad_proj, quad_Y₃_proj, quad_B₃_proj]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [h.1, h.2]
    simp only [mul_zero, add_zero, and_self]
  · rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, or_self, false_or] at h
    rw [h.2.1, h.2.2]
    exact Prod.mk_eq_zero.mp rfl

/-- A condition which is satisfied if the plane spanned by `R`, `Y₃` and `B₃` lies
entirely in the cubic surface. -/
def InCubeProp (R : MSSMACC.AnomalyFreePerp) : Prop :=
    cubeTriLin R.val R.val R.val = 0 ∧ cubeTriLin R.val R.val B₃.val = 0 ∧
    cubeTriLin R.val R.val Y₃.val = 0

/-- The proposition `InCubeProp` is decidable. -/
instance (R : MSSMACC.AnomalyFreePerp) : Decidable (InCubeProp R) := instDecidableAnd

/-- A condition which is satisfied if the plane spanned by the solutions `R`, `Y₃` and `B₃`
lies entirely in the cubic surface. -/
def InCubeSolProp (R : MSSMACC.Sols) : Prop :=
    cubeTriLin R.val R.val B₃.val = 0 ∧ cubeTriLin R.val R.val Y₃.val = 0

/-- A rational which has two properties. It is zero for a solution `T` if and only if
that solution satisfies `inCubeSolProp`. It appears in the definition of `inLineEqProj`. -/
def cubicCoeff (T : MSSMACC.Sols) : ℚ :=
    3 * (dot Y₃.val B₃.val) ^ 3 * (cubeTriLin T.val T.val Y₃.val ^ 2 +
    cubeTriLin T.val T.val B₃.val ^ 2)

lemma inCubeSolProp_iff_cubicCoeff_zero (T : MSSMACC.Sols) :
    InCubeSolProp T ↔ cubicCoeff T = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [cubicCoeff, h.1, h.2]
    with_unfolding_all rfl
  · rw [cubicCoeff, show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
      not_false_eq_true, pow_eq_zero_iff, or_self, false_or] at h
    apply (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp at h
    simp only [ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at h
    exact h.symm

lemma inCubeSolProp_iff_proj_inCubeProp (R : MSSMACC.Sols) :
    InCubeSolProp R ↔ InCubeProp (proj R.1.1) := by
  rw [InCubeSolProp, InCubeProp]
  rw [cube_proj, cube_proj_proj_Y₃, cube_proj_proj_B₃]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [h.1, h.2]
    simp only [mul_zero, add_zero, and_self]
  · rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
      not_false_eq_true, pow_eq_zero_iff, or_self, false_or] at h
    rw [h.2.1, h.2.2]
    exact Prod.mk_eq_zero.mp rfl

/-- Those charge assignments perpendicular to `Y₃` and `B₃` which satisfy the condition
`lineEqProp`. -/
def InLineEq : Type := {R : MSSMACC.AnomalyFreePerp // LineEqProp R}

/-- Those charge assignments perpendicular to `Y₃` and `B₃` which satisfy the conditions
`lineEqProp` and `inQuadProp`. -/
def InQuad : Type := {R : InLineEq // InQuadProp R.val}

/-- Those charge assignments perpendicular to `Y₃` and `B₃` which satisfy the conditions
`lineEqProp`, `inQuadProp` and `inCubeProp`. -/
def InQuadCube : Type := {R : InQuad // InCubeProp R.val.val}

/-- Those solutions which do not satisfy the condition `lineEqPropSol`. -/
def NotInLineEqSol : Type := {R : MSSMACC.Sols // ¬ LineEqPropSol R}

/-- Those solutions which satisfy the condition `lineEqPropSol` but not `inQuadSolProp`. -/
def InLineEqSol : Type := {R : MSSMACC.Sols // LineEqPropSol R ∧ ¬ InQuadSolProp R}

/-- Those solutions which satisfy the condition `lineEqPropSol` and `inQuadSolProp` but
not `inCubeSolProp`. -/
def InQuadSol : Type := {R : MSSMACC.Sols // LineEqPropSol R ∧ InQuadSolProp R ∧ ¬ InCubeSolProp R}

/-- Those solutions which satisfy the conditions `lineEqPropSol`, `inQuadSolProp`
and `inCubeSolProp`. -/
def InQuadCubeSol : Type :=
  {R : MSSMACC.Sols // LineEqPropSol R ∧ InQuadSolProp R ∧ InCubeSolProp R}

/-- Given an `R` perpendicular to `Y₃` and `B₃` a quadratic solution. -/
def toSolNSQuad (R : MSSMACC.AnomalyFreePerp) : MSSMACC.QuadSols :=
  lineQuad R
    (3 * cubeTriLin R.val R.val Y₃.val)
    (3 * cubeTriLin R.val R.val B₃.val)
    (cubeTriLin R.val R.val R.val)

lemma toSolNSQuad_cube (R : MSSMACC.AnomalyFreePerp) :
    accCube (toSolNSQuad R).val = 0 := by
  rw [toSolNSQuad]
  rw [lineQuad_val]
  rw [planeY₃B₃_cubic]
  ring

lemma toSolNSQuad_eq_planeY₃B₃_on_α (R : MSSMACC.AnomalyFreePerp) :
    (toSolNSQuad R).1 = planeY₃B₃ R (α₁ R) (α₂ R) (α₃ R) := by
  change (planeY₃B₃ _ _ _ _) = _
  apply planeY₃B₃_eq
  rw [α₁, α₂, α₃]
  ring_nf
  exact ⟨trivial, trivial, trivial⟩

/-- Given an `R` perpendicular to `Y₃` and `B₃`, an element of `Sols`. This map is
not surjective. -/
def toSolNS : MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, a, _, _) =>
  a • AnomalyFreeMk'' (toSolNSQuad R) (toSolNSQuad_cube R)

/-- A map from `Sols` to `MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ` which on elements of
`notInLineEqSol` will produce a right inverse to `toSolNS`. -/
def toSolNSProj (T : MSSMACC.Sols) : MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ :=
  (proj T.1.1, (lineEqCoeff T)⁻¹, 0, 0)

lemma toSolNS_proj (T : NotInLineEqSol) : toSolNS (toSolNSProj T.val) = T.val := by
  apply ACCSystem.Sols.ext
  rw [toSolNS, toSolNSProj]
  change (lineEqCoeff T.val)⁻¹ • (toSolNSQuad _).1.1 = _
  rw [toSolNSQuad_eq_planeY₃B₃_on_α]
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [α₁_proj, α₂_proj]
  ring_nf
  simp only [zero_smul, add_zero, zero_add]
  have h1 : α₃ (proj T.val.toLinSols) * dot Y₃.val B₃.val = lineEqCoeff T.val := by
    rw [lineEqCoeff]
    ring
  rw [h1]
  have h1 := (lineEqPropSol_iff_lineEqCoeff_zero T.val).mpr.mt T.prop
  rw [← SemigroupAction.mul_smul, mul_comm, mul_inv_cancel₀ h1]
  exact MulAction.one_smul T.1.val

/-- A solution to the ACCs, given an element of `inLineEq × ℚ × ℚ × ℚ`. -/
def inLineEqToSol : InLineEq × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, c₁, c₂, c₃) =>
  AnomalyFreeMk'' (lineQuad R.val c₁ c₂ c₃)
    (by
      rw [lineQuad_cube]
      rw [R.prop.1, R.prop.2.1, R.prop.2.2]
      simp)

/-- On elements of `inLineEqSol` a right-inverse to `inLineEqSol`. -/
def inLineEqProj (T : InLineEqSol) : InLineEq × ℚ × ℚ × ℚ :=
  (⟨proj T.val.1.1, (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop.1⟩,
  (quadCoeff T.val)⁻¹ * quadBiLin B₃.val T.val.val,
  (quadCoeff T.val)⁻¹ * (- quadBiLin Y₃.val T.val.val),
  (quadCoeff T.val)⁻¹ *
  (quadBiLin B₃.val T.val.val * (dot B₃.val T.val.val - dot Y₃.val T.val.val)
  - quadBiLin Y₃.val T.val.val * (dot Y₃.val T.val.val - 2 * dot B₃.val T.val.val)))

lemma inLineEqTo_smul (R : InLineEq) (c₁ c₂ c₃ d : ℚ) :
    inLineEqToSol (R, (d * c₁), (d * c₂), (d * c₃)) = d • inLineEqToSol (R, c₁, c₂, c₃) := by
  apply ACCSystem.Sols.ext
  change (lineQuad _ _ _ _).val = _
  rw [lineQuad_smul]
  rfl

lemma inLineEqToSol_proj (T : InLineEqSol) : inLineEqToSol (inLineEqProj T) = T.val := by
  rw [inLineEqProj, inLineEqTo_smul]
  apply ACCSystem.Sols.ext
  change _ • (lineQuad _ _ _ _).val = _
  rw [lineQuad_val]
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [quad_proj, quad_Y₃_proj, quad_B₃_proj]
  ring_nf
  simp only [zero_smul, add_zero, zero_add]
  have h1 : (quadBiLin Y₃.val T.val.val ^ 2 * dot Y₃.val B₃.val ^ 2 * 2 +
      dot Y₃.val B₃.val ^ 2 * quadBiLin B₃.val T.val.val ^ 2 * 2) = quadCoeff T.val := by
    rw [quadCoeff]
    ring
  rw [h1]
  have h2 := (inQuadSolProp_iff_quadCoeff_zero T.val).mpr.mt T.prop.2
  rw [← SemigroupAction.mul_smul, mul_comm, mul_inv_cancel₀ h2]
  exact MulAction.one_smul T.1.val

/-- Given an element of `inQuad × ℚ × ℚ × ℚ`, a solution to the ACCs. -/
def inQuadToSol : InQuad × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, a₁, a₂, a₃) =>
  AnomalyFreeMk' (lineCube R.val.val a₁ a₂ a₃)
    (by erw [planeY₃B₃_quad, R.prop.1, R.prop.2.1, R.prop.2.2]; simp)
      (lineCube_cube R.val.val a₁ a₂ a₃)

lemma inQuadToSol_smul (R : InQuad) (c₁ c₂ c₃ d : ℚ) :
    inQuadToSol (R, (d * c₁), (d * c₂), (d * c₃)) = d • inQuadToSol (R, c₁, c₂, c₃) := by
  apply ACCSystem.Sols.ext
  change (lineCube _ _ _ _).val = _
  rw [lineCube_smul]
  rfl

/-- On elements of `inQuadSol` a right-inverse to `inQuadToSol`. -/
def inQuadProj (T : InQuadSol) : InQuad × ℚ × ℚ × ℚ :=
  (⟨⟨proj T.val.1.1, (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop.1⟩,
    (inQuadSolProp_iff_proj_inQuadProp T.val).mp T.prop.2.1⟩,
  (cubicCoeff T.val)⁻¹ * (cubeTriLin T.val.val T.val.val B₃.val),
  (cubicCoeff T.val)⁻¹ * (- cubeTriLin T.val.val T.val.val Y₃.val),
  (cubicCoeff T.val)⁻¹ *
  (cubeTriLin T.val.val T.val.val B₃.val * (dot B₃.val T.val.val - dot Y₃.val T.val.val)
  - cubeTriLin T.val.val T.val.val Y₃.val
    * (dot Y₃.val T.val.val - 2 * dot B₃.val T.val.val)))

lemma inQuadToSol_proj (T : InQuadSol) : inQuadToSol (inQuadProj T) = T.val := by
  rw [inQuadProj, inQuadToSol_smul]
  apply ACCSystem.Sols.ext
  change _ • (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_val, Y₃_plus_B₃_plus_proj, cube_proj, cube_proj_proj_B₃, cube_proj_proj_Y₃]
  ring_nf
  simp only [zero_smul, add_zero, zero_add]
  have h1 : (cubeTriLin T.val.val T.val.val Y₃.val ^ 2 * dot Y₃.val B₃.val ^ 3 * 3 +
      dot Y₃.val B₃.val ^ 3 * cubeTriLin T.val.val T.val.val B₃.val ^ 2* 3) = cubicCoeff T.val := by
    rw [cubicCoeff]
    ring
  rw [h1]
  have h2 := (inCubeSolProp_iff_cubicCoeff_zero T.val).mpr.mt T.prop.2.2
  rw [← SemigroupAction.mul_smul, mul_comm, mul_inv_cancel₀ h2]
  exact MulAction.one_smul T.1.val

/-- Given a element of `inQuadCube × ℚ × ℚ × ℚ`, a solution to the ACCs. -/
def inQuadCubeToSol : InQuadCube × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, b₁, b₂, b₃) =>
  AnomalyFreeMk' (planeY₃B₃ R.val.val.val b₁ b₂ b₃)
  (by rw [planeY₃B₃_quad, R.val.prop.1, R.val.prop.2.1, R.val.prop.2.2]; simp)
  (by rw [planeY₃B₃_cubic, R.prop.1, R.prop.2.1, R.prop.2.2]; simp)

lemma inQuadCubeToSol_smul (R : InQuadCube) (c₁ c₂ c₃ d : ℚ) :
    inQuadCubeToSol (R, (d * c₁), (d * c₂), (d * c₃)) = d • inQuadCubeToSol (R, c₁, c₂, c₃) := by
  apply ACCSystem.Sols.ext
  change (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_smul]
  rfl

/-- On elements of `inQuadCubeSol` a right-inverse to `inQuadCubeToSol`. -/
def inQuadCubeProj (T : InQuadCubeSol) : InQuadCube × ℚ × ℚ × ℚ :=
  (⟨⟨⟨proj T.val.1.1, (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop.1⟩,
    (inQuadSolProp_iff_proj_inQuadProp T.val).mp T.prop.2.1⟩,
    (inCubeSolProp_iff_proj_inCubeProp T.val).mp T.prop.2.2⟩,
  (dot Y₃.val B₃.val)⁻¹ * (dot Y₃.val T.val.val - dot B₃.val T.val.val),
  (dot Y₃.val B₃.val)⁻¹ * (2 * dot B₃.val T.val.val - dot Y₃.val T.val.val),
  (dot Y₃.val B₃.val)⁻¹ * 1)

lemma inQuadCubeToSol_proj (T : InQuadCubeSol) :
    inQuadCubeToSol (inQuadCubeProj T) = T.val := by
  rw [inQuadCubeProj, inQuadCubeToSol_smul]
  apply ACCSystem.Sols.ext
  change _ • (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_val, Y₃_plus_B₃_plus_proj]
  ring_nf
  simp only [zero_smul, add_zero, zero_add]
  rw [← SemigroupAction.mul_smul, mul_comm, mul_inv_cancel₀]
  · exact MulAction.one_smul (T.1).val
  · rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl]
    exact Ne.symm (OfNat.zero_ne_ofNat 108)

/-- A solution from an element of `MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ`. We will
show that this map is a surjection. -/
def toSol : MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, a, b, c) =>
  if h₃ : LineEqProp R ∧ InQuadProp R ∧ InCubeProp R then
    inQuadCubeToSol (⟨⟨⟨R, h₃.1⟩, h₃.2.1⟩, h₃.2.2⟩, a, b, c)
  else
    if h₂ : LineEqProp R ∧ InQuadProp R then
      inQuadToSol (⟨⟨R, h₂.1⟩, h₂.2⟩, a, b, c)
    else
      if h₁ : LineEqProp R then
        inLineEqToSol (⟨R, h₁⟩, a, b, c)
      else
        toSolNS ⟨R, a, b, c⟩

lemma toSol_toSolNSProj (T : NotInLineEqSol) :
    ∃ X, toSol X = T.val := by
  use toSolNSProj T.val
  have h1 : ¬ LineEqProp (toSolNSProj T.val).1 :=
    (linEqPropSol_iff_proj_linEqProp T.val).mpr.mt T.prop
  simp_rw [toSol, h1]
  exact toSolNS_proj T

lemma toSol_inLineEq (T : InLineEqSol) : ∃ X, toSol X = T.val := by
  let X := inLineEqProj T
  use ⟨X.1.val, X.2.1, X.2.2⟩
  have : ¬ InQuadProp X.1.val := (inQuadSolProp_iff_proj_inQuadProp T.val).mpr.mt T.prop.2
  have : LineEqProp X.1.val := (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop.1
  simp_all only [toSol]
  exact inLineEqToSol_proj T

lemma toSol_inQuad (T : InQuadSol) : ∃ X, toSol X = T.val := by
  let X := inQuadProj T
  use ⟨X.1.val.val, X.2.1, X.2.2⟩
  have : ¬ InCubeProp X.1.val.val := (inCubeSolProp_iff_proj_inCubeProp T.val).mpr.mt T.prop.2.2
  have : InQuadProp X.1.val.val := (inQuadSolProp_iff_proj_inQuadProp T.val).mp T.prop.2.1
  have : LineEqProp X.1.val.val := (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop.1
  simp_all only [toSol]
  exact inQuadToSol_proj T

lemma toSol_inQuadCube (T : InQuadCubeSol) : ∃ X, toSol X = T.val := by
  let X := inQuadCubeProj T
  use ⟨X.1.val.val.val, X.2.1, X.2.2⟩
  have : InCubeProp X.1.val.val.val := (inCubeSolProp_iff_proj_inCubeProp T.val).mp T.prop.2.2
  have : InQuadProp X.1.val.val.val := (inQuadSolProp_iff_proj_inQuadProp T.val).mp T.prop.2.1
  have : LineEqProp X.1.val.val.val := (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop.1
  simp_all only [toSol]
  exact inQuadCubeToSol_proj T

theorem toSol_surjective : Function.Surjective toSol := by
  intro T
  by_cases h₁ : ¬ LineEqPropSol T
  · exact toSol_toSolNSProj ⟨T, h₁⟩
  · simp only [not_not] at h₁
    by_cases h₂ : ¬ InQuadSolProp T
    · exact toSol_inLineEq ⟨T, And.intro h₁ h₂⟩
    · simp only [not_not] at h₂
      by_cases h₃ : ¬ InCubeSolProp T
      · exact toSol_inQuad ⟨T, And.intro h₁ (And.intro h₂ h₃)⟩
      · simp only [not_not] at h₃
        exact toSol_inQuadCube ⟨T, And.intro h₁ (And.intro h₂ h₃)⟩

end AnomalyFreePerp

end MSSMACC
