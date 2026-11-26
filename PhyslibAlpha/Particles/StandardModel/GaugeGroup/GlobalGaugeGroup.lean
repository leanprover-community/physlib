/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.OfMatrixRep
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.UnitaryJet
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Realization.Conditions
/-!
# The Standard Model gauge group as a global gauge group

The gauge group `SU(3) × SU(2) × U(1)` as block-diagonal `6 × 6` complex matrices.

## i. Overview

The global gauge group of the Standard Model is the product `SU(3) × (SU(2) × U(1))` of global
gauge groups, made of the block-diagonal matrices `diag(g₃, g₂, u)`. Its elements are the
elements of `GaugeGroupI`, through `StandardModel.gaugeGroupEquiv`. Taking the `SU(3)` block,
the `SU(2)` block and the phase `u` are continuous homomorphisms.

The representations of the three factors are pulled back along the projections to the blocks.
The `SU(3)` and `SU(2)` blocks act on the fundamental representations, and the phase `u` is the
hypercharge character. The matter fields of the Standard Model are built from these.

## ii. Key results

- `StandardModel.globalGaugeGroup` : the global gauge group `SU(3) × SU(2) × U(1)`.
- `StandardModel.gaugeGroupEquiv` : its elements are those of `GaugeGroupI`.
- The instance `CompactSpace globalGaugeGroup.group` : the global gauge group is compact.
- `StandardModel.su3Block`, `StandardModel.su2Block`, `StandardModel.u1Phase` : the blocks of
  its elements, which on the image of `gaugeGroupEquiv` are the three factors
  (`StandardModel.su3Block_gaugeGroupEquiv` and its companions).
- `StandardModel.su3Fund`, `StandardModel.su2Fund` : the fundamental representations of the
  `SU(3)` and `SU(2)` factors, as continuous matrix representations of the global gauge group,
  with derivatives `StandardModel.derivMat_su3Fund` and `StandardModel.derivMat_su2Fund`.
- `StandardModel.hypercharge` : the hypercharge character, with derivative the `u(1)` entry
  (see `StandardModel.hypercharge_exp`).

## iii. Table of contents

- A. The global gauge group
- B. The blocks of the global gauge group
- C. The representations of the factors

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open GlobalGaugeGroup Matrix MatrixGroups

/-- The `6 × 6` complex matrices on which the global gauge group acts. -/
local notation "𝕄" => Matrix (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ

/-!

## A. The global gauge group

The product of the global gauge groups `SU 3`, `SU 2` and `U1`, its identification with
`GaugeGroupI` and its compactness.

-/

/-- The global gauge group of the Standard Model, `SU(3) × SU(2) × U(1)` as the
  block-diagonal matrices `diag(g₃, g₂, u)` on `ℂ³ ⊕ ℂ² ⊕ ℂ`. -/
def globalGaugeGroup : GlobalGaugeGroup (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) :=
  (GlobalGaugeGroup.SU 3).prod ((GlobalGaugeGroup.SU 2).prod GlobalGaugeGroup.U1)

/-- The gauge group `GaugeGroupI` of the Standard Model is its global gauge group, through the
  block-diagonal matrices. -/
noncomputable def gaugeGroupEquiv : GaugeGroupI ≃* globalGaugeGroup.group :=
  (MulEquiv.prodCongr (SU.groupEquiv 3)
    ((MulEquiv.prodCongr (SU.groupEquiv 2) U1.groupEquiv).trans
      (prodGroupEquiv (SU 2) U1))).trans (prodGroupEquiv (SU 3) ((SU 2).prod U1))

/-- An element of `GaugeGroupI` is the block-diagonal matrix of its three components. -/
@[simp]
lemma gaugeGroupEquiv_val (g : GaugeGroupI) :
    (((gaugeGroupEquiv g : globalGaugeGroup.group) : GL (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ) : 𝕄) =
      fromBlocks (g.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
        (fromBlocks (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (scalar (Fin 1) (g.2.2 : ℂ))) :=
  rfl

/-- The global gauge group of the Standard Model is compact, being a product of the compact
  groups `SU(3)`, `SU(2)` and `U(1)`. -/
instance : CompactSpace globalGaugeGroup.group := by
  unfold globalGaugeGroup
  infer_instance

/-!

## B. The blocks of the global gauge group

The `SU(3)` block, the `SU(2)` block and the phase of an element, as homomorphisms, read off
the matrix and continuous.

-/

/-- The `SU(3)` block `g₃` of an element `diag(g₃, g₂, u)` of the global gauge group. -/
noncomputable def su3Block : globalGaugeGroup.group →* Matrix (Fin 3) (Fin 3) ℂ :=
  (specialUnitaryGroup (Fin 3) ℂ).subtype.comp
    ((MonoidHom.fst _ _).comp gaugeGroupEquiv.symm.toMonoidHom)

/-- The `SU(2)` block `g₂` of an element `diag(g₃, g₂, u)` of the global gauge group. -/
noncomputable def su2Block : globalGaugeGroup.group →* Matrix (Fin 2) (Fin 2) ℂ :=
  (specialUnitaryGroup (Fin 2) ℂ).subtype.comp
    ((MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp gaugeGroupEquiv.symm.toMonoidHom))

/-- The phase `u` of an element `diag(g₃, g₂, u)` of the global gauge group. -/
noncomputable def u1Phase : globalGaugeGroup.group →* ℂˣ :=
  Unitary.toUnits.comp
    ((MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp gaugeGroupEquiv.symm.toMonoidHom))

/-- The `SU(3)` block of the image of a gauge transformation is its colour factor. -/
@[simp]
lemma su3Block_gaugeGroupEquiv (g : GaugeGroupI) :
    su3Block (gaugeGroupEquiv g) = (g.toSU3.1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  show (((gaugeGroupEquiv.symm (gaugeGroupEquiv g)).1 : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The `SU(2)` block of the image of a gauge transformation is its isospin factor. -/
@[simp]
lemma su2Block_gaugeGroupEquiv (g : GaugeGroupI) :
    su2Block (gaugeGroupEquiv g) = (g.toSU2.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  show (((gaugeGroupEquiv.symm (gaugeGroupEquiv g)).2.1 : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The phase of the image of a gauge transformation is its hypercharge factor. -/
@[simp]
lemma u1Phase_gaugeGroupEquiv (g : GaugeGroupI) :
    ((u1Phase (gaugeGroupEquiv g) : ℂˣ) : ℂ) = (g.toU1.1 : ℂ) := by
  show (((gaugeGroupEquiv.symm (gaugeGroupEquiv g)).2.2 : unitary ℂ) : ℂ) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- An element of the global gauge group is the block-diagonal matrix of its blocks. -/
lemma globalGaugeGroup_val_eq_fromBlocks (g : globalGaugeGroup.group) :
    ((g : GL (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ) : 𝕄) =
      fromBlocks (su3Block g) 0 0 (fromBlocks (su2Block g) 0 0
        (scalar (Fin 1) (u1Phase g : ℂ))) := by
  conv_lhs => rw [← gaugeGroupEquiv.apply_symm_apply g]
  rfl

/-- The `SU(3)` block is the upper-left `3 × 3` block of the matrix. -/
lemma su3Block_eq (g : globalGaugeGroup.group) :
    su3Block g = toBlocks₁₁ ((g : GL (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ) : 𝕄) := by
  rw [globalGaugeGroup_val_eq_fromBlocks, toBlocks_fromBlocks₁₁]

/-- The `SU(2)` block is the middle `2 × 2` block of the matrix. -/
lemma su2Block_eq (g : globalGaugeGroup.group) :
    su2Block g = toBlocks₁₁ (toBlocks₂₂ ((g : GL (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ) : 𝕄)) := by
  rw [globalGaugeGroup_val_eq_fromBlocks, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁]

/-- The phase is the lower-right entry of the matrix. -/
lemma u1Phase_eq (g : globalGaugeGroup.group) :
    (u1Phase g : ℂ) = toBlocks₂₂ (toBlocks₂₂ ((g : GL (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ) : 𝕄)) 0 0 := by
  rw [globalGaugeGroup_val_eq_fromBlocks, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₂₂]
  simp

/-- The matrix of an element of the global gauge group depends continuously on it. -/
lemma continuous_globalGaugeGroup_val :
    Continuous fun g : globalGaugeGroup.group => ((g : GL (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ) : 𝕄) :=
  Units.continuous_val.comp continuous_subtype_val

/-- The `SU(3)` block depends continuously on the gauge transformation. -/
lemma continuous_su3Block : Continuous fun g => su3Block g :=
  (continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp ((continuous_apply _).comp continuous_globalGaugeGroup_val)).congr
      fun g => (su3Block_eq g).symm

/-- The `SU(2)` block depends continuously on the gauge transformation. -/
lemma continuous_su2Block : Continuous fun g => su2Block g :=
  (continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp ((continuous_apply _).comp continuous_globalGaugeGroup_val)).congr
      fun g => (su2Block_eq g).symm

/-- The phase depends continuously on the gauge transformation. -/
lemma continuous_u1Phase : Continuous fun g => (u1Phase g : ℂ) :=
  ((continuous_apply _).comp ((continuous_apply _).comp continuous_globalGaugeGroup_val)).congr
    fun g => (u1Phase_eq g).symm

/-!

## C. The representations of the factors

The fundamental representations of the `SU(3)` and `SU(2)` factors are the blocks of a gauge
transformation `diag(g₃, g₂, u)`, which act by `g₃` and `g₂`. The hypercharge character is the
phase `u`, and its derivative is the entry of the `U(1)` block of a Lie algebra element.

-/

/-- A continuous monoid homomorphism from the global gauge group to a monoid, which takes
  values in the units, is a continuous homomorphism to the units. -/
lemma continuous_toHomUnits {M : Type} [Monoid M] [TopologicalSpace M]
    {f : globalGaugeGroup.group →* M} (hf : Continuous f) : Continuous f.toHomUnits :=
  Units.continuous_iff.2 ⟨hf, (hf.comp continuous_inv).congr fun g =>
    congrArg Units.val (map_inv f.toHomUnits g)⟩

/-- The fundamental representation of the `SU(3)` factor, as a continuous representation of the
  global gauge group. A gauge transformation `diag(g₃, g₂, u)` acts by `g₃`. -/
noncomputable def su3Fund : globalGaugeGroup.group →ₜ* (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  ⟨su3Block.toHomUnits, continuous_toHomUnits continuous_su3Block⟩

/-- The fundamental representation of the `SU(2)` factor, as a continuous representation of the
  global gauge group. A gauge transformation `diag(g₃, g₂, u)` acts by `g₂`. -/
noncomputable def su2Fund : globalGaugeGroup.group →ₜ* (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  ⟨su2Block.toHomUnits, continuous_toHomUnits continuous_su2Block⟩

/-- A gauge transformation acts on the fundamental representation of the `SU(3)` factor by
  its `SU(3)` block. -/
@[simp]
lemma su3Fund_val (g : globalGaugeGroup.group) :
    ((su3Fund g : (Matrix (Fin 3) (Fin 3) ℂ)ˣ) : Matrix (Fin 3) (Fin 3) ℂ) = su3Block g := rfl

/-- A gauge transformation acts on the fundamental representation of the `SU(2)` factor by
  its `SU(2)` block. -/
@[simp]
lemma su2Fund_val (g : globalGaugeGroup.group) :
    ((su2Fund g : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) = su2Block g := rfl

/-- The Lie algebra acts on the fundamental representation of the `SU(3)` factor by its
  `SU(3)` block. -/
lemma derivMat_su3Fund (c : globalGaugeGroup.lieSubalgebra) :
    derivMat su3Fund c = (c : 𝕄).toBlocks₁₁ := by
  refine derivMat_eq_of _ fun t g hg => ?_
  rw [su3Fund_val, su3Block_eq, hg,
    exp_smul_eq_fromBlocks_of_mem_lieAlgebra_prod (SU 3) ((SU 2).prod U1) c.2,
    toBlocks_fromBlocks₁₁]

/-- The Lie algebra acts on the fundamental representation of the `SU(2)` factor by its
  `SU(2)` block. -/
lemma derivMat_su2Fund (c : globalGaugeGroup.lieSubalgebra) :
    derivMat su2Fund c = (c : 𝕄).toBlocks₂₂.toBlocks₁₁ := by
  have h₂₂ := (SU 3).toBlocks_mem_lieAlgebra_of_mem_lieAlgebra_prod
    ((SU 2).prod U1) c.2
  refine derivMat_eq_of _ fun t g hg => ?_
  rw [su2Fund_val, su2Block_eq, hg,
    exp_smul_eq_fromBlocks_of_mem_lieAlgebra_prod (SU 3) ((SU 2).prod U1) c.2,
    toBlocks_fromBlocks₂₂,
    exp_smul_eq_fromBlocks_of_mem_lieAlgebra_prod (SU 2) U1 h₂₂.2, toBlocks_fromBlocks₁₁]

/-- The hypercharge character of the global gauge group is the phase `u` of an element
  `diag(g₃, g₂, u)`. Its derivative is the entry of the `U(1)` block of a Lie algebra
  element, see `hypercharge_exp`. -/
noncomputable def hypercharge : globalGaugeGroup.group →ₜ* ℂˣ :=
  ⟨u1Phase, Units.continuous_iff.2 ⟨continuous_u1Phase,
    (continuous_u1Phase.comp continuous_inv).congr fun g =>
      congrArg Units.val (map_inv u1Phase g)⟩⟩

/-- The hypercharge character of the exponential of a Lie algebra element is the exponential of
  the entry of its `U(1)` block, that is `hypercharge (exp (t c)) = exp (t z)` with `z` the
  derivative of the hypercharge at `c`. -/
lemma hypercharge_exp (c : globalGaugeGroup.lieSubalgebra) (t : ℝ)
    (g : globalGaugeGroup.group)
    (hg : ((g : GL (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ) : 𝕄) =
      NormedSpace.exp (t • (c : 𝕄))) :
    ((hypercharge g : ℂˣ) : ℂ) = Complex.exp (t * (c : 𝕄).toBlocks₂₂.toBlocks₂₂ 0 0) := by
  have h₂₂ := (SU 3).toBlocks_mem_lieAlgebra_of_mem_lieAlgebra_prod
    ((SU 2).prod U1) c.2
  have hs : t • (c : 𝕄).toBlocks₂₂.toBlocks₂₂ =
      scalar (Fin 1) ((t : ℂ) * (c : 𝕄).toBlocks₂₂.toBlocks₂₂ 0 0) :=
    Matrix.ext fun i j => by
      fin_cases i
      fin_cases j
      simp [Complex.real_smul]
  show (u1Phase g : ℂ) = _
  rw [u1Phase_eq, hg, exp_smul_eq_fromBlocks_of_mem_lieAlgebra_prod (SU 3) ((SU 2).prod U1)
    c.2, toBlocks_fromBlocks₂₂,
    exp_smul_eq_fromBlocks_of_mem_lieAlgebra_prod (SU 2) U1 h₂₂.2, toBlocks_fromBlocks₂₂,
    hs, exp_scalar]
  simp only [scalar_apply, diagonal_apply_eq]

end StandardModel
