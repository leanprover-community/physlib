/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.Particles.StandardModel.GaugeAlgebra.Basic
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GlobalGaugeGroup
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GlobalGaugeGroup.UnitaryJet
/-!
# The gauge algebra as the Lie algebra of the global gauge group

The gauge algebra of the Standard Model is the Lie algebra of its global gauge group.

## i. Overview

The Lie algebra of the global gauge group `SU(3) × SU(2) × U(1)` consists of the block-diagonal
matrices `diag(X₃, X₂, X₁)` with `X₃` and `X₂` traceless anti-hermitian and `X₁` an imaginary
scalar, with the commutator as bracket. The gauge algebra `GaugeAlgebra` has the hermitian
matrices `c₃`, `c₂` and the real scalar `c₁` instead, with the bracket carrying a factor of `i`.
The two are identified through `c ↦ diag(i c₃, i c₂, i c₁)`, which is a Lie algebra
isomorphism.

## ii. Key results

- `StandardModel.gaugeAlgebraToMatrix` : the block-diagonal matrix `diag(i c₃, i c₂, i c₁)` of
  an element `c` of the gauge algebra.
- `StandardModel.gaugeAlgebraEquiv` : the Lie algebra isomorphism from `GaugeAlgebra` to the
  Lie algebra of `globalGaugeGroup`.
- `StandardModel.gaugeAlgebraEquiv_coe` : the underlying matrix of its value.
- `StandardModel.derivMat_su3Fund_gaugeAlgebraEquiv`,
  `StandardModel.derivMat_su2Fund_gaugeAlgebraEquiv`,
  `StandardModel.hypercharge_exp_gaugeAlgebraEquiv` : the derivatives of the fundamental
  representations and of the hypercharge, on the image of a gauge algebra element.
- `StandardModel.adjointRep_gaugeAlgebraEquiv` : the adjoint action of the global gauge group
  is the blockwise conjugation `GaugeAlgebra.adjointMap`.
- `StandardModel.gaugeDualToLie` : a functional on the gauge algebra transported to one on the
  Lie algebra of `globalGaugeGroup`.

## iii. Table of contents

- A. The block-diagonal matrix of a gauge algebra element
- B. The Lie algebra homomorphism
- C. The equivalence
- D. The fundamental representations and the hypercharge
- E. The adjoint action

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open GlobalGaugeGroup Matrix

/-- The `6 × 6` complex matrices on which the global gauge group acts. -/
local notation "𝕄" => Matrix (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ

/-!

## A. The block-diagonal matrix of a gauge algebra element

The real-linear map `c ↦ diag(i c₃, i c₂, i c₁)`, whose values are traceless anti-hermitian in
the non-abelian blocks and imaginary in the abelian one.

-/

/-- The block-diagonal matrix `diag(i c₃, i c₂, i c₁)` of an element `c` of the gauge algebra,
  with `c₃` and `c₂` hermitian traceless and `c₁` a real scalar. -/
noncomputable def gaugeAlgebraToMatrix : GaugeAlgebra →ₗ[ℝ] 𝕄 where
  toFun c := fromBlocks (Complex.I • c.toSU3Matrix) 0 0
    (fromBlocks (Complex.I • c.toSU2Matrix) 0 0 (Complex.I • scalar (Fin 1) c.toU1Value))
  map_add' a b := by
    simp only [GaugeAlgebra.add_toSU3Matrix, GaugeAlgebra.add_toSU2Matrix,
      GaugeAlgebra.add_toU1Value, smul_add, map_add, fromBlocks_add, add_zero]
  map_smul' r a := by
    simp only [GaugeAlgebra.smul_toSU3Matrix, GaugeAlgebra.smul_toSU2Matrix,
      GaugeAlgebra.smul_toU1Value, RingHom.id_apply, fromBlocks_smul, smul_zero]
    rw [scalar_smul, smul_comm Complex.I r, smul_comm Complex.I r, smul_comm Complex.I r]

/-- The block-diagonal matrix of a gauge algebra element lies in the Lie algebra of the global
  gauge group. -/
lemma gaugeAlgebraToMatrix_mem (c : GaugeAlgebra) :
    gaugeAlgebraToMatrix c ∈ globalGaugeGroup.lieAlgebra := by
  have hanti {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : star A = A) :
      star (Complex.I • A) = -(Complex.I • A) := by
    rw [star_smul, hA, Complex.star_def, Complex.conj_I, neg_smul]
  have h3 := mem_lieAlgebra_SU (hanti c.1.2.1)
    (by rw [Matrix.trace_smul, show (c.1 : Matrix (Fin 3) (Fin 3) ℂ).trace = 0 by
      simpa using c.1.2.2, smul_zero])
  have h2 := mem_lieAlgebra_SU (hanti c.2.1.2.1)
    (by rw [Matrix.trace_smul, show (c.2.1 : Matrix (Fin 2) (Fin 2) ℂ).trace = 0 by
      simpa using c.2.1.2.2, smul_zero])
  have h1 : Complex.I • scalar (Fin 1) c.toU1Value ∈ U1.lieAlgebra := by
    refine mem_lieAlgebra_U1 ?_
    rw [star_smul, star_scalar, Complex.star_def, Complex.conj_I, neg_smul]
    have : starRingEnd ℂ c.toU1Value = c.toU1Value := c.2.2.2
    rw [this]
  exact fromBlocks_mem_lieAlgebra_prod _ _ h3 (fromBlocks_mem_lieAlgebra_prod _ _ h2 h1)

/-!

## B. The Lie algebra homomorphism

The factor of `i` in the bracket of `GaugeAlgebra` is what makes the map a Lie algebra
homomorphism to the commutator bracket.

-/

/-- The Lie algebra homomorphism from the gauge algebra to the Lie algebra of the global gauge
  group, sending `c` to `diag(i c₃, i c₂, i c₁)`. -/
noncomputable def gaugeAlgebraHom : GaugeAlgebra →ₗ⁅ℝ⁆ globalGaugeGroup.lieSubalgebra where
  toFun c := ⟨gaugeAlgebraToMatrix c, gaugeAlgebraToMatrix_mem c⟩
  map_add' a b := Subtype.ext (map_add gaugeAlgebraToMatrix a b)
  map_smul' r a := Subtype.ext (map_smul gaugeAlgebraToMatrix r a)
  map_lie' {a b} := by
    refine Subtype.ext ?_
    show gaugeAlgebraToMatrix ⁅a, b⁆ = gaugeAlgebraToMatrix a * gaugeAlgebraToMatrix b -
      gaugeAlgebraToMatrix b * gaugeAlgebraToMatrix a
    simp only [gaugeAlgebraToMatrix, LinearMap.coe_mk, AddHom.coe_mk,
      GaugeAlgebra.bracket_toSU3Matrix, GaugeAlgebra.bracket_toSU2Matrix,
      GaugeAlgebra.bracket_toU1Value]
    simp [fromBlocks_multiply, smul_smul]
    ext (i | i | i) (j | j | j) <;>
      simp [sub_eq_add_neg, add_comm, diagonal_apply, mul_comm]

/-!

## C. The equivalence

-/

/-- The homomorphism from the gauge algebra is injective. -/
lemma gaugeAlgebraHom_injective : Function.Injective gaugeAlgebraHom := by
  intro a b hab
  have h := congrArg Subtype.val hab
  obtain ⟨h3, -, -, h⟩ := fromBlocks_inj.1 h
  obtain ⟨h2, -, -, h1⟩ := fromBlocks_inj.1 h
  refine GaugeAlgebra.ext_of_matrix ?_ ?_ ?_
  · exact smul_right_injective _ Complex.I_ne_zero h3
  · exact smul_right_injective _ Complex.I_ne_zero h2
  · have := congrFun (congrFun (smul_right_injective _ Complex.I_ne_zero h1) 0) 0
    simpa using this

/-- Every element of the Lie algebra of the global gauge group is the image of an element of the
  gauge algebra. The `SU(3)` and `SU(2)` blocks are traceless and anti-hermitian, and the
  `U(1)` block is an imaginary scalar. -/
lemma gaugeAlgebraHom_surjective : Function.Surjective gaugeAlgebraHom := by
  rintro ⟨X, hX⟩
  obtain ⟨X₃, h₃, Y, hY, rfl⟩ := (mem_lieAlgebra_prod_iff _ _).1 hX
  obtain ⟨X₂, h₂, Z, hZ, rfl⟩ := (mem_lieAlgebra_prod_iff _ _).1 hY
  obtain ⟨a, rfl⟩ := exists_eq_I_smul_scalar_of_mem_lieAlgebra_U1 hZ
  have hunit {n : ℕ} (G : GlobalGaugeGroup (Fin n)) (hG : G = SU n) {A : Matrix (Fin n) (Fin n) ℂ}
      (hA : A ∈ G.lieAlgebra) : star (-(Complex.I • A)) = -(Complex.I • A) ∧
        (-(Complex.I • A)).trace = 0 := by
    subst hG
    have h := star_eq_neg_of_mem_lieAlgebra (G := SU n) (fun g hg =>
      (mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp (mem_SU_iff.mp hg)).1)) hA
    refine ⟨?_, ?_⟩
    · rw [star_neg, star_smul, h, Complex.star_def, Complex.conj_I]; simp
    · rw [Matrix.trace_neg, Matrix.trace_smul, trace_eq_zero_of_mem_lieAlgebra_SU hA]; simp
  obtain ⟨hs3, ht3⟩ := hunit (SU 3) rfl h₃
  obtain ⟨hs2, ht2⟩ := hunit (SU 2) rfl h₂
  refine ⟨GaugeAlgebra.ofMatrixProd (-(Complex.I • X₃), -(Complex.I • X₂), (a : ℂ))
    ⟨hs3, ht3⟩ ⟨hs2, ht2⟩ (Complex.conj_ofReal a), ?_⟩
  refine Subtype.ext ?_
  show fromBlocks _ 0 0 (fromBlocks _ 0 0 _) = _
  simp [smul_smul]

/-- The Lie algebra isomorphism from the gauge algebra of the Standard Model to the Lie algebra
  of its global gauge group, sending `c` to `diag(i c₃, i c₂, i c₁)`. -/
noncomputable def gaugeAlgebraEquiv : GaugeAlgebra ≃ₗ⁅ℝ⁆ globalGaugeGroup.lieSubalgebra :=
  LieEquiv.ofBijective gaugeAlgebraHom ⟨gaugeAlgebraHom_injective, gaugeAlgebraHom_surjective⟩

/-- The underlying matrix of the image of `c` under `gaugeAlgebraEquiv` is
  `diag(i c₃, i c₂, i c₁)`. -/
@[simp]
lemma gaugeAlgebraEquiv_coe (c : GaugeAlgebra) :
    ((gaugeAlgebraEquiv c : globalGaugeGroup.lieSubalgebra) : 𝕄) =
      fromBlocks (Complex.I • c.toSU3Matrix) 0 0
        (fromBlocks (Complex.I • c.toSU2Matrix) 0 0
          (Complex.I • scalar (Fin 1) c.toU1Value)) := rfl

/-!

## D. The fundamental representations and the hypercharge

On the image of a gauge algebra element `c`, the derivatives of the fundamental representations
are `i c₃` and `i c₂`, and that of the hypercharge is `i c₁`. The matter fields of the Standard
Model read their infinitesimal actions off these.

-/

/-- The Lie algebra element `gaugeAlgebraEquiv c` acts on the fundamental representation of the
  `SU(3)` factor by `i c₃`. -/
lemma derivMat_su3Fund_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    derivMat su3Fund (gaugeAlgebraEquiv c) = Complex.I • c.toSU3Matrix := by
  rw [derivMat_su3Fund, gaugeAlgebraEquiv_coe, toBlocks_fromBlocks₁₁]

/-- The Lie algebra element `gaugeAlgebraEquiv c` acts on the fundamental representation of the
  `SU(2)` factor by `i c₂`. -/
lemma derivMat_su2Fund_gaugeAlgebraEquiv (c : GaugeAlgebra) :
    derivMat su2Fund (gaugeAlgebraEquiv c) = Complex.I • c.toSU2Matrix := by
  rw [derivMat_su2Fund, gaugeAlgebraEquiv_coe, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁]

/-- The hypercharge of the exponential of `t` times the image of `c` is `exp (t i c₁)`, so the
  derivative of the hypercharge at `gaugeAlgebraEquiv c` is `i c₁`. -/
lemma hypercharge_exp_gaugeAlgebraEquiv (c : GaugeAlgebra) (t : ℝ)
    (g : globalGaugeGroup.group)
    (hg : ((g : GL (Fin 3 ⊕ (Fin 2 ⊕ Fin 1)) ℂ) : 𝕄) =
      NormedSpace.exp (t • ((gaugeAlgebraEquiv c : globalGaugeGroup.lieSubalgebra) : 𝕄))) :
    ((hypercharge g : ℂˣ) : ℂ) = Complex.exp (t * (Complex.I * c.toU1Value)) := by
  have h : ((gaugeAlgebraEquiv c : globalGaugeGroup.lieSubalgebra) : 𝕄).toBlocks₂₂.toBlocks₂₂
      0 0 = Complex.I * c.toU1Value := by
    rw [gaugeAlgebraEquiv_coe]
    simp
  rw [hypercharge_exp _ t g hg, h]

/-!

## E. The adjoint action

The adjoint action of the global gauge group is blockwise conjugation on the gauge algebra, and
functionals on the gauge algebra are transported to the Lie algebra with their dual action.

-/

/-- The adjoint action of the global gauge group on its Lie algebra, transported along
  `gaugeGroupEquiv` and `gaugeAlgebraEquiv`, is the blockwise conjugation
  `GaugeAlgebra.adjointMap`. -/
lemma adjointRep_gaugeAlgebraEquiv (g : GaugeGroupI) (a : GaugeAlgebra) :
    globalGaugeGroup.adjointRep (gaugeGroupEquiv g) (gaugeAlgebraEquiv a) =
      gaugeAlgebraEquiv (GaugeAlgebra.adjointMap g a) := by
  refine Subtype.ext ?_
  rw [globalGaugeGroup.adjointRep_val]
  have hinv := gaugeGroupEquiv_val g⁻¹
  rw [map_inv] at hinv
  have h1 := gaugeGroupEquiv_val g
  simp only [gaugeAlgebraEquiv_coe, GaugeAlgebra.adjointMap_toSU3Matrix,
    GaugeAlgebra.adjointMap_toSU2Matrix, GaugeAlgebra.adjointMap_toU1Value]
  erw [hinv, h1]
  have e3 : ((g⁻¹.1 : Matrix.specialUnitaryGroup (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ) =
      star (g.1 : Matrix (Fin 3) (Fin 3) ℂ) := rfl
  have e2 : ((g⁻¹.2.1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      star (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  have e1 : ((g⁻¹.2.2 : unitary ℂ) : ℂ) = star (g.2.2 : ℂ) := by
    rfl
  rw [e3, e2, e1]
  have hu : (g.2.2 : ℂ) * star (g.2.2 : ℂ) = 1 := by
    simpa using Unitary.mul_star_self_of_mem g.2.2.2
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    GaugeGroupI.toSU3, GaugeGroupI.toSU2]
  congr 2
  · rw [mul_smul_comm, smul_mul_assoc]; rfl
  · rw [mul_smul_comm, smul_mul_assoc]; rfl
  · rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul]
    congr 2
    rw [mul_comm (g.2.2 : ℂ), mul_assoc, hu, mul_one]

/-- The dual of the adjoint action of the global gauge group on a functional of the form
  `φ ∘ gaugeAlgebraEquiv⁻¹` is the transport of the dual of `GaugeAlgebra.adjointMap`. -/
lemma dualMap_adjointRep_comp_symm (g : GaugeGroupI)
    (φ : Module.Dual ℝ GaugeAlgebra) :
    (globalGaugeGroup.adjointRep (gaugeGroupEquiv g)).dualMap
        (φ ∘ₗ (gaugeAlgebraEquiv.symm : globalGaugeGroup.lieSubalgebra →ₗ[ℝ] GaugeAlgebra)) =
      ((GaugeAlgebra.adjointMap g).dualMap φ) ∘ₗ
        (gaugeAlgebraEquiv.symm : globalGaugeGroup.lieSubalgebra →ₗ[ℝ] GaugeAlgebra) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := gaugeAlgebraEquiv.surjective x
  simp [LinearMap.dualMap_apply, adjointRep_gaugeAlgebraEquiv]

/-- A functional on the gauge algebra `GaugeAlgebra`, transported along `gaugeAlgebraEquiv` to
  one on the Lie algebra of the global gauge group. -/
noncomputable abbrev gaugeDualToLie (φ : Module.Dual ℝ GaugeAlgebra) :
    Module.Dual ℝ globalGaugeGroup.lieSubalgebra :=
  LinearMap.dualMap (gaugeAlgebraEquiv.symm : globalGaugeGroup.lieSubalgebra →ₗ[ℝ] GaugeAlgebra) φ

end StandardModel
