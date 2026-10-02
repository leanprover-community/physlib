/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules
public import Mathlib.RepresentationTheory.Intertwining
/-!

# Real Lorentz vectors

We define real Lorentz vectors in as representations of the Lorentz group.

-/

@[expose] public section

noncomputable section

open Matrix Module MatrixGroups Complex TensorProduct

namespace Lorentz
open minkowskiMatrix

/-- The standard basis of contravariant Lorentz vectors. -/
def contrBasis (d : ℕ := 3) : Basis (Fin 1 ⊕ Fin d) ℝ (ContrMod d) :=
  Basis.ofEquivFun ContrMod.toFin1dℝEquiv

@[simp]
lemma contrBasis_ρ_apply {d : ℕ} (M : LorentzGroup d) (i j : Fin 1 ⊕ Fin d) :
    (LinearMap.toMatrix (contrBasis d) (contrBasis d)) (ContrMod.rep M) i j =
    M.1 i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [contrBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1 *ᵥ (Pi.single j 1)) i = _
  simp

@[simp]
lemma contrBasis_toFin1dℝ {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (contrBasis d i).toFin1dℝ = Pi.single i 1 := by
  simp only [ContrMod.toFin1dℝ, contrBasis, Basis.coe_ofEquivFun]
  rfl

lemma contrBasis_repr_apply {d : ℕ} (p : ContrMod d) (i : Fin 1 ⊕ Fin d) :
    (contrBasis d).repr p i = p.val i := by
  simp only [contrBasis, Basis.ofEquivFun_repr_apply]
  rfl

/-- The standard basis of contravariant Lorentz vectors indexed by `Fin (1 + d)`. -/
def contrBasisFin (d : ℕ := 3) : Basis (Fin (1 + d)) ℝ (ContrMod d) :=
  Basis.reindex (contrBasis d) finSumFinEquiv

@[simp]
lemma contrBasisFin_toFin1dℝ {d : ℕ} (i : Fin (1 + d)) :
    (contrBasisFin d i).toFin1dℝ = Pi.single (finSumFinEquiv.symm i) 1 := by
  simp only [contrBasisFin, Basis.reindex_apply, contrBasis_toFin1dℝ]

lemma contrBasisFin_repr_apply {d : ℕ} (p : ContrMod d) (i : Fin (1 + d)) :
    (contrBasisFin d).repr p i = p.val (finSumFinEquiv.symm i) := by rfl

lemma continuous_contr {T : Type} [TopologicalSpace T] (f : T → ContrMod d)
    (h : Continuous (fun i => (f i).toFin1dℝ)) : Continuous f := by
  exact continuous_induced_rng.mpr h

lemma contr_continuous {T : Type} [TopologicalSpace T] (f : ContrMod d → T)
    (h : Continuous (f ∘ (@ContrMod.toFin1dℝEquiv d).symm)) : Continuous f := by
  let x := Equiv.toHomeomorphOfIsInducing (@ContrMod.toFin1dℝEquiv d).toEquiv
    ContrMod.toFin1dℝEquiv_isInducing
  rw [← Homeomorph.comp_continuous_iff' x.symm]
  exact h

/-- The standard basis of contravariant Lorentz vectors. -/
def coBasis (d : ℕ := 3) : Basis (Fin 1 ⊕ Fin d) ℝ (CoMod d) :=
  Basis.ofEquivFun CoMod.toFin1dℝEquiv

@[simp]
lemma coBasis_ρ_apply {d : ℕ} (M : LorentzGroup d) (i j : Fin 1 ⊕ Fin d) :
    (LinearMap.toMatrix (coBasis d) (coBasis d)) (CoMod.rep M) i j =
    M⁻¹ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [coBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change (_ *ᵥ (Pi.single j 1)) i = _
  simp [LorentzGroup.transpose, ← LorentzGroup.coe_inv]

lemma coBasis_repr_apply {d : ℕ} (p : CoMod d) (i : Fin 1 ⊕ Fin d) :
    (coBasis d).repr p i = p.val i := by
  simp only [coBasis, Basis.ofEquivFun_repr_apply]
  rfl

@[simp]
lemma coBasis_toFin1dℝ {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (coBasis d i).toFin1dℝ = Pi.single i 1 := by
  simp only [coBasis, Basis.coe_ofEquivFun]
  rfl

/-- The standard basis of covariant Lorentz vectors indexed by `Fin (1 + d)`. -/
def coBasisFin (d : ℕ := 3) : Basis (Fin (1 + d)) ℝ (CoMod d) :=
  Basis.reindex (coBasis d) finSumFinEquiv

@[simp]
lemma coBasisFin_toFin1dℝ {d : ℕ} (i : Fin (1 + d)) :
    (coBasisFin d i).toFin1dℝ = Pi.single (finSumFinEquiv.symm i) 1 := by
  simp only [coBasisFin, Basis.reindex_apply, coBasis_toFin1dℝ]

lemma coBasisFin_repr_apply {d : ℕ} (p : CoMod d) (i : Fin (1 + d)) :
    (coBasisFin d).repr p i = p.val (finSumFinEquiv.symm i) := by rfl

/-!

## Isomorphism between contravariant and covariant Lorentz vectors

-/

open Representation
/-- The morphism of representations from `ContrMod.rep` to `CoMod.rep` defined by multiplication
  with the metric. -/
def Contr.toCo (d : ℕ) : IntertwiningMap (ContrMod.rep (d := d)) (CoMod.rep (d := d)) where
  toFun := fun ψ => CoMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ)
  map_add' := by
    intro ψ ψ'
    simp only [map_add, mulVec_add]
  map_smul' := by
    intro r ψ
    simp only [_root_.map_smul, mulVec_smul, RingHom.id_apply]
  isIntertwining' g := by
    ext1 ψ
    conv_lhs =>
      change CoMod.toFin1dℝEquiv.symm (η *ᵥ (g.1 *ᵥ ψ.toFin1dℝ))
      rw [mulVec_mulVec, LorentzGroup.minkowskiMatrix_comm, ← mulVec_mulVec]
    rfl

/-- The morphism of representations from `CoMod.rep` to `ContrMod.rep` defined by multiplication
  with the metric. -/
def Co.toContr (d : ℕ) : IntertwiningMap (CoMod.rep (d := d)) (ContrMod.rep (d := d)) where
    toFun := fun ψ => ContrMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ)
    map_add' := by
      intro ψ ψ'
      simp only [map_add, mulVec_add]
    map_smul' := by
      intro r ψ
      simp only [_root_.map_smul, mulVec_smul, RingHom.id_apply]
    isIntertwining' g := by
      ext1 ψ
      conv_lhs =>
        change ContrMod.toFin1dℝEquiv.symm (η *ᵥ ((LorentzGroup.transpose g⁻¹).1 *ᵥ ψ.toFin1dℝ))
        rw [mulVec_mulVec, ← LorentzGroup.comm_minkowskiMatrix, ← mulVec_mulVec]
      rfl

/-- The isomorphism between `ContrMod.rep` and `CoMod.rep` induced by multiplication with the
  Minkowski metric. -/
def contrIsoCo (d : ℕ) : Representation.Equiv (ContrMod.rep (d := d)) (CoMod.rep (d := d)) := by
  refine Representation.Equiv.mk' (Contr.toCo d) (Co.toContr d) ?_ ?_
  · intro x
    simp [Contr.toCo, Co.toContr]
  · intro x
    simp [Contr.toCo, Co.toContr]

/-!

## Other properties

-/
namespace Contr

open Lorentz
lemma ρ_stdBasis (μ : Fin 1 ⊕ Fin 3) (Λ : LorentzGroup 3) :
    ContrMod.rep Λ (ContrMod.stdBasis μ) = ∑ j, Λ.1 j μ • ContrMod.stdBasis j := by
  change Λ *ᵥ ContrMod.stdBasis μ = ∑ j, Λ.1 j μ • ContrMod.stdBasis j
  apply ContrMod.ext
  simp only [toLinAlgEquiv_self, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, ContrMod.val_add, ContrMod.val_smul]

end Contr
end Lorentz
end
