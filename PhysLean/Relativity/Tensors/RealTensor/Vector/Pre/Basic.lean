/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.Modules
public import Mathlib.RepresentationTheory.Rep
/-!

# Real Lorentz vectors

We define real Lorentz vectors in as representations of the Lorentz group.

-/

@[expose] public section

noncomputable section

open Matrix Module MatrixGroups Complex TensorProduct

namespace Lorentz
open minkowskiMatrix
/-- The representation of `LorentzGroup d` on real vectors corresponding to contravariant
  Lorentz vectors. In index notation these have an up index `ψⁱ`. -/
def Contr (d : ℕ) : Rep ℝ (LorentzGroup d) := Rep.of ContrMod.rep

/-- The standard basis of contravariant Lorentz vectors. -/
def contrBasis (d : ℕ := 3) : Basis (Fin 1 ⊕ Fin d) ℝ (Contr d) :=
  Basis.ofEquivFun ContrMod.toFin1dℝEquiv

@[simp]
lemma contrBasis_ρ_apply {d : ℕ} (M : LorentzGroup d) (i j : Fin 1 ⊕ Fin d) :
    (LinearMap.toMatrix (contrBasis d) (contrBasis d)) ((Contr d).ρ M) i j =
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

/-- The standard basis of contravariant Lorentz vectors indexed by `Fin (1 + d)`. -/
def contrBasisFin (d : ℕ := 3) : Basis (Fin (1 + d)) ℝ (Contr d) :=
  Basis.reindex (contrBasis d) finSumFinEquiv

@[simp]
lemma contrBasisFin_toFin1dℝ {d : ℕ} (i : Fin (1 + d)) :
    (contrBasisFin d i).toFin1dℝ = Pi.single (finSumFinEquiv.symm i) 1 := by
  simp only [contrBasisFin, Basis.reindex_apply, contrBasis_toFin1dℝ]

lemma contrBasisFin_repr_apply {d : ℕ} (p : Contr d) (i : Fin (1 + d)) :
    (contrBasisFin d).repr p i = p.val (finSumFinEquiv.symm i) := by rfl

/-- The representation of contravariant Lorentz vectors forms a topological space, induced
  by its equivalence to `Fin 1 ⊕ Fin d → ℝ`. -/
instance : TopologicalSpace (Contr d) := TopologicalSpace.induced
  ContrMod.toFin1dℝEquiv (Pi.topologicalSpace)

lemma continuous_contr {T : Type} [TopologicalSpace T] (f : T → Contr d)
    (h : Continuous (fun i => (f i).toFin1dℝ)) : Continuous f := by
  exact continuous_induced_rng.mpr h

lemma contr_continuous {T : Type} [TopologicalSpace T] (f : Contr d → T)
    (h : Continuous (f ∘ (@ContrMod.toFin1dℝEquiv d).symm)) : Continuous f := by
  let x := Equiv.toHomeomorphOfIsInducing (@ContrMod.toFin1dℝEquiv d).toEquiv
    ContrMod.toFin1dℝEquiv_isInducing
  rw [← Homeomorph.comp_continuous_iff' x.symm]
  exact h

/-- The representation of `LorentzGroup d` on real vectors corresponding to covariant
  Lorentz vectors. In index notation these have an up index `ψⁱ`. -/
def Co (d : ℕ) : Rep ℝ (LorentzGroup d) := Rep.of CoMod.rep

/-- The standard basis of contravariant Lorentz vectors. -/
def coBasis (d : ℕ := 3) : Basis (Fin 1 ⊕ Fin d) ℝ (Co d) :=
  Basis.ofEquivFun CoMod.toFin1dℝEquiv

@[simp]
lemma coBasis_ρ_apply {d : ℕ} (M : LorentzGroup d) (i j : Fin 1 ⊕ Fin d) :
    (LinearMap.toMatrix (coBasis d) (coBasis d)) ((Co d).ρ M) i j =
    M⁻¹ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [coBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change (_ *ᵥ (Pi.single j 1)) i = _
  simp [LorentzGroup.transpose, ← LorentzGroup.coe_inv]

@[simp]
lemma coBasis_toFin1dℝ {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (coBasis d i).toFin1dℝ = Pi.single i 1 := by
  simp only [coBasis, Basis.coe_ofEquivFun]
  rfl

/-- The standard basis of covariant Lorentz vectors indexed by `Fin (1 + d)`. -/
def coBasisFin (d : ℕ := 3) : Basis (Fin (1 + d)) ℝ (Co d) :=
  Basis.reindex (coBasis d) finSumFinEquiv

@[simp]
lemma coBasisFin_toFin1dℝ {d : ℕ} (i : Fin (1 + d)) :
    (coBasisFin d i).toFin1dℝ = Pi.single (finSumFinEquiv.symm i) 1 := by
  simp only [coBasisFin, Basis.reindex_apply, coBasis_toFin1dℝ]

lemma coBasisFin_repr_apply {d : ℕ} (p : Co d) (i : Fin (1 + d)) :
    (coBasisFin d).repr p i = p.val (finSumFinEquiv.symm i) := by rfl

open CategoryTheory.MonoidalCategory

/-!

## Isomorphism between contravariant and covariant Lorentz vectors

-/

/-- The morphism of representations from `Contr d` to `Co d` defined by multiplication
  with the metric. -/
def Contr.toCo (d : ℕ) : Contr d ⟶ Co d where
  hom := ModuleCat.ofHom {
    toFun := fun ψ => CoMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ),
    map_add' := by
      intro ψ ψ'
      simp only [map_add, mulVec_add]
    map_smul' := by
      intro r ψ
      simp only [_root_.map_smul, mulVec_smul, RingHom.id_apply]}
  comm g := by
    ext ψ : 2
    simp only [ModuleCat.hom_comp]
    conv_lhs =>
      change CoMod.toFin1dℝEquiv.symm (η *ᵥ (g.1 *ᵥ ψ.toFin1dℝ))
      rw [mulVec_mulVec, LorentzGroup.minkowskiMatrix_comm, ← mulVec_mulVec]
    rfl

/-- The morphism of representations from `Co d` to `Contr d` defined by multiplication
  with the metric. -/
def Co.toContr (d : ℕ) : Co d ⟶ Contr d where
  hom := ModuleCat.ofHom {
    toFun := fun ψ => ContrMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ),
    map_add' := by
      intro ψ ψ'
      simp only [map_add, mulVec_add]
    map_smul' := by
      intro r ψ
      simp only [_root_.map_smul, mulVec_smul, RingHom.id_apply]}
  comm g := by
    ext ψ : 2
    simp only [ModuleCat.hom_comp]
    conv_lhs =>
      change ContrMod.toFin1dℝEquiv.symm (η *ᵥ ((LorentzGroup.transpose g⁻¹).1 *ᵥ ψ.toFin1dℝ))
      rw [mulVec_mulVec, ← LorentzGroup.comm_minkowskiMatrix, ← mulVec_mulVec]
    rfl

/-- The isomorphism between `Contr d` and `Co d` induced by multiplication with the
  Minkowski metric. -/
def contrIsoCo (d : ℕ) : Contr d ≅ Co d where
  hom := Contr.toCo d
  inv := Co.toContr d
  hom_inv_id := by
    ext ψ
    simp only [Action.comp_hom, ModuleCat.hom_comp, Action.id_hom,
      ModuleCat.id_apply]
    conv_lhs => change ContrMod.toFin1dℝEquiv.symm (η *ᵥ
      CoMod.toFin1dℝEquiv (CoMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ)))
    rw [LinearEquiv.apply_symm_apply, mulVec_mulVec, minkowskiMatrix.sq]
    simp
  inv_hom_id := by
    ext ψ
    simp only [Action.comp_hom, ModuleCat.hom_comp, Action.id_hom,
      ModuleCat.id_apply]
    conv_lhs => change CoMod.toFin1dℝEquiv.symm (η *ᵥ
      ContrMod.toFin1dℝEquiv (ContrMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ)))
    rw [LinearEquiv.apply_symm_apply, mulVec_mulVec, minkowskiMatrix.sq]
    simp

/-!

## Other properties

-/
namespace Contr

open Lorentz
lemma ρ_stdBasis (μ : Fin 1 ⊕ Fin 3) (Λ : LorentzGroup 3) :
    (Contr 3).ρ Λ (ContrMod.stdBasis μ) = ∑ j, Λ.1 j μ • ContrMod.stdBasis j := by
  change Λ *ᵥ ContrMod.stdBasis μ = ∑ j, Λ.1 j μ • ContrMod.stdBasis j
  apply ContrMod.ext
  simp only [toLinAlgEquiv_self, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, ContrMod.val_add, ContrMod.val_smul]

end Contr
end Lorentz
end
