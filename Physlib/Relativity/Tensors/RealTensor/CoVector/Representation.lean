/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Physlib.Relativity.LorentzGroup.Basic
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Basic
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.RepresentationDual
/-!

# Representation of the Lorentz group on Lorentz vectors

In this module we define the representation of the Lorentz group on Lorentz covectors.
This does not define the MulAction on `Lorentz.CoVector`, which is induced
by its tensor structure.

-/

@[expose] public section


open Module Matrix MatrixGroups Complex TensorProduct

noncomputable section

namespace Lorentz

namespace CoVector
attribute [-simp] Fintype.sum_sum_type

/-- The representation of the Lorentz group on Lorentz covectors. -/
def rep {d : ℕ} : Representation ℝ (LorentzGroup d) (CoVector d) where
  toFun Λ := Matrix.toLinAlgEquiv basis (LorentzGroup.transpose Λ⁻¹)
  map_one' := by
    simp only [inv_one, LorentzGroup.transpose_one, lorentzGroupIsGroup_one_coe, _root_.map_one]
  map_mul' x y := by
    simp only [_root_.mul_inv_rev, LorentzGroup.inv_eq_dual, LorentzGroup.transpose_mul,
      lorentzGroupIsGroup_mul_coe, _root_.map_mul]

/-!

## Properties of the representation.

-/

lemma rep_apply_eq_mulVec (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) :
    rep Λ v = (LorentzGroup.transpose Λ⁻¹) *ᵥ v := by rfl

lemma rep_apply_eq_sum (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, (Λ⁻¹).1 j k • v j := rfl

lemma rep_apply_eq_sum_coe (d : ℕ) (Λ : LorentzGroup d) (v : CoVector d) (k : Fin 1 ⊕ Fin d) :
    rep Λ v k = ∑ j, Λ.1⁻¹ j k • v j := by
  rw [rep_apply_eq_sum, LorentzGroup.coe_inv]

lemma rep_apply_basis {d} (μ : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) :
    rep Λ (basis μ) = ∑ j, Λ.1⁻¹ μ j • basis j := by
  ext k
  simp [rep_apply_eq_sum_coe, apply_sum]

lemma rep_toMatrix (d : ℕ) (Λ : LorentzGroup d) :
    LinearMap.toMatrix basis basis (rep Λ) = Λ.1⁻¹ᵀ := by
  simp only [rep, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← LorentzGroup.coe_inv]
  exact (LinearEquiv.eq_symm_apply (LinearMap.toMatrix basis basis)).mp rfl

lemma rep_injective (d : ℕ) (Λ : LorentzGroup d) : Function.Injective (rep Λ) := by
  intro v1 v2 h
  rw [rep_apply_eq_mulVec, rep_apply_eq_mulVec] at h
  exact Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible _) h

lemma rep_surjective (d : ℕ) (Λ : LorentzGroup d) : Function.Surjective (rep Λ) := by
  intro v
  use (LorentzGroup.transpose Λ) *ᵥ v
  rw [rep_apply_eq_mulVec]
  simp [← LorentzGroup.transpose_inv, LorentzGroup.coe_inv]

lemma rep_bijective (d : ℕ) (Λ : LorentzGroup d) : Function.Bijective (rep Λ) :=
  ⟨rep_injective d Λ, rep_surjective d Λ⟩

/-!

## The representation of `SL(2,ℂ)`

-/

/-- The representation of `SL(2,ℂ)` on real Lorentz covectors, obtained from the
  representation of the Lorentz group through the covering map
  `SL(2,ℂ) →* LorentzGroup 3`. -/
noncomputable def sl2Rep : Representation ℝ SL(2,ℂ) Lorentz.CoVector :=
  MonoidHom.comp Lorentz.CoVector.rep Lorentz.SL2C.toLorentzGroup

/-- The dual of the covector representation on the dual basis: dual covectors
  transform contravariantly, by the columns of the Lorentz matrix. -/
lemma sl2Rep_dual_dualBasis (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    Lorentz.CoVector.sl2Rep.dual Λ (Lorentz.CoVector.basis.dualBasis μ) =
      ∑ j, (Lorentz.SL2C.toLorentzGroup Λ).1 j μ •
        Lorentz.CoVector.basis.dualBasis j := by
  refine Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (Lorentz.SL2C.toLorentzGroup Λ).1 j l) (fun j => ?_)
  rw [show Lorentz.CoVector.sl2Rep Λ⁻¹ =
      Lorentz.CoVector.rep (Lorentz.SL2C.toLorentzGroup Λ⁻¹) from rfl,
    Lorentz.CoVector.rep_apply_basis, ← LorentzGroup.coe_inv, map_inv, inv_inv]
  rfl

end CoVector

end Lorentz
