/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded
/-!
# The type corresponding to quark doublets

In this module we define the type corresponding to
the target vector space of a quark field in the Standard Model.

On this type we define a representation of the Lorentz group, and a
representation of the Standard Model gauge group.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

TODO "Add other fermions similar to this file with the names:
 - UpSinglet (3, 1)_{4} (right-handed)
 - LeptonSinglet (1, 1)_{-6} (right-handed)"

/-- The vector space of a quark field in the Standard Model.
  These live in the (3, 2)_{1} representation of the gauge group. -/
@[ext]
structure QuarkDoublet where
  /-- The underlying value of the quark field in the tensor product space. -/
  val : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)

namespace QuarkDoublet

/-!

## Equivalence with the underlying tensor product space

-/

/-- The linear equivalence between `QuarkDoublet` and its underlying tensor product space. -/
def valEquiv : QuarkDoublet ≃
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩

/-!

## The structure of a module

The AddCommGroup and module instances are inherited from the underlying tensor product space.
-/

instance : AddCommGroup QuarkDoublet := Equiv.addCommGroup valEquiv

instance : Module ℂ QuarkDoublet := AddEquiv.module ℂ { valEquiv with map_add' _ _ := rfl }

/-- The linear equivalence between `QuarkDoublet` and its underlying tensor product space. -/
def valLinEquiv : QuarkDoublet ≃ₗ[ℂ]
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (q : QuarkDoublet) : valLinEquiv q = q.val := rfl

lemma valLinEquiv_symm_apply
    (m : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (q1 q2 : QuarkDoublet) : (q1 + q2).val = q1.val + q2.val := rfl

@[simp]
lemma val_smul (r : ℂ) (q : QuarkDoublet) : (r • q).val = r • q.val := rfl

/-!

## Lorentz group representation

-/
open Matrix MatrixGroups

open Representation in
/-- The representation of the Lorentz group on the space of quark fields. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) QuarkDoublet where
  toFun Λ :=  valLinEquiv.symm ∘ₗ
      TensorProduct.map
      (TensorProduct.map (Fermion.LeftHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 3)) Λ))
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 2)) Λ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp [Module.End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    ext1 q
    simp [TensorProduct.map_map, ← TensorProduct.map_comp, Module.End.mul_eq_comp]

/-!

## The representation of the Standard Model gauge group

-/

/-- The action of the full Standard Model gauge group on quark fields. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI QuarkDoublet where
  toFun g := valLinEquiv.symm ∘ₗ
      TensorProduct.map
        (TensorProduct.map
        (LinearMap.id (M := Fermion.LeftHandedWeyl)) -- action on the Lorentz indices
        g.toSU3.1.toEuclideanLin) -- SU(3) action
        g.toSU2.1.toEuclideanLin  -- SU(2) action
      ∘ₗ LinearMap.lsmul ℂ _ (g.toU1 : ℂ) -- U(1) action
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp [valLinEquiv_symm_apply]
  map_mul' g1 g2 := by
    ext q
    simp [smul_smul, mul_comm, TensorProduct.map_map, ← TensorProduct.map_comp,
      valLinEquiv_symm_apply]

lemma repGaugeGroupI_tmul (g : GaugeGroupI) (ψ : Fermion.LeftHandedWeyl)
    (v : EuclideanSpace ℂ (Fin 3)) (w : EuclideanSpace ℂ (Fin 2)) :
    repGaugeGroupI g ⟨ψ ⊗ₜ v ⊗ₜ w⟩ = ⟨g.toU1 • ψ ⊗ₜ (g.toSU3.1.toEuclideanLin v) ⊗ₜ
      (g.toSU2.1.toEuclideanLin w)⟩ := rfl

open Fermion in
/-- The action of the full gauge group on a tensor product of basis elements, expanded as a
  sum over the columns of the `SU(3)` and `SU(2)` matrices. -/
lemma repGaugeGroupI_tmul_basis_eq_sum (g : GaugeGroupI) (k : Fin 2) (i : Fin 3) (j : Fin 2) :
    repGaugeGroupI g ⟨LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i
      ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩ =
      ∑ i' : Fin 3, ∑ j' : Fin 2, (g.toU1.1 * g.toSU3.1 i' i * g.toSU2.1 j' j)
      • (⟨LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i'
          ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j'⟩ : QuarkDoublet) := by
  apply valLinEquiv.injective
  apply (((LeftHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).repr.injective
  ext ⟨⟨k, l⟩, m⟩
  simp only [EuclideanSpace.basisFun_apply, repGaugeGroupI_tmul, Submonoid.smul_def,
    valLinEquiv_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, ofLp_toLpLin, PiLp.ofLp_single, toLin'_apply, mulVec_single,
    MulOpposite.op_one, col_apply, one_smul, Module.Basis.repr_self, smul_eq_mul, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply, PiLp.single_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero]
  ring

open Fermion in
lemma repGaugeGroupI_eq_iff_mul_eq {g1 g2 : GaugeGroupI} :
    repGaugeGroupI g1 = repGaugeGroupI g2 ↔ ∀ i i' j j',
    g1.toU1.1 * g1.toSU3.1 i' i * g1.toSU2.1 j' j =
    g2.toU1.1 * g2.toSU3.1 i' i * g2.toSU2.1 j' j := by
  let b := ((LeftHandedWeyl.basis).tensorProduct
      (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).tensorProduct
      (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  constructor
  · intro h i i' j j'
    have h' := congrFun (congrArg (fun f => f.1) h)
      ⟨LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i
      ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩
    simp only [Fin.isValue, LinearMap.coe_toAddHom, repGaugeGroupI_tmul_basis_eq_sum] at h'
    replace h' := congrArg b.repr (congrArg valLinEquiv h')
    simpa [Module.Basis.tensorProduct_repr_tmul_apply, -Fin.sum_univ_two, b] using
      congrArg (fun f => f ((0, i'), j')) h'
  · intro h
    apply (valLinEquiv.symm.eq_comp_toLinearMap_iff (repGaugeGroupI g1) (repGaugeGroupI g2)).mp
    apply b.ext
    rintro ⟨⟨i, j⟩, k⟩
    have h1 := repGaugeGroupI_tmul_basis_eq_sum g1 i j k
    have h2 := repGaugeGroupI_tmul_basis_eq_sum g2 i j k
    simp only [EuclideanSpace.basisFun_apply, Fin.sum_univ_two, Fin.isValue] at h1 h2
    simp [valLinEquiv_symm_apply, h1, h2, b, h]

TODO "Improve the efficiency of `mem_repGaugeGroupI_ker_iff_eq` by removing the
  `grind`s and replacing them with a more direct argument."

lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ ∃ a b : ℂ, g.toSU2.1 = a • 1 ∧ g.toSU3.1 = b • 1 ∧
      a * b * g.toU1.1 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff_mul_eq]
  constructor; swap
  · rintro ⟨a, b, h1, h2, h3⟩ i i' j j'
    simp only [h2, Matrix.smul_apply, smul_eq_mul, h1, map_one, OneMemClass.coe_one, one_mul]
    linear_combination h3 * (1 : Matrix _ _ ℂ) i' i * (1 : Matrix  _ _ ℂ) j' j
  · intro h
    use g.toSU2.1 0 0, g.toSU3.1 0 0
    simp only [map_one, OneMemClass.coe_one, one_mul, Fin.forall_fin_succ, Fin.isValue,
      Fin.succ_zero_eq_one, IsEmpty.forall_iff, and_true, one_apply_eq, mul_one, ne_eq, one_ne_zero,
      not_false_eq_true, one_apply_ne, mul_zero, mul_eq_zero, zero_ne_one, Fin.succ_one_eq_two,
      Fin.reduceEq] at h
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp <;> grind
    · ext i j
      fin_cases i <;> fin_cases j <;> simp <;> grind (splits := 20)
    · grind

lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [SetLike.le_def, mem_repGaugeGroupI_ker_iff_eq,
    GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, MonoidHom.mem_range,
    gaugeGroupℤ₆Hom_apply, Subtype.exists, exists_and_left, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  use starRingEnd ℂ (x ^ 3)
  simp only [gaugeGroupℤ₆OfRoot_toSU2, gaugeGroupℤ₆SU2OfRoot_eq_mul_id, RCLike.star_def,
    Complex.conj_rootsOfUnity hx, Units.val_inv_eq_inv_val, inv_pow, map_pow,
    gaugeGroupℤ₆OfRoot_toSU3, gaugeGroupℤ₆SU3OfRoot_eq_mul_id, ne_eq, one_ne_zero,
    not_false_eq_true, smul_left_inj, gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe,
    exists_eq_left', true_and]
  field_simp

lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The action of the Standard Model gauge group, potentially quotiented by
  a discrete factor on quark fields. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) QuarkDoublet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

end QuarkDoublet

end StandardModel
