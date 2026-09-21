/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!
# Up-type singlets

In this module we define the type corresponding to
the target vector space of an up-type singlet quark field in the Standard Model.

On this type we define a representation of the Lorentz group, and a
representation of the Standard Model gauge group.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-- The vector space of an up-type singlet quark field in the Standard Model.
  These live in the (3, 1)_{4} representation of the gauge group. -/
@[ext]
structure UpSinglet where
  /-- The underlying value of the up-type quark field in the tensor product space. -/
  val : Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3)

namespace UpSinglet

/-!

## Equivalence with the underlying tensor product space

-/

/-- The linear equivalence between `UpSinglet` and its underlying tensor product space. -/
def valEquiv : UpSinglet ≃ Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun := val
  invFun := fun m => ⟨m⟩

/-!

## The structure of a module

The AddCommGroup and module instances are inherited from the underlying tensor product space.
-/

instance : AddCommGroup UpSinglet := Equiv.addCommGroup valEquiv

instance : Module ℂ UpSinglet := AddEquiv.module ℂ { valEquiv with map_add' _ _ := rfl }

/-- The linear equivalence between `UpSinglet` and its underlying tensor product space. -/
def valLinEquiv : UpSinglet ≃ₗ[ℂ]
    Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (q : UpSinglet) : valLinEquiv q = q.val := rfl

lemma valLinEquiv_symm_apply (m : Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (q1 q2 : UpSinglet) : (q1 + q2).val = q1.val + q2.val := rfl

@[simp]
lemma val_smul (r : ℂ) (q : UpSinglet) : (r • q).val = r • q.val := rfl

/-!

## Lorentz group representation

-/
open Matrix MatrixGroups

open Representation in
/-- The representation of the Lorentz group on the space of up-type quark fields. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) UpSinglet where
  toFun Λ :=  valLinEquiv.symm ∘ₗ
      (TensorProduct.map (Fermion.RightHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 3)) Λ))
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp [Module.End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    ext1 q
    simp [TensorProduct.map_map, Module.End.mul_eq_comp]

/-!

## The representation of the Standard Model gauge group

-/

/-- The action of the full Standard Model gauge group on up-type quark fields. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI UpSinglet where
  toFun g := valLinEquiv.symm ∘ₗ
        (TensorProduct.map
        (LinearMap.id (M := Fermion.RightHandedWeyl)) -- action on the Lorentz indices
        g.toSU3.1.toEuclideanLin) -- SU(3) action
      ∘ₗ LinearMap.lsmul ℂ _ (g.toU1.1 ^ 4 : ℂ) -- U(1) action
      ∘ₗ valLinEquiv
  map_one' := by
    ext q
    simp [valLinEquiv_symm_apply]
  map_mul' g1 g2 := by
    ext q
    simp [smul_smul, mul_comm, TensorProduct.map_map, valLinEquiv_symm_apply]
    ring_nf

lemma repGaugeGroupI_tmul (g : GaugeGroupI) (ψ : Fermion.RightHandedWeyl)
    (v : EuclideanSpace ℂ (Fin 3)) :
    repGaugeGroupI g ⟨ψ ⊗ₜ v⟩ = ⟨g.toU1 ^ 4 • ψ ⊗ₜ (g.toSU3.1.toEuclideanLin v)⟩ := rfl

open Fermion in
/-- The action of the full gauge group on a tensor product of basis elements, expanded as a
  sum over the columns of the `SU(3)` matrix. -/
lemma repGaugeGroupI_tmul_basis_eq_sum (g : GaugeGroupI) (k : Fin 2) (i : Fin 3) :
    repGaugeGroupI g ⟨RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i⟩ =
      ∑ i' : Fin 3, (g.toU1.1 ^ 4  * g.toSU3.1 i' i)
      • (⟨RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i'⟩ : UpSinglet) := by
  apply valLinEquiv.injective
  apply (((RightHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis)).repr.injective
  ext ⟨⟨k, l⟩, m⟩
  simp only [EuclideanSpace.basisFun_apply, repGaugeGroupI_tmul, Submonoid.smul_def,
    SubmonoidClass.coe_pow, valLinEquiv_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, ofLp_toLpLin, PiLp.ofLp_single, toLin'_apply, mulVec_single,
    MulOpposite.op_one, col_apply, one_smul, Module.Basis.repr_self, smul_eq_mul, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply, PiLp.single_apply, ite_mul, one_mul, zero_mul, mul_ite,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

open Fermion in
lemma repGaugeGroupI_eq_iff_mul_eq {g1 g2 : GaugeGroupI} :
    repGaugeGroupI g1 = repGaugeGroupI g2 ↔ ∀ i i',
    g1.toU1.1 ^ 4 * g1.toSU3.1 i' i = g2.toU1.1 ^ 4 * g2.toSU3.1 i' i := by
  let b := (RightHandedWeyl.basis).tensorProduct (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis
  constructor
  · intro h i i'
    have h' := congrFun (congrArg (fun f => f.1) h)
      ⟨RightHandedWeyl.basis 0 ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i⟩
    simp only [Fin.isValue, LinearMap.coe_toAddHom, repGaugeGroupI_tmul_basis_eq_sum] at h'
    replace h' := congrArg b.repr (congrArg valLinEquiv h')
    simpa [Module.Basis.tensorProduct_repr_tmul_apply, -Fin.sum_univ_two, b] using
      congrArg (fun f => f (0, i')) h'
  · intro h
    apply (valLinEquiv.symm.eq_comp_toLinearMap_iff (repGaugeGroupI g1) (repGaugeGroupI g2)).mp
    apply b.ext
    rintro ⟨i, k⟩
    have h1 := repGaugeGroupI_tmul_basis_eq_sum g1 i k
    have h2 := repGaugeGroupI_tmul_basis_eq_sum g2 i k
    simp only [EuclideanSpace.basisFun_apply] at h1 h2
    simp [valLinEquiv_symm_apply, h1, h2, b, h]

lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ ∃ a : ℂ, g.toSU3.1 = a • 1 ∧  a * g.toU1.1 ^ 4 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff_mul_eq]
  constructor; swap
  · rintro ⟨a, h1, h2⟩ i i'
    simp only [Matrix.smul_apply, smul_eq_mul, h1, map_one, OneMemClass.coe_one]
    linear_combination h2 * (1 : Matrix _ _ ℂ) i' i
  · intro h
    use g.toSU3.1 0 0
    simp only [map_one, OneMemClass.coe_one, Fin.forall_fin_succ, Fin.isValue,
      Fin.succ_zero_eq_one, IsEmpty.forall_iff, and_true, one_apply_eq, mul_one, ne_eq, one_ne_zero,
      not_false_eq_true, one_apply_ne, mul_zero, mul_eq_zero, zero_ne_one, Fin.succ_one_eq_two,
      Fin.reduceEq] at h
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp <;> grind
    · grind

lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, SetLike.le_def, MonoidHom.mem_range,
    gaugeGroupℤ₆Hom_apply, Subtype.exists, mem_repGaugeGroupI_ker_iff_eq, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  use  (x ^ 2)
  simp only [gaugeGroupℤ₆OfRoot_toSU3, gaugeGroupℤ₆SU3OfRoot_eq_mul_id, gaugeGroupℤ₆OfRoot_toU1,
    gaugeGroupℤ₆UnitaryOfRoot_coe, true_and]
  field_simp
  exact (mem_rootsOfUnity' 6 x).mp hx

lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The action of the Standard Model gauge group, potentially quotiented by
  a discrete factor on quark fields. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) UpSinglet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

end UpSinglet

end StandardModel
