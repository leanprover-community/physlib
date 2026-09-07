/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Relativity.Fermions.Weyl.BoostWeight
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.CovariantDeriv
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
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

instance : Module ℂ UpSinglet := Equiv.module ℂ valEquiv

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

## The basis of the up-singlet space

-/

/-- A basis on the up singlets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 3) ℂ UpSinglet :=
  (Fermion.RightHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).map valLinEquiv.symm

instance : Module.Finite ℂ UpSinglet := Module.Finite.of_basis basis

instance : Module.Free ℂ UpSinglet := Module.Free.of_basis basis

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

/-!

## The representation of the jet gauge group

-/

/-- Absorbs the jet ring into the colour index: a jet of an up-type singlet is the
same thing as a right-handed Weyl spinor tensored with a `JetRing`-valued colour
vector,

  `JetRing ⊗[ℂ] UpSinglet ≃ RightHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 3)`.

-/
noncomputable def jetValLinEquiv :
    JetRing ⊗[ℂ] UpSinglet ≃ₗ[ℂ]
      Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 3) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) valLinEquiv).trans <|
    (TensorProduct.leftComm ℂ JetRing Fermion.RightHandedWeyl
        (EuclideanSpace ℂ (Fin 3))).trans <|
      TensorProduct.congr (LinearEquiv.refl ℂ Fermion.RightHandedWeyl) <|
        (TensorProduct.congr (LinearEquiv.refl ℂ JetRing)
            (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ))).trans <|
          ((TensorProduct.piScalarRight ℂ JetRing JetRing (Fin 3)).trans
            (WithLp.linearEquiv 2 JetRing (Fin 3 → JetRing)).symm).restrictScalars ℂ

open Matrix in
/-- The `(3, 1)_{4}` action of the jet gauge group on the jet space of the up-type
singlet. Through `jetValLinEquiv` the colour matrix of the gauge jet, carrying the
`4` hypercharge phase `u ^ 4`, acts `JetRing`-linearly on the colour factor by
matrix-vector multiplication, while the Weyl factor is untouched. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] UpSinglet) where
  toFun U :=
    jetValLinEquiv.symm.toLinearMap ∘ₗ
      Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3)) Fermion.RightHandedWeyl
        ((Matrix.toLpLinAlgEquiv 2
            ((((U.2.2 : unitary JetRing) : JetRing)) ^ 4 •
              ((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
                Matrix (Fin 3) (Fin 3) JetRing))).restrictScalars ℂ) ∘ₗ
      jetValLinEquiv.toLinearMap
  map_one' := by
    have hres : (1 : Module.End JetRing (EuclideanSpace JetRing (Fin 3))).restrictScalars ℂ
        = 1 := rfl
    rw [show ((((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) ^ 4 •
          (((1 : JetGaugeGroupI).1 : specialUnitaryGroup (Fin 3) JetRing) :
            Matrix (Fin 3) (Fin 3) JetRing)) = 1 from by simp,
      map_one, hres, map_one]
    ext d x
    simp [-valLinEquiv_apply]
  map_mul' U₁ U₂ := by
    have hres : ∀ f g : Module.End JetRing (EuclideanSpace JetRing (Fin 3)),
        (f * g).restrictScalars ℂ = f.restrictScalars ℂ * g.restrictScalars ℂ :=
      fun _ _ => rfl
    have hM : ((((U₁ * U₂).2.2 : unitary JetRing) : JetRing) ^ 4 •
          (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) JetRing) :
            Matrix (Fin 3) (Fin 3) JetRing)) =
        (((U₁.2.2 : unitary JetRing) : JetRing) ^ 4 •
            ((U₁.1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing)) *
          (((U₂.2.2 : unitary JetRing) : JetRing) ^ 4 •
            ((U₂.1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing)) := by
      rw [show (((U₁ * U₂).2.2 : unitary JetRing) : JetRing) =
            ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
            from rfl,
        show (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing) =
            ((U₁.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) *
              ((U₂.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing)
            from rfl,
        mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hM, map_mul, hres, map_mul]
    ext d x
    simp

/-- The identification of the jets of the up-type singlet intertwines multiplication by
a scalar jet with the `JetRing`-scalar action on the colour coordinates. -/
lemma jetValLinEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] UpSinglet) :
    jetValLinEquiv (χ • z)
      = Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
          Fermion.RightHandedWeyl
          ((LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ).restrictScalars ℂ)
          (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, map_add]
  | tmul f x =>
    obtain ⟨v⟩ := x
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : UpSinglet) = 0 from rfl, TensorProduct.tmul_zero,
        smul_zero, map_zero, map_zero]
    | tmul ψ c =>
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        show jetValLinEquiv ((χ * f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : UpSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (χ * f)) from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : UpSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        show Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
            Fermion.RightHandedWeyl
            ((LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ).restrictScalars ℂ)
            (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f))
          = ψ ⊗ₜ[ℂ] (χ • WithLp.toLp 2 fun i => c.ofLp i • f) from rfl]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      show c.ofLp i • (χ * f) = χ * (c.ofLp i • f)
      rw [Algebra.mul_smul_comm]
    | add a b ha hb =>
      rw [show ({ val := a + b } : UpSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]

/-- **The jet gauge action on the jets of the up-type singlet is fibrewise**: it commutes
with multiplication by scalar jets. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] UpSinglet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  set S : Module.End JetRing (EuclideanSpace JetRing (Fin 3)) :=
    LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ with hS
  set M : Module.End JetRing (EuclideanSpace JetRing (Fin 3)) :=
    (Matrix.toLpLinAlgEquiv 2
      ((((U.2.2 : unitary JetRing) : JetRing)) ^ 4 •
        ((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
          Matrix (Fin 3) (Fin 3) JetRing)) :
      Module.End JetRing (EuclideanSpace JetRing (Fin 3))) with hM
  have hMS : M * S = S * M := LinearMap.ext fun e => by
    simp only [Module.End.mul_apply, hS, LinearMap.lsmul_apply, map_smul]
  apply jetValLinEquiv.injective
  rw [show repJetGaugeGroupI U (χ • z)
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.RightHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv (χ • z))) from rfl,
    LinearEquiv.apply_symm_apply, jetValLinEquiv_smul,
    show repJetGaugeGroupI U z
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.RightHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv z)) from rfl,
    jetValLinEquiv_smul, LinearEquiv.apply_symm_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    show M.restrictScalars ℂ * S.restrictScalars ℂ = (M * S).restrictScalars ℂ from rfl,
    show S.restrictScalars ℂ * M.restrictScalars ℂ = (S * M).restrictScalars ℂ from rfl,
    hMS]

/-- On jets of constant gauge transformations the jet action reduces to the global
gauge action on the fibre: the `(3, 1)_{4}` action on the up-singlet factor, and the
trivial action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext d x
  obtain ⟨v⟩ := x
  induction v using TensorProduct.induction_on with
  | zero => simp [show ({ val := 0 } : UpSinglet) = 0 from rfl]
  | tmul psi c =>
      apply jetValLinEquiv.injective
      simp [repJetGaugeGroupI, jetValLinEquiv, repGaugeGroupI]
      have hu : (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
          = MvPowerSeries.C ((g.toU1.1 : ℂ)) := rfl
      have hM : ∀ i j, (((JetGaugeGroupI.ofConstant g).1 :
            specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) i j
          = MvPowerSeries.C (g.toSU3.1 i j) := fun _ _ => rfl
      have halg : ∀ A : Matrix (Fin 3) (Fin 3) JetRing,
          (Matrix.toLpLinAlgEquiv 2 A :
              Module.End JetRing (EuclideanSpace JetRing (Fin 3)))
            = Matrix.toLpLin 2 2 A := fun _ => rfl
      have hvec : ∀ i : Fin 3,
          (∑ x, MvPowerSeries.C ((g.toSU3.1) i x) * (MvPowerSeries.C (c.ofLp x) * d))
            = MvPowerSeries.C (∑ x, (g.toSU3.1) i x * c.ofLp x) * d := by
        intro i
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ← map_mul]
      rw [TensorProduct.liftAux_tmul, ← TensorProduct.tmul_smul]
      simp only [LinearMap.compl₂_apply, TensorProduct.mk_apply, LinearMap.smul_apply,
        LinearMap.restrictScalars_apply, halg, Matrix.toLpLin_toLp]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      simp only [WithLp.ofLp_smul, Pi.smul_apply, Matrix.toLin'_apply,
        Matrix.mulVec_apply_eq_sum, hM, Algebra.smul_def, MvPowerSeries.algebraMap_apply,
        hu, map_pow, Algebra.algebraMap_self_apply]
      rw [hvec i]
  | add a b ha hb =>
      simp only [show ({ val := a + b } : UpSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        map_add, ha, hb]

/-!

## Component transformation laws

The basis of `UpSinglet` splits as a right-handed Weyl index and a colour index. The
Lorentz group moves only the first, the gauge group only the second (up to the hypercharge
scalar), so both actions are recorded as a single sum over the index they move. Dualising
inverts and transposes the coefficient matrix, and conjugating stars it; the four
combinations below are what a component of an up-singlet symbol needs.

-/

/-- The up-singlet basis vector as an explicit spinor–colour tensor. -/
lemma basis_eq_mk (k : Fin 2) (c : Fin 3) : basis (k, c) =
    ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    OrthonormalBasis.coe_toBasis]
  rfl

/-- The Lorentz action on the up-singlet basis: the colour index is inert and the
  spinor index transforms by the entrywise conjugate matrix. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup Λ (basis j) = ∑ β, star (Λ.1 β j.1) • basis (β, j.2) := by
  obtain ⟨k, c⟩ := j
  simp only [basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    repLorentzGroup, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply,
    TensorProduct.map_tmul, Fermion.RightHandedWeyl.rep_apply_basis,
    Representation.trivial_apply, TensorProduct.sum_tmul, map_sum,
    Matrix.map_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul]

/-- The up-singlet coordinate functionals transform contragrediently, by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.dual Λ (basis.dualBasis j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • basis.dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup basis Λ j
    (Matrix.of fun p q => if p.2 = q.2 then star ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The Lorentz action on the conjugate up-singlet basis: the coefficients are the
  conjugates of those of the up-singlet action, that is, the matrix itself. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.conj Λ (basis.conj j) = ∑ β, Λ.1 β j.1 • basis.conj (β, j.2) := by
  rw [Representation.conj_apply, Module.Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_star, Module.Basis.conj_apply]

/-- The conjugate up-singlet coordinate functionals transform by the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.conj.dual Λ (basis.conj.dualBasis j) =
      ∑ β, (Λ⁻¹).1 j.1 β • basis.conj.dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup.conj basis.conj Λ j
    (Matrix.of fun p q => if p.2 = q.2 then ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the up-singlet basis: the spinor index is inert and the colour
  index transforms by the `SU(3)` matrix, scaled by the hypercharge factor. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI g (basis j) =
      ∑ c, (g.toU1.1 ^ 4 * g.toSU3.1 c j.2) • basis (j.1, c) := by
  obtain ⟨k, c⟩ := j
  simp only [basis_eq_mk]
  exact repGaugeGroupI_tmul_basis_eq_sum g k c

/-- The up-singlet coordinate functionals carry the contragredient gauge action: the
  hypercharge and `SU(3)` factors of the inverse group element, transposed. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.dual g (basis.dualBasis j) =
      ∑ c, ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 j.2 c) • basis.dualBasis (j.1, c) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then (g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 p.2 q.2 else 0)
    (fun q => by
      rw [repGaugeGroupI_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the conjugate up-singlet basis: the coefficients of the
  up-singlet action, conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.conj g (basis.conj j) =
      ∑ c, star (g.toU1.1 ^ 4 * g.toSU3.1 c j.2) • basis.conj (j.1, c) := by
  rw [Representation.conj_apply, Module.Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Module.Basis.conj_apply]

/-- The conjugate up-singlet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.conj.dual g (basis.conj.dualBasis j) =
      ∑ c, star ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 j.2 c) •
        basis.conj.dualBasis (j.1, c) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj basis.conj g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star ((g⁻¹).toU1.1 ^ 4 * (g⁻¹).toSU3.1 p.2 q.2) else 0)
    (fun q => by
      rw [repGaugeGroupI_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

end UpSinglet

/-!

## The gauge weight of the UpSinglet components

The gauge torus acts diagonally on the basis of `UpSinglet`; the weights are recorded by
`UpSinglet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the up-singlet basis: the colour weights and hypercharge
  `4`. -/
def UpSinglet.valueGaugeWeight (j : Fin 2 × Fin 3) : GaugeWeight :=
  ((colourWeight j.2).1, (colourWeight j.2).2, 0, 4)

/-- The gauge torus acts diagonally on the basis of `UpSinglet`, with the weights
  `UpSinglet.valueGaugeWeight`. -/
lemma UpSinglet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI (gaugeTorusGen i) (UpSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) •
        UpSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  have hb : UpSinglet.basis (k, c)
      = ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
    simp only [UpSinglet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
      OrthonormalBasis.coe_toBasis]
    rfl
  rw [hb, UpSinglet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo,
      Fin.sum_univ_three,
      Matrix.diagonal,
      UpSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star] <;>
  (try congr 1)

/-- The dual action of the gauge torus on the coordinate functionals of
  `UpSinglet`: the weights are negated. -/
lemma UpSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (UpSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i))) •
        UpSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => UpSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `UpSinglet`: the two negations cancel and the weights are those of
  the value space. -/
lemma UpSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((UpSinglet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) •
        (UpSinglet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord UpSinglet.repGaugeGroupI.conj (UpSinglet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (UpSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => UpSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-!

## The boost weight of the UpSinglet components

-/

open Lorentz in
/-- The up-singlet basis diagonalises the `z`-boost. -/
lemma upSinglet_repLorentzGroup_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0)
    (j : Fin 2 × Fin 3) :
    UpSinglet.repLorentzGroup (SL2C.boostAxis 2 t ht) (UpSinglet.basis j)
      = ((t : ℝ) : ℂ) ^ (weylWeight j.1) • UpSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  simp [UpSinglet.basis, UpSinglet.repLorentzGroup, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply, rightHandedWeyl_rep_boostAxis_two_basis]
  rw [← TensorProduct.smul_tmul', map_smul]

end StandardModel
