/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.DownSinglet
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Basic
public import PhyslibAlpha.Relativity.Fermions.Weyl.BoostWeight
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GaugeWeight
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.JetGaugeGroup.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponent.GaugeAction
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGauge.GaugeAction
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# Down-type singlets

## i. Overview

The Standard Model down-type singlet is a right-handed Weyl spinor in the `(3, 1)_{-2}`
representation. Here charges are normalized as `6Y`, so `-2` is the usual hypercharge
`Y = -1/3`.

`DownSinglet` is the target vector space of one down-type quark multiplet. Its Weyl factor
carries the Lorentz index and its three-dimensional factor carries the colour index. The absence
of a weak factor makes it an `SU(2)` singlet.

The Lorentz and gauge actions are first defined separately. The gauge action is then computed on a
basis, used to identify its kernel, and descended to each supported global form of the Standard
Model gauge group.

## ii. Key results

- `DownSinglet` : the target space of the `(3, 1)_{-2}` multiplet.
- `repLorentzGroup` : the right-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_tmul_basis_eq_sum` : the gauge action in a tensor-product basis.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.
- `gaugeAlgebraAction` : the infinitesimal `(3, 1)_{-2}` action of the gauge algebra.
- `repJetGaugeGroupI` : the jet gauge action on jets of the down singlet.
- `isInfinitesimalActionOf` : the gauge-algebra action is the infinitesimal action
  underlying the jet gauge action.

## iii. Table of contents

- A. The down-singlet space
- B. Linear structure
- C. The basis of the down-singlet space
- D. Lorentz action
- E. Gauge action
- F. Kernel of the gauge action
- G. Descent to quotient gauge groups
- H. The representation of the jet gauge group
- I. Component transformation laws
- J. The gauge weight of the DownSinglet components
- K. The boost weight of the DownSinglet components

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The down-singlet space

The Weyl factor carries the right-handed Lorentz index, while
`EuclideanSpace ℂ (Fin 3)` carries the colour index.
-/

namespace DownSinglet

/-!

## B. Linear structure

`DownSinglet` wraps its tensor-product carrier as a distinct type. The equivalences below identify
the two types and transport the additive and complex module structures to `DownSinglet`.
-/

/-!

## C. The basis of the down-singlet space

-/

/-- A basis on the down singlets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 3) ℂ DownSinglet :=
  (Fermion.RightHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).map valLinEquiv.symm

instance : Module.Finite ℂ DownSinglet := Module.Finite.of_basis basis

instance : Module.Free ℂ DownSinglet := Module.Free.of_basis basis

/-!

## D. Lorentz action

The Lorentz group acts on the right-handed Weyl factor and leaves the colour index fixed.
-/

open Matrix MatrixGroups

/-!

## E. Gauge action

The `SU(3)` component acts on the colour index, while the `SU(2)` component acts trivially. The
`U(1)` action is `star z ^ 2`; since `z` is unitary, `star z = z⁻¹`, so this represents charge
`-2`.

The tensor and basis formulas below expose the coefficients used to compare actions and compute the
kernel.
-/

/-!

## F. Kernel of the gauge action

An element acts trivially when its colour action is scalar and that scalar cancels its `U(1)`
phase. Its weak component is unrestricted because the down-type singlet is an `SU(2)` singlet.
-/

/-!

## G. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its kernel. For
the central `ℤ₆`, the colour phase is `x²` while the charge `-2` phase is `(star x)² = x⁻²`, so
their product is one.
-/

/-!

## H. The representation of the jet gauge group
-/

/-- Absorbs the jet ring into the colour index: a jet of a down-type singlet is the
same thing as a right-handed Weyl spinor tensored with a `SpaceTimeAlgebra`-valued colour
vector,

  `SpaceTimeAlgebra ⊗[ℂ] DownSinglet ≃
    RightHandedWeyl ⊗[ℂ] EuclideanSpace SpaceTimeAlgebra (Fin 3)`.

-/
noncomputable def jetValLinEquiv :
    SpaceTimeAlgebra ⊗[ℂ] DownSinglet ≃ₗ[ℂ]
      Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace SpaceTimeAlgebra (Fin 3) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ SpaceTimeAlgebra) valLinEquiv).trans <|
    (TensorProduct.leftComm ℂ SpaceTimeAlgebra Fermion.RightHandedWeyl
        (EuclideanSpace ℂ (Fin 3))).trans <|
      TensorProduct.congr (LinearEquiv.refl ℂ Fermion.RightHandedWeyl) <|
        (TensorProduct.congr (LinearEquiv.refl ℂ SpaceTimeAlgebra)
            (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ))).trans <|
          ((TensorProduct.piScalarRight ℂ SpaceTimeAlgebra SpaceTimeAlgebra (Fin 3)).trans
            (WithLp.linearEquiv 2 SpaceTimeAlgebra
                (Fin 3 → SpaceTimeAlgebra)).symm).restrictScalars ℂ

/-- The `(3, 1)_{-2}` action of the jet gauge group on the jet space of the down-type
singlet. Through `jetValLinEquiv` the colour matrix of the gauge jet, carrying the
`-2` hypercharge phase `(star u) ^ 2`, acts `SpaceTimeAlgebra`-linearly on the colour factor by
matrix-vector multiplication, while the Weyl factor is untouched.

Both monoid laws come from bundled algebra maps — `Matrix.toLpLinAlgEquiv` and
`Module.End.lTensorAlgHom` are morphisms of algebras — so only the multiplicativity of
the colour-times-hypercharge matrix itself is checked. Note `Matrix.toLpLinAlgEquiv 2`
is the same map as the `Matrix.toEuclideanLin` used by `repGaugeGroupI`, which is an
abbreviation for `Matrix.toLpLin 2 2`, taken at the `CommRing` generality that
`SpaceTimeAlgebra` needs. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (SpaceTimeAlgebra ⊗[ℂ] DownSinglet) where
  toFun U :=
    jetValLinEquiv.symm.toLinearMap ∘ₗ
      Module.End.lTensorAlgHom ℂ (EuclideanSpace SpaceTimeAlgebra (Fin 3)) Fermion.RightHandedWeyl
        ((Matrix.toLpLinAlgEquiv 2
            (((star ((U.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 2) •
              ((U.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
                Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra))).restrictScalars ℂ) ∘ₗ
      jetValLinEquiv.toLinearMap
  map_one' := by
    have hres :
        (1 : Module.End SpaceTimeAlgebra
        (EuclideanSpace SpaceTimeAlgebra (Fin 3))).restrictScalars ℂ
        = 1 := rfl
    rw [show (((star
        (((1 : JetGaugeGroupI).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 2) •
          (((1 : JetGaugeGroupI).1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
            Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra)) = 1 from by simp,
      map_one, hres, map_one]
    ext d x
    simp [-valLinEquiv_apply]
  map_mul' U₁ U₂ := by
    have hres : ∀ f g : Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3)),
        (f * g).restrictScalars ℂ = f.restrictScalars ℂ * g.restrictScalars ℂ :=
      fun _ _ => rfl
    have hM : (((star (((U₁ * U₂).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 2) •
          (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
            Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra)) =
        (((star ((U₁.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 2) •
            ((U₁.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
              Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra)) *
          (((star ((U₂.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 2) •
            ((U₂.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
              Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra)) := by
      rw [show (((U₁ * U₂).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) =
            ((U₁.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) *
                ((U₂.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)
            from rfl,
        show (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
              Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra) =
            ((U₁.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) : Matrix (Fin 3)
                (Fin 3) SpaceTimeAlgebra) *
              ((U₂.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) : Matrix (Fin 3)
                  (Fin 3) SpaceTimeAlgebra)
            from rfl,
        star_mul', mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hM, map_mul, hres, map_mul]
    ext d x
    simp

/-- The identification of the jets of the down-type singlet intertwines multiplication by
a scalar jet with the `SpaceTimeAlgebra`-scalar action on the colour coordinates. -/
lemma jetValLinEquiv_smul (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] DownSinglet) :
    jetValLinEquiv (χ • z)
      = Module.End.lTensorAlgHom ℂ (EuclideanSpace SpaceTimeAlgebra (Fin 3))
          Fermion.RightHandedWeyl
          ((LinearMap.lsmul SpaceTimeAlgebra
              (EuclideanSpace SpaceTimeAlgebra (Fin 3)) χ).restrictScalars ℂ)
          (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, map_add]
  | tmul f x =>
    obtain ⟨v⟩ := x
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero,
        smul_zero, map_zero, map_zero]
    | tmul ψ c =>
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        show jetValLinEquiv ((χ * f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (χ * f)) from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        show Module.End.lTensorAlgHom ℂ (EuclideanSpace SpaceTimeAlgebra (Fin 3))
            Fermion.RightHandedWeyl
            ((LinearMap.lsmul SpaceTimeAlgebra
                (EuclideanSpace SpaceTimeAlgebra (Fin 3)) χ).restrictScalars ℂ)
            (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f))
          = ψ ⊗ₜ[ℂ] (χ • WithLp.toLp 2 fun i => c.ofLp i • f) from rfl]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      show c.ofLp i • (χ * f) = χ * (c.ofLp i • f)
      rw [Algebra.mul_smul_comm]
    | add a b ha hb =>
      rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]

/-- **The jet gauge action on the jets of the down-type singlet is fibrewise**: it
commutes with multiplication by scalar jets, acting on the values of the field over the
identity on spacetime. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : SpaceTimeAlgebra)
    (z : SpaceTimeAlgebra ⊗[ℂ] DownSinglet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  set S : Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3)) :=
    LinearMap.lsmul SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3)) χ with hS
  set M : Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3)) :=
    (Matrix.toLpLinAlgEquiv 2
      (((star ((U.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)) ^ 2) •
        ((U.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
          Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra)) :
      Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3))) with hM
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
gauge action on the fibre: the `(3, 1)_{-2}` action on the down-singlet factor, and the
trivial action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext d x
  obtain ⟨v⟩ := x
  induction v using TensorProduct.induction_on with
  | zero => simp [show ({ val := 0 } : DownSinglet) = 0 from rfl]
  | tmul psi c =>
      apply jetValLinEquiv.injective
      simp [repJetGaugeGroupI, jetValLinEquiv, repGaugeGroupI, -TensorProduct.congr_symm]
      have hu : star
          (((JetGaugeGroupI.ofConstant g).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)
          = MvPowerSeries.C ((starRingEnd ℂ) (g.toU1.1 : ℂ)) := by
        rw [show (((JetGaugeGroupI.ofConstant g).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra)
          = MvPowerSeries.C ((g.toU1.1 : ℂ)) from rfl, SpaceTimeAlgebra.star_C]
        rfl
      have hM : ∀ i j, (((JetGaugeGroupI.ofConstant g).1 :
            specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) : Matrix (Fin 3)
                (Fin 3) SpaceTimeAlgebra) i j
          = MvPowerSeries.C (g.toSU3.1 i j) := fun _ _ => rfl
      have halg : ∀ A : Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra,
          (Matrix.toLpLinAlgEquiv 2 A :
              Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3)))
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
      simp only [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        map_add, ha, hb]

/-!

## I. Component transformation laws

The basis of `DownSinglet` splits as a right-handed Weyl index and a colour index. The
Lorentz group moves only the first, the gauge group only the second (up to the hypercharge
scalar), so both actions are recorded as a single sum over the index they move. Dualising
inverts and transposes the coefficient matrix, and conjugating stars it; the four
combinations below are what a component of a down-singlet symbol needs.

-/

/-- The down-singlet basis vector as an explicit spinor–colour tensor. -/
lemma basis_eq_mk (k : Fin 2) (c : Fin 3) : basis (k, c) =
    ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
  simp only [basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    OrthonormalBasis.coe_toBasis]
  rfl

/-- The Lorentz action on the down-singlet basis: the colour index is inert and the
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

/-- The down-singlet coordinate functionals transform contragrediently, by the entrywise
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

/-- The Lorentz action on the conjugate down-singlet basis: the coefficients are the
  conjugates of those of the down-singlet action, that is, the matrix itself. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.conj Λ ((Basis.conj basis) j)
      = ∑ β, Λ.1 β j.1 • (Basis.conj basis) (β, j.2) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, star_star, Basis.conj_apply]

/-- The conjugate down-singlet coordinate functionals transform by the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3) :
    repLorentzGroup.conj.dual Λ ((Basis.conj basis).dualBasis j) =
      ∑ β, (Λ⁻¹).1 j.1 β • (Basis.conj basis).dualBasis (β, j.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup.conj (Basis.conj basis) Λ j
    (Matrix.of fun p q => if p.2 = q.2 then ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- **The centre of `SL(2,ℂ)` acts on the down-singlet space by `-1`**: the value space carries a
  single Weyl-spinor index, and `-1` is not the identity on a half-integer spin. -/
lemma repLorentzGroup_neg_one : repLorentzGroup (-1) = -LinearMap.id := by
  apply basis.ext
  intro j
  obtain ⟨a, c⟩ := j
  rw [repLorentzGroup_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply, Module.Basis.tensorProduct_apply]

/-- The centre acts on the conjugate down-singlet space by `-1` as well: conjugation does not
  move a real sign. -/
lemma repLorentzGroup_conj_neg_one : repLorentzGroup.conj (-1) = -LinearMap.id := by
  apply (Basis.conj basis).ext
  intro j
  obtain ⟨a, c⟩ := j
  rw [repLorentzGroup_conj_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply, Module.Basis.tensorProduct_apply]

/-- The gauge action on the down-singlet basis: the spinor index is inert and the colour
  index transforms by the `SU(3)` matrix, scaled by the hypercharge factor. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI g (basis j) =
      ∑ c, (star g.toU1.1 ^ 2 * g.toSU3.1 c j.2) • basis (j.1, c) := by
  obtain ⟨k, c⟩ := j
  simp only [basis_eq_mk]
  exact repGaugeGroupI_tmul_basis_eq_sum g k c

/-- The down-singlet coordinate functionals carry the contragredient gauge action: the
  hypercharge and `SU(3)` factors of the inverse group element, transposed. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.dual g (basis.dualBasis j) =
      ∑ c, (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 j.2 c) • basis.dualBasis (j.1, c) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 p.2 q.2 else 0)
    (fun q => by
      rw [repGaugeGroupI_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the conjugate down-singlet basis: the coefficients of the
  down-singlet action, conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.conj g ((Basis.conj basis) j) =
      ∑ c, star (star g.toU1.1 ^ 2 * g.toSU3.1 c j.2) • (Basis.conj basis) (j.1, c) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Basis.conj_apply]

/-- The conjugate down-singlet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3) :
    repGaugeGroupI.conj.dual g ((Basis.conj basis).dualBasis j) =
      ∑ c, star (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 j.2 c) •
        (Basis.conj basis).dualBasis (j.1, c) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj (Basis.conj basis) g j
    (Matrix.of fun p q =>
      if p.1 = q.1 then star (star (g⁻¹).toU1.1 ^ 2 * (g⁻¹).toSU3.1 p.2 q.2) else 0)
    (fun q => by
      rw [repGaugeGroupI_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

end DownSinglet

/-!

## J. The gauge weight of the DownSinglet components

The gauge torus acts diagonally on the basis of `DownSinglet`; the weights are recorded by
`DownSinglet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the down-singlet basis: the colour weights and hypercharge
  `-2`. -/
def DownSinglet.valueGaugeWeight (j : Fin 2 × Fin 3) : GaugeWeight :=
  ((colourWeight j.2).1, (colourWeight j.2).2, 0, -2)

/-- The gauge torus acts diagonally on the basis of `DownSinglet`, with the weights
  `DownSinglet.valueGaugeWeight`. -/
lemma DownSinglet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI (gaugeTorusGen i) (DownSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) •
        DownSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  have hb : DownSinglet.basis (k, c)
      = ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
    simp only [DownSinglet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
      OrthonormalBasis.coe_toBasis]
    rfl
  rw [hb, DownSinglet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo,
      Fin.sum_univ_three,
      Matrix.diagonal,
      DownSinglet.valueGaugeWeight, colourWeight, GaugeWeight.coord,
      expI_inv_eq_star, starRingEnd_expI_pow] <;>
  (try congr 1)

/-- The dual action of the gauge torus on the coordinate functionals of
  `DownSinglet`: the weights are negated. -/
lemma DownSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (DownSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i))) •
        DownSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => DownSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `DownSinglet`: the two negations cancel and the weights are those of
  the value space. -/
lemma DownSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i)
      (((Basis.conj DownSinglet.basis)).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) •
        ((Basis.conj DownSinglet.basis)).coord j := by
  have hd := dual_gaugeTorusGen_coord DownSinglet.repGaugeGroupI.conj
    ((Basis.conj DownSinglet.basis))
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (DownSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => DownSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-!

## K. The boost weight of the DownSinglet components

-/

open Lorentz in
/-- The down-singlet basis diagonalises the `z`-boost: the colour index is inert, so the
  weight is the Weyl weight of the spinor index. -/
lemma downSinglet_repLorentzGroup_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0)
    (j : Fin 2 × Fin 3) :
    DownSinglet.repLorentzGroup (SL2C.boostAxis 2 t ht) (DownSinglet.basis j)
      = ((t : ℝ) : ℂ) ^ (weylWeight j.1) • DownSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  simp [DownSinglet.basis, DownSinglet.repLorentzGroup, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply, rightHandedWeyl_rep_boostAxis_two_basis]
  rw [← TensorProduct.smul_tmul', map_smul]

end StandardModel
