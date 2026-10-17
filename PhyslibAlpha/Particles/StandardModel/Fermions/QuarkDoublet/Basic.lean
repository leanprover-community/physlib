/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.Basic
public import PhyslibAlpha.Relativity.Fermions.Weyl.BoostWeight
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.GaugeWeight
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.JetGaugeGroup.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction
public import PhyslibAlpha.Particles.StandardModel.GaugeGroup.LocalGaugeData
public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# The type corresponding to quark doublets

## i. Overview

In this module we define the type corresponding to
the target vector space of a quark field in the Standard Model.

On this type we define a representation of the Lorentz group, and a
representation of the Standard Model gauge group.

## ii. Key results

- `basis` : a basis on the quark doublets
- `colourWeakEquiv` : the colour and weak factors of the quark doublet combined into a single
  Euclidean factor over `Fin 3 × Fin 2`
- `colourWeakEquiv_tmul`
- `jetValLinEquiv`

## iii. Table of contents

- A. Equivalence with the underlying tensor product space
- B. The structure of a module
- C. The basis of the quark doublet space
- D. Lorentz group representation
- E. The representation of the Standard Model gauge group
- F. The representation of the jet gauge group
- G. Component transformation laws
- H. The gauge weight of the QuarkDoublet components
- I. The boost weight of the QuarkDoublet components

## iv. References

* None.

-/

@[expose] public section

namespace StandardModel

open TensorProduct

namespace QuarkDoublet

/-!

## A. Equivalence with the underlying tensor product space

-/

/-!

## B. The structure of a module

The AddCommGroup and module instances are inherited from the underlying tensor product space.
-/

/-!

## C. The basis of the quark doublet space

-/

/-- A basis on the quark doublets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 3 × Fin 2) ℂ QuarkDoublet :=
  ((((Fermion.LeftHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).map valLinEquiv.symm).reindex
    (Equiv.prodAssoc (Fin 2) (Fin 3) (Fin 2)))

instance : Module.Finite ℂ QuarkDoublet := Module.Finite.of_basis basis

instance : Module.Free ℂ QuarkDoublet := Module.Free.of_basis basis

/-!

## D. Lorentz group representation

-/
open Matrix MatrixGroups

/-!

## E. The representation of the Standard Model gauge group

-/

/-!

## F. The representation of the jet gauge group

The colour and weak indices are combined into the single index `Fin 3 × Fin 2`, on which
the `SU(3)` and `SU(2)` power-series matrices of a jet of gauge transformations act
together through their Kronecker product, scaled by the hypercharge power series `u`.

-/

open Kronecker

/-- The colour and weak factors of the quark doublet combined into a single Euclidean
factor over `Fin 3 × Fin 2`. -/
noncomputable def colourWeakEquiv :
    EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2) ≃ₗ[ℂ] (Fin 3 × Fin 2 → ℂ) :=
  (TensorProduct.congr (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ))
      (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ))).trans <|
    (TensorProduct.piScalarRight ℂ ℂ (Fin 3 → ℂ) (Fin 2)).trans <|
      (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 3)).symm.trans <|
        LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (Equiv.prodComm (Fin 2) (Fin 3))

@[simp]
lemma colourWeakEquiv_tmul (c : EuclideanSpace ℂ (Fin 3)) (w : EuclideanSpace ℂ (Fin 2))
    (p : Fin 3 × Fin 2) :
    colourWeakEquiv (c ⊗ₜ[ℂ] w) p = c.ofLp p.1 * w.ofLp p.2 := by
  simp [colourWeakEquiv, Function.uncurry, Algebra.algebraMap_eq_smul_one, mul_comm]

/-- Absorbs the jet ring into the combined colour–weak index: a jet of a quark doublet is
the same thing as a left-handed Weyl spinor tensored with a `SpaceTimeAlgebra`-valued
colour–weak vector,

  `SpaceTimeAlgebra ⊗[ℂ] QuarkDoublet ≃
    LeftHandedWeyl ⊗[ℂ] EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2)`.

-/
noncomputable def jetValLinEquiv :
    SpaceTimeAlgebra ⊗[ℂ] QuarkDoublet ≃ₗ[ℂ]
      Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ SpaceTimeAlgebra)
      (valLinEquiv.trans (TensorProduct.assoc ℂ Fermion.LeftHandedWeyl
        (EuclideanSpace ℂ (Fin 3)) (EuclideanSpace ℂ (Fin 2))))).trans <|
    (TensorProduct.leftComm ℂ SpaceTimeAlgebra Fermion.LeftHandedWeyl
        (EuclideanSpace ℂ (Fin 3) ⊗[ℂ] EuclideanSpace ℂ (Fin 2))).trans <|
      TensorProduct.congr (LinearEquiv.refl ℂ Fermion.LeftHandedWeyl) <|
        (TensorProduct.congr (LinearEquiv.refl ℂ SpaceTimeAlgebra) colourWeakEquiv).trans <|
          ((TensorProduct.piScalarRight ℂ SpaceTimeAlgebra SpaceTimeAlgebra (Fin 3 × Fin 2)).trans
            (WithLp.linearEquiv 2 SpaceTimeAlgebra
                (Fin 3 × Fin 2 → SpaceTimeAlgebra)).symm).restrictScalars ℂ

/-- The matrix of jets through which a jet of gauge transformations acts on the combined
colour–weak index of the quark doublet: the Kronecker product of the `SU(3)` and `SU(2)`
power-series matrices, scaled by the hypercharge power series `u`. -/
noncomputable def jetGaugeMatrix (U : JetGaugeGroupI) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) SpaceTimeAlgebra :=
  ((U.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) •
    (((U.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) : Matrix (Fin 3)
        (Fin 3) SpaceTimeAlgebra) ⊗ₖ
      ((U.2.1 : specialUnitaryGroup (Fin 2) SpaceTimeAlgebra) : Matrix (Fin 2)
          (Fin 2) SpaceTimeAlgebra))

lemma jetGaugeMatrix_one : jetGaugeMatrix 1 = 1 := by
  rw [jetGaugeMatrix,
    show (((1 : JetGaugeGroupI).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) = 1 from rfl,
    show ((((1 : JetGaugeGroupI).1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra)) :
      Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra) = 1 from rfl,
    show ((((1 : JetGaugeGroupI).2.1 : specialUnitaryGroup (Fin 2) SpaceTimeAlgebra)) :
      Matrix (Fin 2) (Fin 2) SpaceTimeAlgebra) = 1 from rfl,
    Matrix.one_kronecker_one, one_smul]

lemma jetGaugeMatrix_mul (U₁ U₂ : JetGaugeGroupI) :
    jetGaugeMatrix (U₁ * U₂) = jetGaugeMatrix U₁ * jetGaugeMatrix U₂ := by
  rw [jetGaugeMatrix, jetGaugeMatrix, jetGaugeMatrix,
    show (((U₁ * U₂).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) =
      ((U₁.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) *
          ((U₂.2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) from rfl,
    show (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
        Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra) =
      ((U₁.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) : Matrix (Fin 3)
          (Fin 3) SpaceTimeAlgebra) *
        ((U₂.1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) : Matrix (Fin 3)
            (Fin 3) SpaceTimeAlgebra)
      from rfl,
    show (((U₁ * U₂).2.1 : specialUnitaryGroup (Fin 2) SpaceTimeAlgebra) :
        Matrix (Fin 2) (Fin 2) SpaceTimeAlgebra) =
      ((U₁.2.1 : specialUnitaryGroup (Fin 2) SpaceTimeAlgebra) : Matrix (Fin 2)
          (Fin 2) SpaceTimeAlgebra) *
        ((U₂.2.1 : specialUnitaryGroup (Fin 2) SpaceTimeAlgebra) : Matrix (Fin 2)
            (Fin 2) SpaceTimeAlgebra)
      from rfl,
    Matrix.mul_kronecker_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The `(3, 2)_{1}` action of the jet gauge group on the jet space of the quark doublet.
Through `jetValLinEquiv` the Kronecker matrix of the gauge jet, carrying the hypercharge
phase `u`, acts `SpaceTimeAlgebra`-linearly on the combined colour–weak factor by matrix-vector
multiplication, while the Weyl factor is untouched. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (SpaceTimeAlgebra ⊗[ℂ] QuarkDoublet) where
  toFun U :=
    jetValLinEquiv.symm.toLinearMap ∘ₗ
      Module.End.lTensorAlgHom ℂ (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2))
        Fermion.LeftHandedWeyl
        ((Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U)).restrictScalars ℂ) ∘ₗ
      jetValLinEquiv.toLinearMap
  map_one' := by
    have hres : (1 : Module.End SpaceTimeAlgebra
        (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2))).restrictScalars ℂ = 1 := rfl
    rw [jetGaugeMatrix_one, map_one, hres, map_one]
    ext d x
    simp [-valLinEquiv_apply]
  map_mul' U₁ U₂ := by
    have hres : ∀ f g : Module.End SpaceTimeAlgebra
        (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2)),
        (f * g).restrictScalars ℂ = f.restrictScalars ℂ * g.restrictScalars ℂ :=
      fun _ _ => rfl
    rw [jetGaugeMatrix_mul, map_mul, hres, map_mul]
    ext d x
    simp

/-- The entries of the gauge matrix of a jet of a constant gauge transformation are the
constant power series with the global gauge coefficients. -/
lemma jetGaugeMatrix_ofConstant (g : GaugeGroupI) (p q : Fin 3 × Fin 2) :
    jetGaugeMatrix (JetGaugeGroupI.ofConstant g) p q =
      MvPowerSeries.C ((g.toU1.1 : ℂ) * (g.toSU3.1 p.1 q.1 * g.toSU2.1 p.2 q.2)) := by
  rw [jetGaugeMatrix, Matrix.smul_apply,
    show (((JetGaugeGroupI.ofConstant g).2.2 : unitary SpaceTimeAlgebra) : SpaceTimeAlgebra) =
      MvPowerSeries.C ((g.toU1.1 : ℂ)) from rfl]
  rw [Matrix.kroneckerMap_apply,
    show (((JetGaugeGroupI.ofConstant g).1 : specialUnitaryGroup (Fin 3) SpaceTimeAlgebra) :
        Matrix (Fin 3) (Fin 3) SpaceTimeAlgebra) p.1 q.1 =
      MvPowerSeries.C (g.toSU3.1 p.1 q.1) from rfl,
    show (((JetGaugeGroupI.ofConstant g).2.1 : specialUnitaryGroup (Fin 2) SpaceTimeAlgebra) :
        Matrix (Fin 2) (Fin 2) SpaceTimeAlgebra) p.2 q.2 =
      MvPowerSeries.C (g.toSU2.1 p.2 q.2) from rfl,
    smul_eq_mul, ← map_mul, ← map_mul]

/-- The identification of the jets of the quark doublet intertwines multiplication by a
scalar jet with the `SpaceTimeAlgebra`-scalar action on the colour–weak coordinates. -/
lemma jetValLinEquiv_smul (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] QuarkDoublet) :
    jetValLinEquiv (χ • z)
      = Module.End.lTensorAlgHom ℂ (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2))
          Fermion.LeftHandedWeyl
          ((LinearMap.lsmul SpaceTimeAlgebra
            (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2)) χ).restrictScalars ℂ)
          (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, map_add]
  | tmul f x =>
    obtain ⟨v⟩ := x
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : QuarkDoublet) = 0 from rfl, TensorProduct.tmul_zero,
        smul_zero, map_zero, map_zero]
    | tmul vc w =>
      induction vc using TensorProduct.induction_on with
      | zero =>
        rw [show ({ val := (0 : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3))
            ⊗ₜ[ℂ] w } : QuarkDoublet) = 0 from by
          rw [TensorProduct.zero_tmul]; rfl, TensorProduct.tmul_zero, smul_zero,
          map_zero, map_zero]
      | tmul ψ c =>
        rw [TensorProduct.smul_tmul', smul_eq_mul,
          show jetValLinEquiv ((χ * f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet))
            = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • (χ * f)) from rfl,
          show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c ⊗ₜ[ℂ] w⟩ : QuarkDoublet))
            = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f) from rfl,
          show Module.End.lTensorAlgHom ℂ (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2))
              Fermion.LeftHandedWeyl
              ((LinearMap.lsmul SpaceTimeAlgebra
                (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2)) χ).restrictScalars ℂ)
              (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun q => colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f))
            = ψ ⊗ₜ[ℂ] (χ • WithLp.toLp 2 fun q =>
                colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f) from rfl]
        congr 1
        refine WithLp.ofLp_injective 2 ?_
        funext q
        show colourWeakEquiv (c ⊗ₜ[ℂ] w) q • (χ * f)
          = χ * (colourWeakEquiv (c ⊗ₜ[ℂ] w) q • f)
        rw [Algebra.mul_smul_comm]
      | add a b ha hb =>
        rw [show ({ val := (a + b) ⊗ₜ[ℂ] w } : QuarkDoublet)
            = ⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ from by
          rw [show (⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ : QuarkDoublet)
              = ⟨a ⊗ₜ[ℂ] w + b ⊗ₜ[ℂ] w⟩ from rfl, TensorProduct.add_tmul],
          TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]
    | add a b ha hb =>
      rw [show ({ val := a + b } : QuarkDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]

/-- **The jet gauge action on the jets of the quark doublet is fibrewise**: it commutes
with multiplication by scalar jets. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : SpaceTimeAlgebra)
    (z : SpaceTimeAlgebra ⊗[ℂ] QuarkDoublet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  set S : Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2)) :=
    LinearMap.lsmul SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2)) χ with hS
  set M : Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2)) :=
    (Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U) :
      Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2))) with hM
  have hMS : M * S = S * M := LinearMap.ext fun e => by
    simp only [Module.End.mul_apply, hS, LinearMap.lsmul_apply, map_smul]
  apply jetValLinEquiv.injective
  rw [show repJetGaugeGroupI U (χ • z)
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.LeftHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv (χ • z))) from rfl,
    LinearEquiv.apply_symm_apply, jetValLinEquiv_smul,
    show repJetGaugeGroupI U z
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.LeftHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv z)) from rfl,
    jetValLinEquiv_smul, LinearEquiv.apply_symm_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    show M.restrictScalars ℂ * S.restrictScalars ℂ = (M * S).restrictScalars ℂ from rfl,
    show S.restrictScalars ℂ * M.restrictScalars ℂ = (S * M).restrictScalars ℂ from rfl,
    hMS]

/-- On jets of constant gauge transformations the jet action reduces to the global gauge
action on the fibre: the `(3, 2)_{1}` action on the quark-doublet factor, and the trivial
action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext d x
  obtain ⟨v⟩ := x
  induction v using TensorProduct.induction_on with
  | zero => simp [show ({ val := 0 } : QuarkDoublet) = 0 from rfl]
  | tmul vc w =>
      induction vc using TensorProduct.induction_on with
      | zero =>
          have h : ({ val := (0 : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3))
              ⊗ₜ[ℂ] w } : QuarkDoublet) = 0 := by
            rw [TensorProduct.zero_tmul]
            rfl
          rw [h]
          simp
      | tmul psi c =>
          apply jetValLinEquiv.injective
          simp [repJetGaugeGroupI, jetValLinEquiv, repGaugeGroupI, -TensorProduct.congr_symm]
          have halg : ∀ A : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) SpaceTimeAlgebra,
              (Matrix.toLpLinAlgEquiv 2 A :
                  Module.End SpaceTimeAlgebra (EuclideanSpace SpaceTimeAlgebra (Fin 3 × Fin 2)))
                = Matrix.toLpLin 2 2 A := fun _ => rfl
          rw [TensorProduct.liftAux_tmul]
          simp only [LinearMap.compl₂_apply, TensorProduct.mk_apply, LinearMap.smul_apply,
            LinearMap.restrictScalars_apply, halg, Matrix.toLpLin_toLp]
          rw [← TensorProduct.tmul_smul]
          congr 1
          refine WithLp.ofLp_injective 2 ?_
          funext p
          simp only [WithLp.ofLp_smul, Pi.smul_apply, Matrix.toLin'_apply,
            Matrix.mulVec_apply_eq_sum, jetGaugeMatrix_ofConstant, Algebra.smul_def,
            MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]
          rw [Finset.sum_congr rfl fun q _ => by
            rw [show MvPowerSeries.C ((g.toU1.1 : ℂ) * (g.toSU3.1 p.1 q.1 * g.toSU2.1 p.2 q.2))
                  * (MvPowerSeries.C (c.ofLp q.1 * w.ofLp q.2) * d)
                = MvPowerSeries.C ((g.toU1.1 : ℂ) * (g.toSU3.1 p.1 q.1 * g.toSU2.1 p.2 q.2)
                    * (c.ofLp q.1 * w.ofLp q.2)) * d from by
              rw [← mul_assoc, ← map_mul]], ← Finset.sum_mul, ← map_sum]
          rw [← mul_assoc, ← map_mul]
          congr 1
          rw [Fintype.sum_prod_type,
            show (∑ j, g.toSU3.1 p.1 j * c.ofLp j) * (∑ j, g.toSU2.1 p.2 j * w.ofLp j)
                = ∑ i, ∑ j, (g.toSU3.1 p.1 i * c.ofLp i) * (g.toSU2.1 p.2 j * w.ofLp j) from
              Finset.sum_mul_sum _ _ _ _, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      | add a b ha hb =>
          simp only [show ({ val := (a + b) ⊗ₜ[ℂ] w } : QuarkDoublet)
              = ⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ from by
            rw [show (⟨a ⊗ₜ[ℂ] w⟩ + ⟨b ⊗ₜ[ℂ] w⟩ : QuarkDoublet)
                = ⟨a ⊗ₜ[ℂ] w + b ⊗ₜ[ℂ] w⟩ from rfl, TensorProduct.add_tmul],
            map_add, ha, hb]
  | add a b ha hb =>
      simp only [show ({ val := a + b } : QuarkDoublet) = ⟨a⟩ + ⟨b⟩ from rfl,
        map_add, ha, hb]

/-!

## G. Component transformation laws

The basis of `QuarkDoublet` splits as a left-handed Weyl index, a colour index and a
weak-isospin index. The Lorentz group moves only the first, the gauge group only the last
two (up to the hypercharge scalar), so each action is recorded as a sum over the indices it
moves. Dualising inverts and transposes the coefficient matrices, and conjugating stars
them; the four combinations below are what a component of a quark-doublet symbol needs.

-/

/-- The quark-doublet basis vector as an explicit spinor–colour–weak tensor. -/
lemma basis_eq_mk (k : Fin 2) (c : Fin 3) (w : Fin 2) : basis (k, c, w) =
    ⟨Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c
      ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ w⟩ := by
  simp only [basis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis,
    Equiv.prodAssoc_symm_apply]
  rfl

/-- The Lorentz action on the quark-doublet basis: the colour and weak indices are inert
  and the spinor index transforms by the matrix itself. -/
lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentzGroup Λ (basis j) = ∑ β, Λ.1 β j.1 • basis (β, j.2.1, j.2.2) := by
  obtain ⟨k, c, w⟩ := j
  simp only [basis_eq_mk, repLorentzGroup, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    valLinEquiv_apply, TensorProduct.map_tmul, Fermion.LeftHandedWeyl.rep_apply_basis,
    Representation.trivial_apply, TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
  exact map_smul valLinEquiv.symm _ _

/-- The quark-doublet coordinate functionals transform contragrediently, by the inverse
  matrix. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentzGroup.dual Λ (basis.dualBasis j) =
      ∑ β, (Λ⁻¹).1 j.1 β • basis.dualBasis (β, j.2.1, j.2.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup basis Λ j
    (Matrix.of fun p q => if p.2 = q.2 then (Λ⁻¹).1 p.1 q.1 else 0)
    (fun q => by
      rw [repLorentzGroup_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The Lorentz action on the conjugate quark-doublet basis: the coefficients are the
  conjugates of those of the quark-doublet action. -/
lemma repLorentzGroup_conj_apply_basis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentzGroup.conj Λ ((Basis.conj basis) j) =
      ∑ β, star (Λ.1 β j.1) • (Basis.conj basis) (β, j.2.1, j.2.2) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repLorentzGroup_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Basis.conj_apply]

/-- The conjugate quark-doublet coordinate functionals transform by the entrywise
  conjugate of the inverse matrix. -/
lemma repLorentzGroup_conj_dual_dualBasis (Λ : SL(2,ℂ)) (j : Fin 2 × Fin 3 × Fin 2) :
    repLorentzGroup.conj.dual Λ ((Basis.conj basis).dualBasis j) =
      ∑ β, star ((Λ⁻¹).1 j.1 β) • (Basis.conj basis).dualBasis (β, j.2.1, j.2.2) := by
  have key := Representation.dual_apply_dualBasis repLorentzGroup.conj (Basis.conj basis) Λ j
    (Matrix.of fun p q => if p.2 = q.2 then star ((Λ⁻¹).1 p.1 q.1) else 0)
    (fun q => by
      rw [repLorentzGroup_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- **The centre of `SL(2,ℂ)` acts on the quark-doublet space by `-1`**: the value space carries a
  single Weyl-spinor index, and `-1` is not the identity on a half-integer spin. -/
lemma repLorentzGroup_neg_one : repLorentzGroup (-1) = -LinearMap.id := by
  apply basis.ext
  intro j
  obtain ⟨a, c, w⟩ := j
  rw [repLorentzGroup_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply, Module.Basis.tensorProduct_apply]

/-- The centre acts on the conjugate quark-doublet space by `-1` as well: conjugation does not
  move a real sign. -/
lemma repLorentzGroup_conj_neg_one : repLorentzGroup.conj (-1) = -LinearMap.id := by
  apply (Basis.conj basis).ext
  intro j
  obtain ⟨a, c, w⟩ := j
  rw [repLorentzGroup_conj_apply_basis]
  fin_cases a <;>
    simp [basis, Matrix.one_apply, Module.Basis.tensorProduct_apply]

/-- The gauge action on the quark-doublet basis: the spinor index is inert, the colour
  index transforms by the `SU(3)` matrix and the weak index by the `SU(2)` matrix, scaled
  by the hypercharge factor. -/
lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3 × Fin 2) :
    repGaugeGroupI g (basis j) =
      ∑ c, ∑ w, (g.toU1.1 * g.toSU3.1 c j.2.1 * g.toSU2.1 w j.2.2) • basis (j.1, c, w) := by
  obtain ⟨k, c, w⟩ := j
  simp only [basis_eq_mk]
  exact repGaugeGroupI_tmul_basis_eq_sum g k c w

/-- The quark-doublet coordinate functionals carry the contragredient gauge action: the
  hypercharge, `SU(3)` and `SU(2)` factors of the inverse group element, transposed. -/
lemma repGaugeGroupI_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3 × Fin 2) :
    repGaugeGroupI.dual g (basis.dualBasis j) =
      ∑ c, ∑ w, ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 j.2.1 c * (g⁻¹).toSU2.1 j.2.2 w) •
        basis.dualBasis (j.1, c, w) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI basis g j
    (Matrix.of fun p q => if p.1 = q.1 then
      (g⁻¹).toU1.1 * (g⁻¹).toSU3.1 p.2.1 q.2.1 * (g⁻¹).toSU2.1 p.2.2 q.2.2 else 0)
    (fun q => by
      rw [repGaugeGroupI_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

/-- The gauge action on the conjugate quark-doublet basis: the coefficients of the
  quark-doublet action, conjugated. -/
lemma repGaugeGroupI_conj_apply_basis (g : GaugeGroupI) (j : Fin 2 × Fin 3 × Fin 2) :
    repGaugeGroupI.conj g ((Basis.conj basis) j) =
      ∑ c, ∑ w, star (g.toU1.1 * g.toSU3.1 c j.2.1 * g.toSU2.1 w j.2.2) •
        (Basis.conj basis) (j.1, c, w) := by
  rw [Representation.conj_apply, Basis.conj_apply, LinearEquiv.symm_apply_apply,
    repGaugeGroupI_apply_basis, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [LinearEquiv.map_smulₛₗ, starRingEnd_apply, Basis.conj_apply]

/-- The conjugate quark-doublet coordinate functionals carry the conjugate of the
  contragredient gauge action. -/
lemma repGaugeGroupI_conj_dual_dualBasis (g : GaugeGroupI) (j : Fin 2 × Fin 3 × Fin 2) :
    repGaugeGroupI.conj.dual g ((Basis.conj basis).dualBasis j) =
      ∑ c, ∑ w, star ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 j.2.1 c * (g⁻¹).toSU2.1 j.2.2 w) •
        (Basis.conj basis).dualBasis (j.1, c, w) := by
  have key := Representation.dual_apply_dualBasis repGaugeGroupI.conj (Basis.conj basis) g j
    (Matrix.of fun p q => if p.1 = q.1 then
      star ((g⁻¹).toU1.1 * (g⁻¹).toSU3.1 p.2.1 q.2.1 * (g⁻¹).toSU2.1 p.2.2 q.2.2) else 0)
    (fun q => by
      rw [repGaugeGroupI_conj_apply_basis]
      simp [Fintype.sum_prod_type, ite_smul, eq_comm])
  rw [key]
  simp [Fintype.sum_prod_type, ite_smul]

end QuarkDoublet

/-!

## H. The gauge weight of the QuarkDoublet components

The gauge torus acts diagonally on the basis of `QuarkDoublet`; the weights are recorded by
`QuarkDoublet.valueGaugeWeight`, and pass to the dual and conjugate-dual coordinate
functionals with the expected signs.

-/

/-- The gauge weight of the quark-doublet basis: the colour and isospin weights and
  hypercharge `1`. -/
def QuarkDoublet.valueGaugeWeight (j : Fin 2 × Fin 3 × Fin 2) : GaugeWeight :=
  ((colourWeight j.2.1).1, (colourWeight j.2.1).2, isoWeight j.2.2, 1)

/-- The gauge torus acts diagonally on the basis of `QuarkDoublet`, with the weights
  `QuarkDoublet.valueGaugeWeight`. -/
lemma QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI (gaugeTorusGen i) (QuarkDoublet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) •
        QuarkDoublet.basis j := by
  obtain ⟨k, c, s⟩ := j
  have hb : QuarkDoublet.basis (k, c, s)
      = ⟨Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c ⊗ₜ[ℂ]
      EuclideanSpace.basisFun (Fin 2) ℂ s⟩ := by
    simp only [QuarkDoublet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
      OrthonormalBasis.coe_toBasis,
      Module.Basis.reindex_apply, Equiv.prodAssoc_symm_apply]
    rfl
  rw [hb, QuarkDoublet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;> fin_cases s <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo,
      Fin.sum_univ_three, GaugeGroupI.toSU2, su2ExpI, Fin.sum_univ_two,
      Matrix.diagonal,
      QuarkDoublet.valueGaugeWeight, colourWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star]

/-- The dual action of the gauge torus on the coordinate functionals of
  `QuarkDoublet`: the weights are negated. -/
lemma QuarkDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4)
    (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI.dual (gaugeTorusGen i) (QuarkDoublet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i))) •
        QuarkDoublet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `QuarkDoublet`: the two negations cancel and the weights are those of
  the value space. -/
lemma QuarkDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4)
    (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI.conj.dual (gaugeTorusGen i)
      (((Basis.conj QuarkDoublet.basis)).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) •
        ((Basis.conj QuarkDoublet.basis)).coord j := by
  have hd := dual_gaugeTorusGen_coord QuarkDoublet.repGaugeGroupI.conj
    ((Basis.conj QuarkDoublet.basis))
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-!

## I. The boost weight of the QuarkDoublet components

-/

open Lorentz in
/-- The quark-doublet basis diagonalises the `z`-boost: the colour and isospin indices are
  inert. -/
lemma quarkDoublet_repLorentzGroup_boostAxis_two_basis (t : ℝ) (ht : t ≠ 0)
    (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repLorentzGroup (SL2C.boostAxis 2 t ht) (QuarkDoublet.basis j)
      = ((t : ℝ) : ℂ) ^ (weylWeight j.1) • QuarkDoublet.basis j := by
  obtain ⟨k, c, a⟩ := j
  simp [QuarkDoublet.basis, QuarkDoublet.repLorentzGroup, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply, leftHandedWeyl_rep_boostAxis_two_basis]
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', map_smul]

end StandardModel
