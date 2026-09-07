/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# The jet algebra of the Higgs field

## i. Overview

The Higgs field is a bosonic matter field valued in `HiggsVec`, so its jet algebra is the
bosonic algebra `BosonicAlgebra HiggsVec`: the symmetric algebra on the component
functions `∂_s H_α` and `∂_s H̄_α`, commuting as bosons do.

The file first equips the jets `JetRing ⊗[ℂ] HiggsVec` of the Higgs field with the action
of the jet gauge group, following the same pattern as the fermion species (see
`Physlib.Particles.StandardModel.Fermions.DownSinglet`): the `SU(2)` power-series matrix,
scaled by the hypercharge power series `u ^ 3`, acts `JetRing`-linearly through the
identification `JetRing ⊗[ℂ] HiggsVec ≃ EuclideanSpace JetRing (Fin 2)`. Everything the
generic bosonic algebra provides — the total derivative, the Lorentz action (trivial: the
Higgs is a Lorentz scalar), the jet gauge action, and the mass-weight scaling at the Higgs
mass weight `2` — is then instantiated.

## ii. Key results

- `HiggsVec.jetValLinEquiv` : the jets of the Higgs field as a `JetRing`-valued doublet.
- `HiggsVec.repJetGaugeGroupI` : the jet gauge action on the jets of the Higgs field.
- `HiggsVec.repJetGaugeGroupI_smul` : the action is fibrewise.
- `HiggsVec.repJetGaugeGroupI_ofConstant` : constant jets act by the global gauge action.
- `HiggsJetAlgebra` : the jet algebra of the Higgs field.
- `HiggsJetAlgebra.ofHiggs`, `HiggsJetAlgebra.ofConjHiggs` : the component functions.
- `HiggsJetAlgebra.repLorentzGroup`, `HiggsJetAlgebra.repJetGaugeGroupI` : the actions.
- `HiggsJetAlgebra.massWeightScale` : the mass-dimension scaling at mass weight `2`.

## iii. Table of contents

- A. The jet gauge action on the jets of the Higgs field
  - A.1. The jets of the Higgs field
  - A.2. The action of the jet gauge group
  - A.3. Fibrewise linearity
  - A.4. Constant jets act by the global gauge action
- B. The jet algebra of the Higgs field
  - B.1. The component functions
  - B.2. The Lorentz action
  - B.3. The jet gauge action
  - B.4. The mass-dimension scaling

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix

namespace HiggsVec

/-!

## A. The jet gauge action on the jets of the Higgs field

-/

/-!

### A.1. The jets of the Higgs field

-/

/-- Absorbs the jet ring into the weak index: a jet of the Higgs field is the same thing
as a `JetRing`-valued weak doublet,

  `JetRing ⊗[ℂ] HiggsVec ≃ EuclideanSpace JetRing (Fin 2)`.

-/
noncomputable def jetValLinEquiv :
    JetRing ⊗[ℂ] HiggsVec ≃ₗ[ℂ] EuclideanSpace JetRing (Fin 2) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ JetRing)
      (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ))).trans <|
    ((TensorProduct.piScalarRight ℂ JetRing JetRing (Fin 2)).trans
      (WithLp.linearEquiv 2 JetRing (Fin 2 → JetRing)).symm).restrictScalars ℂ

lemma jetValLinEquiv_tmul (f : JetRing) (v : HiggsVec) :
    jetValLinEquiv (f ⊗ₜ[ℂ] v) = WithLp.toLp 2 fun i => v.ofLp i • f := rfl

/-- The identification of the jets of the Higgs field is `JetRing`-linear: multiplying a
  jet by a scalar jet multiplies each of its weak components. -/
lemma jetValLinEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] HiggsVec) :
    jetValLinEquiv (χ • z) = χ • jetValLinEquiv z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul f v =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, jetValLinEquiv_tmul, jetValLinEquiv_tmul]
    refine WithLp.ofLp_injective 2 ?_
    funext i
    show v.ofLp i • (χ * f) = χ * (v.ofLp i • f)
    rw [Algebra.mul_smul_comm]

lemma jetValLinEquiv_symm_smul (χ : JetRing) (y : EuclideanSpace JetRing (Fin 2)) :
    jetValLinEquiv.symm (χ • y) = χ • jetValLinEquiv.symm y := by
  apply jetValLinEquiv.injective
  rw [LinearEquiv.apply_symm_apply, jetValLinEquiv_smul, LinearEquiv.apply_symm_apply]

/-!

### A.2. The action of the jet gauge group

-/

/-- The matrix of jets through which a jet of gauge transformations acts on the Higgs
  doublet: the `SU(2)` power-series matrix scaled by the hypercharge power series
  `u ^ 3`. -/
noncomputable def jetGaugeMatrix (U : JetGaugeGroupI) : Matrix (Fin 2) (Fin 2) JetRing :=
  (((U.2.2 : unitary JetRing) : JetRing) ^ 3) •
    ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing)

lemma jetGaugeMatrix_one : jetGaugeMatrix 1 = 1 := by
  simp [jetGaugeMatrix]

lemma jetGaugeMatrix_mul (U₁ U₂ : JetGaugeGroupI) :
    jetGaugeMatrix (U₁ * U₂) = jetGaugeMatrix U₁ * jetGaugeMatrix U₂ := by
  rw [jetGaugeMatrix, jetGaugeMatrix, jetGaugeMatrix,
    show (((U₁ * U₂).2.2 : unitary JetRing) : JetRing) =
      ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing) from rfl,
    show (((U₁ * U₂).2.1 : specialUnitaryGroup (Fin 2) JetRing) :
        Matrix (Fin 2) (Fin 2) JetRing) =
      ((U₁.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) *
        ((U₂.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing)
      from rfl,
    mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The `2_{3}` action of the jet gauge group on the jets of the Higgs field. Through
`jetValLinEquiv` the weak matrix of the gauge jet, carrying the `3` hypercharge phase
`u ^ 3`, acts `JetRing`-linearly by matrix-vector multiplication. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] HiggsVec) where
  toFun U :=
    jetValLinEquiv.symm.toLinearMap ∘ₗ
      ((Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U)).restrictScalars ℂ :
        EuclideanSpace JetRing (Fin 2) →ₗ[ℂ] EuclideanSpace JetRing (Fin 2)) ∘ₗ
      jetValLinEquiv.toLinearMap
  map_one' := by
    have hres : (1 : Module.End JetRing (EuclideanSpace JetRing (Fin 2))).restrictScalars ℂ
        = 1 := rfl
    rw [jetGaugeMatrix_one, map_one, hres]
    ext z
    simp
  map_mul' U₁ U₂ := by
    have hres : ∀ f g : Module.End JetRing (EuclideanSpace JetRing (Fin 2)),
        (f * g).restrictScalars ℂ = f.restrictScalars ℂ * g.restrictScalars ℂ :=
      fun _ _ => rfl
    rw [jetGaugeMatrix_mul, map_mul, hres]
    ext z
    simp

lemma repJetGaugeGroupI_apply (U : JetGaugeGroupI) (z : JetRing ⊗[ℂ] HiggsVec) :
    repJetGaugeGroupI U z =
      jetValLinEquiv.symm
        (Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix U) (jetValLinEquiv z)) := rfl

/-!

### A.3. Fibrewise linearity

-/

/-- **The jet gauge action on the jets of the Higgs field is fibrewise**: it commutes
  with multiplication by scalar jets, acting on the values of the field over the identity
  on spacetime. This is the hypothesis under which the action lifts to the bosonic
  algebra. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] HiggsVec) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  rw [repJetGaugeGroupI_apply, repJetGaugeGroupI_apply, jetValLinEquiv_smul, map_smul,
    jetValLinEquiv_symm_smul]

/-!

### A.4. Constant jets act by the global gauge action

-/

/-- On jets of constant gauge transformations the jet action reduces to the global gauge
action on the fibre: the action `HiggsVec.repGaugeGroupI` on the Higgs factor, and the
trivial action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext f v
  have hu : (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
      = MvPowerSeries.C ((g.toU1.1 : ℂ)) := rfl
  have hM : ∀ i j, (((JetGaugeGroupI.ofConstant g).2.1 :
        specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) i j
      = MvPowerSeries.C (g.toSU2.1 i j) := fun _ _ => rfl
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, repJetGaugeGroupI_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  apply jetValLinEquiv.injective
  rw [LinearEquiv.apply_symm_apply, jetValLinEquiv_tmul, jetValLinEquiv_tmul]
  have halg : (Matrix.toLpLinAlgEquiv 2 (jetGaugeMatrix (JetGaugeGroupI.ofConstant g)) :
      Module.End JetRing (EuclideanSpace JetRing (Fin 2)))
      = Matrix.toLpLin 2 2 (jetGaugeMatrix (JetGaugeGroupI.ofConstant g)) := rfl
  rw [halg]
  refine WithLp.ofLp_injective 2 ?_
  funext i
  simp only [Matrix.toLpLin_toLp, Matrix.toLin'_apply, Matrix.mulVec_apply_eq_sum]
  rw [show (repGaugeGroupI g v).ofLp = g.toU1 ^ 3 • (g.toSU2.1 *ᵥ v.ofLp) from rfl]
  simp only [jetGaugeMatrix, Matrix.smul_apply, hu, hM, ← map_pow, smul_eq_mul, ← map_mul,
    Pi.smul_apply, Matrix.mulVec_apply_eq_sum, Submonoid.smul_def, smul_eq_mul,
    Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm,
    show (MvPowerSeries.C (((GaugeGroupI.toU1 g : unitary ℂ) : ℂ) ^ 3
          * (g.toSU2.1 i j)) : JetRing) * f
        = (((GaugeGroupI.toU1 g : unitary ℂ) : ℂ) ^ 3 * (g.toSU2.1 i j)) • f from by
      rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply],
    smul_smul]
  congr 1
  rw [show ((GaugeGroupI.toU1 (g ^ 3) : unitary ℂ) : ℂ)
      = ((GaugeGroupI.toU1 g : unitary ℂ) : ℂ) ^ 3 from rfl]
  ring

end HiggsVec

/-!

## B. The jet algebra of the Higgs field

-/

/-- **The jet algebra of the Higgs field**: the bosonic algebra of the `HiggsVec`-valued
  Higgs field. Its generators are the component functions `∂_s H_α` and `∂_s H̄_α`, and
  they commute — the Higgs is a boson. -/
abbrev HiggsJetAlgebra : Type := BosonicAlgebra HiggsVec

namespace HiggsJetAlgebra

/-!

### B.1. The component functions

-/

/-- The component functions of the Higgs field inside its jet algebra. -/
noncomputable def ofHiggs : Module.Dual ℂ HiggsVec →ₗ[ℂ] HiggsJetAlgebra :=
  BosonicAlgebra.ofField

/-- The conjugate component functions of the Higgs field inside its jet algebra. -/
noncomputable def ofConjHiggs :
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] HiggsJetAlgebra :=
  BosonicAlgebra.ofConjField

/-!

### B.2. The Lorentz action

-/

open Matrix MatrixGroups in
/-- The Lorentz action on the jet algebra of the Higgs field: the Higgs is a Lorentz
  scalar, so the Lorentz group acts on the component functions only through their
  derivative labels. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) HiggsJetAlgebra :=
  BosonicAlgebra.repLorentzGroup (Representation.trivial ℂ SL(2,ℂ) HiggsVec)

/-!

### B.3. The jet gauge action

-/

/-- The jet gauge action on the jet algebra of the Higgs field, lifted from the fibrewise
  action on its jets. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI HiggsJetAlgebra :=
  BosonicAlgebra.repJetGaugeGroupI HiggsVec.repJetGaugeGroupI
    HiggsVec.repJetGaugeGroupI_smul

/-- The action of the constant — global — gauge transformations on the jet algebra of the
  Higgs field. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI HiggsJetAlgebra :=
  BosonicAlgebra.repGaugeGroupI HiggsVec.repJetGaugeGroupI
    HiggsVec.repJetGaugeGroupI_smul

/-!

### B.4. The mass-dimension scaling

-/

/-- The mass-dimension scaling on the jet algebra of the Higgs field: the Higgs has mass
  dimension one, that is mass weight two, and each derivative adds mass weight two. -/
noncomputable def massWeightScale (c : ℂ) : HiggsJetAlgebra →ₐ[ℂ] HiggsJetAlgebra :=
  BosonicAlgebra.massWeightScale 2 c

/-- The Higgs field carries mass weight two — mass dimension one. -/
@[simp]
lemma massWeightScale_ofHiggs (c : ℂ) (φ : Module.Dual ℂ HiggsVec) :
    massWeightScale c (ofHiggs φ) = c ^ 2 • ofHiggs φ :=
  BosonicAlgebra.massWeightScale_ofField 2 c φ

/-- A derivative of the Higgs field adds mass weight two. -/
lemma massWeightScale_jetDeriv (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : HiggsJetAlgebra) :
    massWeightScale c (BosonicAlgebra.jetDeriv μ x)
      = c ^ 2 • BosonicAlgebra.jetDeriv μ (massWeightScale c x) :=
  BosonicAlgebra.massWeightScale_jetDeriv 2 c μ x

end HiggsJetAlgebra

end StandardModel
