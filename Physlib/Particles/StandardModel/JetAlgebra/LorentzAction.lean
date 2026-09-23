/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.LorentzAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.JetAlgebra.SectorEquiv.Structure
/-!
# The Lorentz action on the jet algebra of the Standard Model

## i. Overview

The Lorentz group acts on the jet algebra of the Standard Model factor by factor: on the
two matter factors by the free-algebra functor applied to the species-wise Lorentz action
on the generator spaces of the field datum, and on the connection factor by the generic
complexified gauge-boson action. The action is multiplicative, restricts to the gauge
sector's own action through the sector inclusion, and intertwines the total derivative
through the columns of the Lorentz matrix — the total derivative is a Lorentz vector,
packaged as a `Lorentz.IsLorentzDeriv` instance.

The covariance of the derivative is assembled from the factor facts through an abstract
two-factor lemma proved at small types and instantiated, which keeps the proof outside the
full tensor product. On each free-algebra factor it comes from the
general covariance of the derivation extending a linear endomorphism, which is proved by
induction on the algebra: a derivation is not an algebra map, so extensionality of algebra
maps would not settle it.

## ii. Key results

- `JetAlgebra.repLorentzGroup` : the Lorentz action.
- `JetAlgebra.repLorentzGroup_apply_mul` : the action is multiplicative.
- `JetAlgebra.repLorentzGroup_includeGauge`,
  `JetAlgebra.repLorentzGroup_includeFermion`, `JetAlgebra.repLorentzGroup_includeHiggs` :
  the restriction to each of the three sectors.
- `JetAlgebra.repLorentzGroup_jetDeriv`, `JetAlgebra.instIsLorentzDeriv` : the total
  derivative is a Lorentz vector.

## iii. Table of contents

- A. The action of the Lorentz group
  - A.1. Multiplicativity
  - A.2. The action on the three factors
  - A.3. The action on the three sectors
- B. The total derivative is a Lorentz vector

-/

@[expose] public section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups

namespace JetAlgebra

/-!

## A. The action of the Lorentz group

-/

/-- The Lorentz action on the fermionic factor: the exterior-algebra functor applied to
  the species-wise Lorentz action on the fermionic generator space. -/
noncomputable abbrev repLorentzGroupFermion :
    Representation ℂ SL(2,ℂ) (ExteriorAlgebra ℂ fieldData.FermionGenerators) :=
  fieldData.repLorentzFermion.exteriorAlgebra

/-- The Lorentz action on the bosonic factor. -/
noncomputable abbrev repLorentzGroupBoson :
    Representation ℂ SL(2,ℂ) (SymmetricAlgebra ℂ fieldData.BosonGenerators) :=
  fieldData.repLorentzBoson.symmetricAlgebra

/-- The Lorentz action on the jet algebra of the Standard Model: the three factors
  transform independently. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) JetAlgebra :=
  (repLorentzGroupFermion.tprod repLorentzGroupBoson).tprod
    (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup GaugeAlgebra)

@[simp]
lemma repLorentzGroup_tmul (Λ : SL(2,ℂ))
    (w : ExteriorAlgebra ℂ fieldData.FermionGenerators ⊗[ℂ]
      SymmetricAlgebra ℂ fieldData.BosonGenerators)
    (g : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) :
    repLorentzGroup Λ (w ⊗ₜ[ℂ] g)
      = ((repLorentzGroupFermion.tprod repLorentzGroupBoson) Λ w)
          ⊗ₜ[ℂ] (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup GaugeAlgebra Λ g) := rfl

/-!

### A.1. Multiplicativity

-/

/-- The Lorentz action on the jet algebra is multiplicative. -/
lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (x y : JetAlgebra) :
    repLorentzGroup Λ (x * y) = repLorentzGroup Λ x * repLorentzGroup Λ y :=
  Representation.tprod_apply_mul _ _
    (Representation.tprod_apply_mul _ _
      (fun Λ' a b => Representation.exteriorAlgebra_apply_mul _ Λ' a b)
      (fun Λ' a b => Representation.symmetricAlgebra_apply_mul _ Λ' a b))
    (fun Λ' a b =>
      _root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup_apply_mul Λ' a b) Λ x y

/-!

### A.2. The action on the three factors

-/

/-- The Lorentz action on the complexified gauge sector fixes the unit. -/
lemma complexRepLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup GaugeAlgebra) Λ
      (1 : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) = 1 := by
  rw [Algebra.TensorProduct.one_def,
    _root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup_tmul,
    _root_.LocalGaugeFieldAlgebra.repLorentzGroup_apply_one]

/-- The matter factor of the Lorentz action fixes the unit, by the same abstract
  instantiation as in the gauge action. -/
lemma repLorentzGroup_matter_one (Λ : SL(2,ℂ)) :
    (repLorentzGroupFermion.tprod repLorentzGroupBoson) Λ
        (1 : fieldData.MatterAlgebra) = 1 :=
  Representation.tprod_apply_one _ _ Λ
    (Representation.exteriorAlgebra_apply_one _ Λ)
    (Representation.symmetricAlgebra_apply_one _ Λ)

/-- The Lorentz action restricts to the generic connection factor. -/
lemma repLorentzGroup_includeConnection (Λ : SL(2,ℂ))
    (y : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) :
    repLorentzGroup Λ (fieldData.includeConnection y)
      = fieldData.includeConnection
          (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup GaugeAlgebra Λ y) :=
  (congrArg (repLorentzGroup Λ) (GaugeFieldData.includeConnection_apply y)).trans
    ((Representation.tprod_apply_one_tmul _ _ Λ (repLorentzGroup_matter_one Λ) y).trans
      (GaugeFieldData.includeConnection_apply
        (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup GaugeAlgebra Λ y)).symm)

/-- The Lorentz action restricts to the fermionic factor, where it is the
  exterior-algebra functor applied to the species-wise action of the datum. -/
lemma repLorentzGroup_includeFermionFactor (Λ : SL(2,ℂ))
    (a : ExteriorAlgebra ℂ fieldData.FermionGenerators) :
    repLorentzGroup Λ (fieldData.includeFermion a)
      = fieldData.includeFermion (repLorentzGroupFermion Λ a) :=
  (congrArg (repLorentzGroup Λ) (GaugeFieldData.includeFermion_apply a)).trans
    ((Representation.tprod_apply_tmul_one _ _ Λ _
        (complexRepLorentzGroup_apply_one Λ)).trans
      ((congrArg (fun w : fieldData.MatterAlgebra =>
            ((w ⊗ₜ[ℂ] (1 : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)) : JetAlgebra))
          (Representation.tprod_apply_tmul_one _ _ Λ a
            (Representation.symmetricAlgebra_apply_one _ Λ))).trans
        (GaugeFieldData.includeFermion_apply (repLorentzGroupFermion Λ a)).symm))

/-- The Lorentz action restricts to the bosonic factor, where it is the
  symmetric-algebra functor applied to the species-wise action of the datum. -/
lemma repLorentzGroup_includeBosonFactor (Λ : SL(2,ℂ))
    (b : SymmetricAlgebra ℂ fieldData.BosonGenerators) :
    repLorentzGroup Λ (fieldData.includeBoson b)
      = fieldData.includeBoson (repLorentzGroupBoson Λ b) :=
  (congrArg (repLorentzGroup Λ) (GaugeFieldData.includeBoson_apply b)).trans
    ((Representation.tprod_apply_tmul_one _ _ Λ _
        (complexRepLorentzGroup_apply_one Λ)).trans
      ((congrArg (fun w : fieldData.MatterAlgebra =>
            ((w ⊗ₜ[ℂ] (1 : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)) : JetAlgebra))
          (Representation.tprod_apply_one_tmul _ _ Λ
            (Representation.exteriorAlgebra_apply_one _ Λ) b)).trans
        (GaugeFieldData.includeBoson_apply (repLorentzGroupBoson Λ b)).symm))

/-!

### A.3. The action on the three sectors

-/

/-- The Lorentz action restricts to the gauge sector's own action. The gauge sector
  inclusion is the connection inclusion of the datum, the Standard Model gauge bosons being
  the generic ones at `GaugeAlgebra`. -/
lemma repLorentzGroup_includeGauge (Λ : SL(2,ℂ))
    (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) :
    repLorentzGroup Λ (includeGauge y)
      = includeGauge (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup GaugeAlgebra Λ y) :=
  repLorentzGroup_includeConnection Λ y

/-- The Lorentz action restricts to the fermionic sector's own action. -/
lemma repLorentzGroup_includeFermion (Λ : SL(2,ℂ)) (f : FermionJetAlgebra) :
    repLorentzGroup Λ (includeFermion f)
      = includeFermion (FermionJetAlgebra.repLorentzGroup Λ f) :=
  (repLorentzGroup_includeFermionFactor Λ (fermionAlgebraEquiv f)).trans
    (congrArg fieldData.includeFermion (fermionAlgebraEquiv_repLorentzGroup Λ f).symm)

/-- The Lorentz action restricts to the Higgs sector's own action. -/
lemma repLorentzGroup_includeHiggs (Λ : SL(2,ℂ)) (h : HiggsJetAlgebra) :
    repLorentzGroup Λ (includeHiggs h)
      = includeHiggs (HiggsJetAlgebra.repLorentzGroup Λ h) :=
  (repLorentzGroup_includeBosonFactor Λ (higgsAlgebraEquiv h)).trans
    (congrArg fieldData.includeBoson (higgsAlgebraEquiv_repLorentzGroup Λ h).symm)

/-!

## B. The total derivative is a Lorentz vector

-/

/-- A factorwise sum of Lorentz-vector derivatives on a tensor product is a Lorentz
  vector: the abstract two-factor assembly, proved by tensor induction at abstract types
  so that it can be instantiated on the jet algebra without rewriting inside it. -/
private lemma tprod_deriv_sum {M N : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N]
    (ρ : Representation ℂ SL(2,ℂ) M) (σ : Representation ℂ SL(2,ℂ) N)
    (D : (Fin 1 ⊕ Fin 3) → M →ₗ[ℂ] M) (E : (Fin 1 ⊕ Fin 3) → N →ₗ[ℂ] N)
    (c : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℂ) (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (hD : ∀ ν x, ρ Λ (D ν x) = ∑ a, c a ν • D a (ρ Λ x))
    (hE : ∀ ν x, σ Λ (E ν x) = ∑ a, c a ν • E a (σ Λ x)) (x : M ⊗[ℂ] N) :
    (ρ.tprod σ) Λ
        ((TensorProduct.map (D μ) (LinearMap.id (M := N))
          + TensorProduct.map (LinearMap.id (M := M)) (E μ)) x)
      = ∑ a, c a μ •
          (TensorProduct.map (D a) (LinearMap.id (M := N))
            + TensorProduct.map (LinearMap.id (M := M)) (E a))
            ((ρ.tprod σ) Λ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add, smul_add]
  | tmul m n =>
    rw [LinearMap.add_apply, TensorProduct.map_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.id_apply, map_add,
      show (ρ.tprod σ) Λ ((D μ m) ⊗ₜ[ℂ] n) = (ρ Λ (D μ m)) ⊗ₜ[ℂ] (σ Λ n) from rfl,
      show (ρ.tprod σ) Λ (m ⊗ₜ[ℂ] (E μ n)) = (ρ Λ m) ⊗ₜ[ℂ] (σ Λ (E μ n)) from rfl,
      hD, hE, TensorProduct.sum_tmul, TensorProduct.tmul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [LinearMap.add_apply,
      show (ρ.tprod σ) Λ (m ⊗ₜ[ℂ] n) = (ρ Λ m) ⊗ₜ[ℂ] (σ Λ n) from rfl,
      TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.id_apply, smul_add, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul]

/-- **The total derivative on the jet algebra is a Lorentz vector.** -/
lemma repLorentzGroup_jetDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    repLorentzGroup Λ (jetDeriv μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        jetDeriv a (repLorentzGroup Λ x) := by
  have e : ∀ ν, TensorProduct.map
      (TensorProduct.map (jetDerivFermionFactor ν) LinearMap.id
        + TensorProduct.map LinearMap.id (jetDerivBosonFactor ν))
      (LinearMap.id (M := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra))
      + TensorProduct.map LinearMap.id
        (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra ν)
      = jetDeriv ν := fun ν =>
    congrArg (fun m => m + TensorProduct.map LinearMap.id
      (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra ν))
      (TensorProduct.map_add_left _ _ _)
  -- The two factor covariances are stated without a type ascription: instantiating the
  -- abstract lemma against an expected type leaves the family and the coefficients as
  -- metavariables, and solving them at this carrier does not terminate.
  have hFermion := fun (ν : Fin 1 ⊕ Fin 3)
      (z : ExteriorAlgebra ℂ fieldData.FermionGenerators) =>
    ExteriorAlgebra.exteriorAlgebra_derivationOfLinear fieldData.repLorentzFermion Λ
      (fun a => fieldData.jetDerivFermion a) ν
      (fun a => (((Lorentz.SL2C.toLorentzGroup Λ).1 a ν : ℝ) : ℂ))
      (fun w => GaugeFieldData.repLorentzFermion_jetDerivFermion Λ ν w) z
  have hBoson := fun (ν : Fin 1 ⊕ Fin 3)
      (z : SymmetricAlgebra ℂ fieldData.BosonGenerators) =>
    SymmetricAlgebra.symmetricAlgebra_derivationOfLinear fieldData.repLorentzBoson Λ
      (fun a => fieldData.jetDerivBoson a) ν
      (fun a => (((Lorentz.SL2C.toLorentzGroup Λ).1 a ν : ℝ) : ℂ))
      (fun w => GaugeFieldData.repLorentzBoson_jetDerivBoson Λ ν w) z
  have hFH : ∀ (ν : Fin 1 ⊕ Fin 3) (w : ExteriorAlgebra ℂ fieldData.FermionGenerators ⊗[ℂ]
      SymmetricAlgebra ℂ fieldData.BosonGenerators),
      (repLorentzGroupFermion.tprod repLorentzGroupBoson) Λ
        ((TensorProduct.map (jetDerivFermionFactor ν)
            (LinearMap.id (M := SymmetricAlgebra ℂ fieldData.BosonGenerators))
          + TensorProduct.map
            (LinearMap.id (M := ExteriorAlgebra ℂ fieldData.FermionGenerators))
            (jetDerivBosonFactor ν)) w)
      = ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a ν : ℝ) : ℂ) •
          (TensorProduct.map (jetDerivFermionFactor a)
            (LinearMap.id (M := SymmetricAlgebra ℂ fieldData.BosonGenerators))
            + TensorProduct.map
              (LinearMap.id (M := ExteriorAlgebra ℂ fieldData.FermionGenerators))
              (jetDerivBosonFactor a))
          ((repLorentzGroupFermion.tprod repLorentzGroupBoson) Λ w) := fun ν w =>
    tprod_deriv_sum _ _ _ _ _ Λ ν (fun κ z => hFermion κ z) (fun κ z => hBoson κ z) w
  refine (congrArg (fun (L : JetAlgebra →ₗ[ℂ] JetAlgebra) => repLorentzGroup Λ (L x))
    (e μ).symm).trans ((tprod_deriv_sum _ _ _ _ _ Λ μ hFH
      (fun κ z => _root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup_jetDeriv Λ κ z) x).trans
    (Finset.sum_congr rfl fun a _ => congrArg
      (fun (L : JetAlgebra →ₗ[ℂ] JetAlgebra) =>
        (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • L (repLorentzGroup Λ x))
      (e a)))

/-- The total derivatives on the jet algebra form a Lorentz derivative. -/
instance instIsLorentzDeriv : Lorentz.IsLorentzDeriv repLorentzGroup jetDeriv where
  rep_deriv := repLorentzGroup_jetDeriv _ _ _

end JetAlgebra

end StandardModel
