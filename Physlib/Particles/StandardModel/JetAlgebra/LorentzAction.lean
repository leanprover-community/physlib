/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.LorentzAction
/-!
# The Lorentz action on the jet algebra of the Standard Model

## i. Overview

The Lorentz group acts on the jet algebra of the Standard Model sector by sector: the
tensor product of the fermionic, Higgs and complexified gauge-boson actions. The action is
multiplicative, restricts to the gauge sector's own action through the sector inclusion,
and intertwines the total derivative through the columns of the Lorentz matrix — the
total derivative is a Lorentz vector, packaged as a `Lorentz.IsLorentzDeriv` instance.

The covariance of the derivative is assembled from the sector facts through an abstract
two-factor lemma proved at small types, instantiated in term mode — rewriting inside the
full tensor product is prohibitively slow.

## ii. Key results

- `JetAlgebra.repLorentzGroup` : the Lorentz action.
- `JetAlgebra.repLorentzGroup_apply_mul` : the action is multiplicative.
- `JetAlgebra.repLorentzGroup_includeGauge` : the restriction to the gauge sector.
- `JetAlgebra.repLorentzGroup_jetDeriv`, `JetAlgebra.instIsLorentzDeriv` : the total
  derivative is a Lorentz vector.

## iii. Table of contents

- A. The action of the Lorentz group
  - A.1. Multiplicativity
  - A.2. The action on the gauge sector
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

/-- The Lorentz action on the jet algebra of the Standard Model: the three sectors
  transform independently. -/
noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) JetAlgebra :=
  (FermionJetAlgebra.repLorentzGroup.tprod HiggsJetAlgebra.repLorentzGroup).tprod
    GaugeJetAlgebra.complexRepLorentzGroup

@[simp]
lemma repLorentzGroup_tmul (Λ : SL(2,ℂ)) (w : FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra)
    (g : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    repLorentzGroup Λ (w ⊗ₜ[ℂ] g)
      = ((FermionJetAlgebra.repLorentzGroup.tprod HiggsJetAlgebra.repLorentzGroup) Λ w)
          ⊗ₜ[ℂ] (GaugeJetAlgebra.complexRepLorentzGroup Λ g) := rfl

/-!

### A.1. Multiplicativity

-/

/-- The Lorentz action on the jet algebra is multiplicative. -/
lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (x y : JetAlgebra) :
    repLorentzGroup Λ (x * y) = repLorentzGroup Λ x * repLorentzGroup Λ y :=
  Representation.tprod_apply_mul _ _
    (Representation.tprod_apply_mul _ _
      (FermionicAlgebra.repLorentzGroup_apply_mul _)
      (BosonicAlgebra.repLorentzGroup_apply_mul _))
    GaugeJetAlgebra.complexRepLorentzGroup_apply_mul Λ x y

/-!

### A.2. The action on the gauge sector

-/

/-- The Lorentz action restricts to the gauge sector's own action. -/
lemma repLorentzGroup_includeGauge (Λ : SL(2,ℂ)) (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    repLorentzGroup Λ (includeGauge y)
      = includeGauge (GaugeJetAlgebra.complexRepLorentzGroup Λ y) := by
  rw [includeGauge_apply, repLorentzGroup_tmul,
    show (FermionJetAlgebra.repLorentzGroup.tprod HiggsJetAlgebra.repLorentzGroup) Λ
        ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] (1 : HiggsJetAlgebra))
      = (FermionJetAlgebra.repLorentzGroup Λ (1 : FermionJetAlgebra)) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repLorentzGroup Λ (1 : HiggsJetAlgebra)) from rfl,
    show HiggsJetAlgebra.repLorentzGroup Λ (1 : HiggsJetAlgebra) = 1 from
      BosonicAlgebra.repLorentzGroup_apply_one _ Λ,
    show FermionJetAlgebra.repLorentzGroup Λ (1 : FermionJetAlgebra) = 1 from
      FermionicAlgebra.repLorentzGroup_apply_one _ Λ,
    includeGauge_apply]

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
      (TensorProduct.map (FermionicAlgebra.jetDeriv ν) LinearMap.id
        + TensorProduct.map LinearMap.id (BosonicAlgebra.jetDeriv ν))
      (LinearMap.id (M := ℂ ⊗[ℝ] GaugeJetAlgebra))
      + TensorProduct.map LinearMap.id (GaugeJetAlgebra.complexJetDeriv ν)
      = jetDeriv ν := fun ν =>
    congrArg (fun m => m + TensorProduct.map LinearMap.id
      (GaugeJetAlgebra.complexJetDeriv ν)) (TensorProduct.map_add_left _ _ _)
  have hFH : ∀ (ν : Fin 1 ⊕ Fin 3) (w : FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra),
      (FermionJetAlgebra.repLorentzGroup.tprod HiggsJetAlgebra.repLorentzGroup) Λ
        ((TensorProduct.map (FermionicAlgebra.jetDeriv (V := FermionSpace) ν)
            (LinearMap.id (M := HiggsJetAlgebra))
          + TensorProduct.map (LinearMap.id (M := FermionJetAlgebra))
            (BosonicAlgebra.jetDeriv (V := HiggsVec) ν)) w)
      = ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a ν : ℝ) : ℂ) •
          (TensorProduct.map (FermionicAlgebra.jetDeriv (V := FermionSpace) a)
            (LinearMap.id (M := HiggsJetAlgebra))
            + TensorProduct.map (LinearMap.id (M := FermionJetAlgebra))
              (BosonicAlgebra.jetDeriv (V := HiggsVec) a))
          ((FermionJetAlgebra.repLorentzGroup.tprod
            HiggsJetAlgebra.repLorentzGroup) Λ w) := fun ν w =>
    tprod_deriv_sum _ _ _ _ _ Λ ν
      (fun κ z => FermionicAlgebra.repLorentzGroup_jetDeriv _ Λ κ z)
      (fun κ z => BosonicAlgebra.repLorentzGroup_jetDeriv _ Λ κ z) w
  refine (congrArg (fun (L : JetAlgebra →ₗ[ℂ] JetAlgebra) => repLorentzGroup Λ (L x))
    (e μ).symm).trans ((tprod_deriv_sum _ _ _ _ _ Λ μ hFH
      (fun κ z => GaugeJetAlgebra.complexRepLorentzGroup_jetDeriv Λ κ z) x).trans
    (Finset.sum_congr rfl fun a _ => congrArg
      (fun (L : JetAlgebra →ₗ[ℂ] JetAlgebra) =>
        (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • L (repLorentzGroup Λ x))
      (e a)))

/-- The total derivatives on the jet algebra form a Lorentz derivative. -/
instance instIsLorentzDeriv : Lorentz.IsLorentzDeriv repLorentzGroup jetDeriv where
  rep_deriv := repLorentzGroup_jetDeriv _ _ _

end JetAlgebra

end StandardModel
