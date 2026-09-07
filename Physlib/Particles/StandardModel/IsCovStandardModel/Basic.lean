/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.Fermions.DownSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.UpSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Symmeterized
public import Physlib.Particles.StandardModel.HiggsBoson.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.IsHiggsSector.Basic
public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.Basic
public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.Basic
/-!
# The algebra valued Standard model

The basic idea here is to just reduce things
down to the covariant version.
In the covariant version we will do the work with
the invariants.

This file carries the structure `IsCovStandardModel` itself — the covariant fields
with their gauge, Lorentz, mass-weight and commutation properties — together with the
algebra they generate. The covariant generators of that algebra are in
`IsCovStandardModel.Generators`, and the mass-weight grading in
`IsCovStandardModel.MassWeight`.

## The sectors

Every covariant generator belongs to one of three classes — **gauge** (the
field-strength towers), **Higgs** (the Higgs towers and their conjugates) and
**fermion** (the ten families and their conjugates) — and a word in the generators
realises a set of classes.  The weight-`w` part of the algebra therefore splits over
the eight subsets of the three classes; the splitting itself is
[`Sectors.lean`](Sectors.lean), and each subset is developed in its own file:

| classes realised | sector | file |
| --- | --- | --- |
| `∅` | the scalars, present at weight zero only | — |
| `{gauge}` | `IsGaugeSector` | [`IsGaugeSector/MassWeight/Basic.lean`](../IsGaugeSector/MassWeight/Basic.lean) |
| `{higgs}` | `IsHiggsSector` | [`IsHiggsSector/MassWeight/Basic.lean`](../IsHiggsSector/MassWeight/Basic.lean) |
| `{fermion}` | `IsFermionSector` | [`IsFermionSector/MassWeight/Basic.lean`](../IsFermionSector/MassWeight/Basic.lean) |
| `{gauge, higgs}` | the gauge–Higgs sector | [`GaugeHiggsSector/Basic.lean`](GaugeHiggsSector/Basic.lean) |
| `{gauge, fermion}` | the gauge–fermion sector | [`FermionGaugeSector/Basic.lean`](FermionGaugeSector/Basic.lean) |
| `{higgs, fermion}` | the Yukawa sector | [`YukawaSector/Basic.lean`](YukawaSector/Basic.lean) |
| `{gauge, higgs, fermion}` | the mixed sector | [`MixedSector/Basic.lean`](MixedSector/Basic.lean) |

The weight-`w` part of a pure sector is exactly the mass-weight submodule of the
corresponding sector structure; the mixed sectors are bounded by products of those.

Because the lightest generator of each class has mass weight four (gauge), two
(Higgs) and three (fermion), a sector is empty below the sum of the minimum weights
of the classes it contains.  In particular the mixed sector is empty below weight
nine, so no Standard-Model term of mass dimension at most four involves all three
kinds of field at once.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

structure IsCovStandardModel (B : Type) [Ring B] [Algebra ℂ B]
    -- The representations, acting by algebra maps
    (repGauge : Representation ℂ GaugeGroupI B)
    (repGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)
    -- The mass weights
    (massWeightPoly : B →ₐ[ℂ] Polynomial B)
    -- The Higgs fields + covariant derivatives
    (H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B)
    (barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B)
    -- The field strength + covariant derivatives derivatives
    (F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
      Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    -- Three families of down-type quarks + derivatives + conjugates
    (d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B)
    (bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B)
    -- Three families of up-type quarks + derivatives + conjugates
    (u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B)
    (baru :{n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B)
    -- Three families of quark doublets + derivatives + conjugates
    (Q : {n : ℕ} →Fin 3 → (Fin n → Fin 1 ⊕ Fin 3)→ Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B)
    (barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B)
    -- Three families of lepton doublets + derivatives + conjugates
    (L : {n : ℕ} → Fin 3  → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B)
    (barL : {n : ℕ} → Fin 3 →  (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B)
    -- Three families of lepton singlets + derivatives + conjugates
    (e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B)
    (bare : {n : ℕ} →  Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B)
    : Prop where
  isHiggsSector : IsHiggsSector B repGauge repGauge_mul repLorentz repLorentz_mul
    (fun n l => H l) (fun n l => barH l) massWeightPoly
  -- *The gauge sector*
  -- The field strength with its covariant derivatives: gauge transformation through
  -- the adjoint action, the Lorentz transformation of the towers with two explicit
  -- covector indices, and the mass weights `2 * (2 + n)`.
  isGaugeSector : IsGaugeSector B repGauge repGauge_mul repLorentz repLorentz_mul
    F massWeightPoly
  -- *The fermion sector*
  -- The ten fermion families with their covariant derivatives: gauge transformation
  -- through the dual of the species representations (conjugate for the barred
  -- fields), the Lorentz transformation of the towers, and the mass weights
  -- `3 + 2 * n`.
  isFermionSector : IsFermionSector B repGauge repGauge_mul repLorentz repLorentz_mul
    d bard u baru Q barQ L barL e bare massWeightPoly
  -- **The cross-sector commutation rules**
  -- The within-sector rules live in the sector structures; across sectors, the
  -- bosonic towers commute with everything.
  -- The gauge sector is bosonic: every field-strength tower commutes with the Higgs
  -- and fermion towers.
  F_comm_H : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec),
    Commute (F l μ ν ψ) (H l' φ)
  F_comm_barH : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (F l μ ν ψ) (barH l' φ)
  F_comm_d : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ DownSinglet),
    Commute (F l μ ν ψ) (d i l' φ)
  F_comm_bard : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (F l μ ν ψ) (bard i l' φ)
  F_comm_u : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ UpSinglet),
    Commute (F l μ ν ψ) (u i l' φ)
  F_comm_baru : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (F l μ ν ψ) (baru i l' φ)
  F_comm_Q : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ QuarkDoublet),
    Commute (F l μ ν ψ) (Q i l' φ)
  F_comm_barQ : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (F l μ ν ψ) (barQ i l' φ)
  F_comm_L : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ LeptonDoublet),
    Commute (F l μ ν ψ) (L i l' φ)
  F_comm_barL : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (F l μ ν ψ) (barL i l' φ)
  F_comm_e : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ LeptonSinglet),
    Commute (F l μ ν ψ) (e i l' φ)
  F_comm_bare : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (F l μ ν ψ) (bare i l' φ)
  -- The Higgs sector is bosonic: the Higgs towers and their conjugates commute
  -- with every fermion.
  H_comm_d : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ DownSinglet),
    Commute (H l φ) (d i l' φ')
  H_comm_bard : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (H l φ) (bard i l' φ')
  H_comm_u : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ UpSinglet),
    Commute (H l φ) (u i l' φ')
  H_comm_baru : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (H l φ) (baru i l' φ')
  H_comm_Q : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ QuarkDoublet),
    Commute (H l φ) (Q i l' φ')
  H_comm_barQ : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (H l φ) (barQ i l' φ')
  H_comm_L : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ LeptonDoublet),
    Commute (H l φ) (L i l' φ')
  H_comm_barL : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (H l φ) (barL i l' φ')
  H_comm_e : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ LeptonSinglet),
    Commute (H l φ) (e i l' φ')
  H_comm_bare : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (H l φ) (bare i l' φ')
  barH_comm_d : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ DownSinglet),
    Commute (barH l φ) (d i l' φ')
  barH_comm_bard : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (barH l φ) (bard i l' φ')
  barH_comm_u : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ UpSinglet),
    Commute (barH l φ) (u i l' φ')
  barH_comm_baru : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (barH l φ) (baru i l' φ')
  barH_comm_Q : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ QuarkDoublet),
    Commute (barH l φ) (Q i l' φ')
  barH_comm_barQ : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (barH l φ) (barQ i l' φ')
  barH_comm_L : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ LeptonDoublet),
    Commute (barH l φ) (L i l' φ')
  barH_comm_barL : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (barH l φ) (barL i l' φ')
  barH_comm_e : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ LeptonSinglet),
    Commute (barH l φ) (e i l' φ')
  barH_comm_bare : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (barH l φ) (bare i l' φ')

namespace IsCovStandardModel

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare)

/-- Gauge transformations act on `B` by algebra maps: dot-notation access to the
  multiplicativity hypothesis of the structure. -/
lemma repGauge_mul (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare) :
    ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂ := hrepGauge_mul

/-- Lorentz transformations act on `B` by algebra maps: dot-notation access to the
  multiplicativity hypothesis of the structure. -/
lemma repLorentz_mul (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare) :
    ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂ := hrepLorentz_mul

/-!

## A. The gauge and Lorentz actions

The two actions on the algebra are multiplicative, so each is a unital algebra
automorphism; in particular each fixes the unit.

-/

include h in
/-- The multiplicative gauge action fixes the unit of the algebra. -/
lemma repGauge_one (g : GaugeGroupI) : repGauge g (1 : B) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, repGauge g u = 1 :=
    ⟨repGauge g⁻¹ 1, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one repGauge,
        Module.End.one_apply]⟩
  have h1 := h.repGauge_mul g u 1
  rw [mul_one, hu, one_mul] at h1
  exact h1.symm

include h in
/-- The multiplicative Lorentz action fixes the unit of the algebra. -/
lemma repLorentz_one (Λ : SL(2,ℂ)) : repLorentz Λ (1 : B) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, repLorentz Λ u = 1 :=
    ⟨repLorentz Λ⁻¹ 1, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one repLorentz,
        Module.End.one_apply]⟩
  have h1 := h.repLorentz_mul Λ u 1
  rw [mul_one, hu, one_mul] at h1
  exact h1.symm

/-!

## B. The field algebra

-/

/-- The algebra generated by all the covariant fields of the Standard Model: the
  covariant-derivative towers of the field strength, of the Higgs and its conjugate,
  and of the three families of each fermion species with their conjugates. -/
def fieldAlgebra (_ : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare) : Subalgebra ℂ B :=
  Algebra.adjoin ℂ
    ((⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        Set.range (F l μ ν)) ∪
      (⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3), Set.range (H l) ∪ Set.range (barH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3),
        Set.range (d i l) ∪ Set.range (bard i l) ∪
        Set.range (u i l) ∪ Set.range (baru i l) ∪
        Set.range (Q i l) ∪ Set.range (barQ i l) ∪
        Set.range (L i l) ∪ Set.range (barL i l) ∪
        Set.range (e i l) ∪ Set.range (bare i l)))

/-!

### B.1. Basic commutation relations

-/

lemma F_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℝ GaugeAlgebra) (x : B) (hx : x ∈ h.fieldAlgebra) :
    F l μ ν φ * x = x * F l μ ν φ := by
  rw [fieldAlgebra] at hx
  refine (IsGaugeField.commute_of_mem_adjoin (y := F l μ ν φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact (h.isGaugeSector.F_comm_F l μ ν φ l' μ' ν' ψ).symm
  · exact (h.F_comm_H l μ ν φ l' φ').symm
  · exact (h.F_comm_barH l μ ν φ l' φ').symm
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (h.F_comm_d l μ ν φ i l' φ').symm
    · exact (h.F_comm_bard l μ ν φ i l' φ').symm
    · exact (h.F_comm_u l μ ν φ i l' φ').symm
    · exact (h.F_comm_baru l μ ν φ i l' φ').symm
    · exact (h.F_comm_Q l μ ν φ i l' φ').symm
    · exact (h.F_comm_barQ l μ ν φ i l' φ').symm
    · exact (h.F_comm_L l μ ν φ i l' φ').symm
    · exact (h.F_comm_barL l μ ν φ i l' φ').symm
    · exact (h.F_comm_e l μ ν φ i l' φ').symm
    · exact (h.F_comm_bare l μ ν φ i l' φ').symm

lemma H_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℂ HiggsVec) (x : B) (hx : x ∈ h.fieldAlgebra) :
    H l φ * x = x * H l φ := by
  rw [fieldAlgebra] at hx
  refine (IsGaugeField.commute_of_mem_adjoin (y := H l φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact h.F_comm_H l' μ' ν' ψ l φ
  · exact h.isHiggsSector.H_comm_H φ' φ _ _ l' l
  · exact (h.isHiggsSector.H_comm_barH φ φ' _ _ l l').symm
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (h.H_comm_d l φ i l' φ').symm
    · exact (h.H_comm_bard l φ i l' φ').symm
    · exact (h.H_comm_u l φ i l' φ').symm
    · exact (h.H_comm_baru l φ i l' φ').symm
    · exact (h.H_comm_Q l φ i l' φ').symm
    · exact (h.H_comm_barQ l φ i l' φ').symm
    · exact (h.H_comm_L l φ i l' φ').symm
    · exact (h.H_comm_barL l φ i l' φ').symm
    · exact (h.H_comm_e l φ i l' φ').symm
    · exact (h.H_comm_bare l φ i l' φ').symm

lemma barH_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (x : B) (hx : x ∈ h.fieldAlgebra) :
    barH l φ * x = x * barH l φ := by
  rw [fieldAlgebra] at hx
  refine (IsGaugeField.commute_of_mem_adjoin (y := barH l φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact h.F_comm_barH l' μ' ν' ψ l φ
  · exact h.isHiggsSector.H_comm_barH φ' φ _ _ l' l
  · exact h.isHiggsSector.barH_comm_barH φ' φ _ _ l' l
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (h.barH_comm_d l φ i l' φ').symm
    · exact (h.barH_comm_bard l φ i l' φ').symm
    · exact (h.barH_comm_u l φ i l' φ').symm
    · exact (h.barH_comm_baru l φ i l' φ').symm
    · exact (h.barH_comm_Q l φ i l' φ').symm
    · exact (h.barH_comm_barQ l φ i l' φ').symm
    · exact (h.barH_comm_L l φ i l' φ').symm
    · exact (h.barH_comm_barL l φ i l' φ').symm
    · exact (h.barH_comm_e l φ i l' φ').symm
    · exact (h.barH_comm_bare l φ i l' φ').symm

end IsCovStandardModel

end StandardModel
