/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.DownSinglet
public import Physlib.Particles.StandardModel.Fermions.UpSinglet
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.Basic
public import Physlib.Mathematics.ConjModule
public import Physlib.Relativity.IsLorentzDeriv
public import Mathlib.Algebra.Polynomial.AlgebraMap
/-!
# The fermion sector

The three families of each fermion species and their conjugates, indexed by ordered
tuples of covariant-derivative directions, form a *fermion sector* of the algebra `B`
when: each family transforms under the global gauge group through the dual of the
species' gauge representation (the conjugate representation for the barred fields),
under the Lorentz group as the covariant derivatives of the species' Lorentz
representation, and each tower is a `massWeightPoly`-eigenvector of weight
`3 + 2 * n` (mass dimension `3/2 + n`).

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

/-- The ten fermion families and their covariant derivatives as a sector of the
  algebra `B`: gauge transformation through the dual of the species representations
  (conjugate for the barred fields), the Lorentz transformation of the towers, and
  the mass weights `3 + 2 * n`. -/
structure IsFermionSector (B : Type) [Ring B] [Algebra ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (repGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
      repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂)
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
      repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂)
    (d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B)
    (bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B)
    (u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B)
    (baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B)
    (Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B)
    (barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B)
    (L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B)
    (barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B)
    (e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B)
    (bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B)
    (massWeightPoly : B →ₐ[ℂ] Polynomial B) : Prop where
  repGauge_d : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet),
    repGauge g (d i l φ) = d i l (DownSinglet.repGaugeGroupI.dual g φ)
  repGauge_bard : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet)),
    repGauge g (bard i l φ) = bard i l (DownSinglet.repGaugeGroupI.conj.dual g φ)
  repGauge_u : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet),
    repGauge g (u i l φ) = u i l (UpSinglet.repGaugeGroupI.dual g φ)
  repGauge_baru : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet)),
    repGauge g (baru i l φ) = baru i l (UpSinglet.repGaugeGroupI.conj.dual g φ)
  repGauge_Q : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet),
    repGauge g (Q i l φ) = Q i l (QuarkDoublet.repGaugeGroupI.dual g φ)
  repGauge_barQ : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
    repGauge g (barQ i l φ) = barQ i l (QuarkDoublet.repGaugeGroupI.conj.dual g φ)
  repGauge_L : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet),
    repGauge g (L i l φ) = L i l (LeptonDoublet.repGaugeGroupI.dual g φ)
  repGauge_barL : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
    repGauge g (barL i l φ) = barL i l (LeptonDoublet.repGaugeGroupI.conj.dual g φ)
  repGauge_e : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonSinglet),
    repGauge g (e i l φ) = e i l (LeptonSinglet.repGaugeGroupI.dual g φ)
  repGauge_bare : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
    repGauge g (bare i l φ) = bare i l (LeptonSinglet.repGaugeGroupI.conj.dual g φ)
  repLorentz_d : ∀ i, IsLorentzCovDerivTransforms repLorentz
    DownSinglet.repLorentzGroup (d i)
  repLorentz_bard : ∀ i, IsLorentzCovDerivTransforms repLorentz
    DownSinglet.repLorentzGroup.conj (bard i)
  repLorentz_u : ∀ i, IsLorentzCovDerivTransforms repLorentz
    UpSinglet.repLorentzGroup (u i)
  repLorentz_baru : ∀ i, IsLorentzCovDerivTransforms repLorentz
    UpSinglet.repLorentzGroup.conj (baru i)
  repLorentz_Q : ∀ i, IsLorentzCovDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup (Q i)
  repLorentz_barQ : ∀ i, IsLorentzCovDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup.conj (barQ i)
  repLorentz_L : ∀ i, IsLorentzCovDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup (L i)
  repLorentz_barL : ∀ i, IsLorentzCovDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup.conj (barL i)
  repLorentz_e : ∀ i, IsLorentzCovDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup (e i)
  repLorentz_bare : ∀ i, IsLorentzCovDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup.conj (bare i)
  massWeight_d : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (d i l φ) = Polynomial.monomial (3 + 2 * n) (d i l φ)
  massWeight_bard : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (bard i l φ) = Polynomial.monomial (3 + 2 * n) (bard i l φ)
  massWeight_u : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (u i l φ) = Polynomial.monomial (3 + 2 * n) (u i l φ)
  massWeight_baru : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (baru i l φ) = Polynomial.monomial (3 + 2 * n) (baru i l φ)
  massWeight_Q : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (Q i l φ) = Polynomial.monomial (3 + 2 * n) (Q i l φ)
  massWeight_barQ : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (barQ i l φ) = Polynomial.monomial (3 + 2 * n) (barQ i l φ)
  massWeight_L : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (L i l φ) = Polynomial.monomial (3 + 2 * n) (L i l φ)
  massWeight_barL : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (barL i l φ) = Polynomial.monomial (3 + 2 * n) (barL i l φ)
  massWeight_e : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (e i l φ) = Polynomial.monomial (3 + 2 * n) (e i l φ)
  massWeight_bare : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (bare i l φ) = Polynomial.monomial (3 + 2 * n) (bare i l φ)
  -- Any two fermionic towers anticommute. On the diagonal (same species, family,
  -- derivative slots and dual vector) this forces the square of every fermionic
  -- symbol to vanish, whenever `2` is invertible in `B`.
  d_anticomm_d : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ DownSinglet),
    d i l φ * d j l' φ' = -(d j l' φ' * d i l φ)
  d_anticomm_bard : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    d i l φ * bard j l' φ' = -(bard j l' φ' * d i l φ)
  d_anticomm_u : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ UpSinglet),
    d i l φ * u j l' φ' = -(u j l' φ' * d i l φ)
  d_anticomm_baru : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    d i l φ * baru j l' φ' = -(baru j l' φ' * d i l φ)
  d_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ QuarkDoublet),
    d i l φ * Q j l' φ' = -(Q j l' φ' * d i l φ)
  d_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    d i l φ * barQ j l' φ' = -(barQ j l' φ' * d i l φ)
  d_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    d i l φ * L j l' φ' = -(L j l' φ' * d i l φ)
  d_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    d i l φ * barL j l' φ' = -(barL j l' φ' * d i l φ)
  d_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    d i l φ * e j l' φ' = -(e j l' φ' * d i l φ)
  d_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    d i l φ * bare j l' φ' = -(bare j l' φ' * d i l φ)
  bard_anticomm_bard : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    bard i l φ * bard j l' φ' = -(bard j l' φ' * bard i l φ)
  bard_anticomm_u : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ UpSinglet),
    bard i l φ * u j l' φ' = -(u j l' φ' * bard i l φ)
  bard_anticomm_baru : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    bard i l φ * baru j l' φ' = -(baru j l' φ' * bard i l φ)
  bard_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ QuarkDoublet),
    bard i l φ * Q j l' φ' = -(Q j l' φ' * bard i l φ)
  bard_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    bard i l φ * barQ j l' φ' = -(barQ j l' φ' * bard i l φ)
  bard_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ LeptonDoublet),
    bard i l φ * L j l' φ' = -(L j l' φ' * bard i l φ)
  bard_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    bard i l φ * barL j l' φ' = -(barL j l' φ' * bard i l φ)
  bard_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ LeptonSinglet),
    bard i l φ * e j l' φ' = -(e j l' φ' * bard i l φ)
  bard_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    bard i l φ * bare j l' φ' = -(bare j l' φ' * bard i l φ)
  u_anticomm_u : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ UpSinglet),
    u i l φ * u j l' φ' = -(u j l' φ' * u i l φ)
  u_anticomm_baru : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    u i l φ * baru j l' φ' = -(baru j l' φ' * u i l φ)
  u_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ QuarkDoublet),
    u i l φ * Q j l' φ' = -(Q j l' φ' * u i l φ)
  u_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    u i l φ * barQ j l' φ' = -(barQ j l' φ' * u i l φ)
  u_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    u i l φ * L j l' φ' = -(L j l' φ' * u i l φ)
  u_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    u i l φ * barL j l' φ' = -(barL j l' φ' * u i l φ)
  u_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    u i l φ * e j l' φ' = -(e j l' φ' * u i l φ)
  u_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    u i l φ * bare j l' φ' = -(bare j l' φ' * u i l φ)
  baru_anticomm_baru : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    baru i l φ * baru j l' φ' = -(baru j l' φ' * baru i l φ)
  baru_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ QuarkDoublet),
    baru i l φ * Q j l' φ' = -(Q j l' φ' * baru i l φ)
  baru_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    baru i l φ * barQ j l' φ' = -(barQ j l' φ' * baru i l φ)
  baru_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ LeptonDoublet),
    baru i l φ * L j l' φ' = -(L j l' φ' * baru i l φ)
  baru_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    baru i l φ * barL j l' φ' = -(barL j l' φ' * baru i l φ)
  baru_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ LeptonSinglet),
    baru i l φ * e j l' φ' = -(e j l' φ' * baru i l φ)
  baru_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    baru i l φ * bare j l' φ' = -(bare j l' φ' * baru i l φ)
  Q_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ QuarkDoublet),
    Q i l φ * Q j l' φ' = -(Q j l' φ' * Q i l φ)
  Q_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Q i l φ * barQ j l' φ' = -(barQ j l' φ' * Q i l φ)
  Q_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    Q i l φ * L j l' φ' = -(L j l' φ' * Q i l φ)
  Q_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Q i l φ * barL j l' φ' = -(barL j l' φ' * Q i l φ)
  Q_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    Q i l φ * e j l' φ' = -(e j l' φ' * Q i l φ)
  Q_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Q i l φ * bare j l' φ' = -(bare j l' φ' * Q i l φ)
  barQ_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    barQ i l φ * barQ j l' φ' = -(barQ j l' φ' * barQ i l φ)
  barQ_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ LeptonDoublet),
    barQ i l φ * L j l' φ' = -(L j l' φ' * barQ i l φ)
  barQ_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    barQ i l φ * barL j l' φ' = -(barL j l' φ' * barQ i l φ)
  barQ_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ LeptonSinglet),
    barQ i l φ * e j l' φ' = -(e j l' φ' * barQ i l φ)
  barQ_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    barQ i l φ * bare j l' φ' = -(bare j l' φ' * barQ i l φ)
  L_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    L i l φ * L j l' φ' = -(L j l' φ' * L i l φ)
  L_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    L i l φ * barL j l' φ' = -(barL j l' φ' * L i l φ)
  L_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    L i l φ * e j l' φ' = -(e j l' φ' * L i l φ)
  L_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    L i l φ * bare j l' φ' = -(bare j l' φ' * L i l φ)
  barL_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonDoublet))
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    barL i l φ * barL j l' φ' = -(barL j l' φ' * barL i l φ)
  barL_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonDoublet))
      (φ' : Module.Dual ℂ LeptonSinglet),
    barL i l φ * e j l' φ' = -(e j l' φ' * barL i l φ)
  barL_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonDoublet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    barL i l φ * bare j l' φ' = -(bare j l' φ' * barL i l φ)
  e_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonSinglet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    e i l φ * e j l' φ' = -(e j l' φ' * e i l φ)
  e_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    e i l φ * bare j l' φ' = -(bare j l' φ' * e i l φ)
  bare_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    bare i l φ * bare j l' φ' = -(bare j l' φ' * bare i l φ)

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
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
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

set_option linter.unusedVariables false in
/-- The algebra generated by the ten fermion families and all their covariant
  derivatives. -/
def fermionAlgebra (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly) : Subalgebra ℂ B :=
  Algebra.adjoin ℂ
    (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3),
      Set.range (d i l) ∪ Set.range (bard i l) ∪
      Set.range (u i l) ∪ Set.range (baru i l) ∪
      Set.range (Q i l) ∪ Set.range (barQ i l) ∪
      Set.range (L i l) ∪ Set.range (barL i l) ∪
      Set.range (e i l) ∪ Set.range (bare i l))


/-!

## The fermion-derivative submodules

-/

set_option linter.unusedVariables false in
/-- The submodule of `B` generated by the fermion symbols carrying exactly `n`
  covariant derivatives: the join, over the families and derivative slots, of the
  ranges of the ten species' symbol maps. -/
def derivSubmodule (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly) (n : ℕ) : Submodule ℂ B :=
  ⨆ (i : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3),
    LinearMap.range (d i l) ⊔ LinearMap.range (bard i l) ⊔
    LinearMap.range (u i l) ⊔ LinearMap.range (baru i l) ⊔
    LinearMap.range (Q i l) ⊔ LinearMap.range (barQ i l) ⊔
    LinearMap.range (L i l) ⊔ LinearMap.range (barL i l) ⊔
    LinearMap.range (e i l) ⊔ LinearMap.range (bare i l)

/-- The derivative submodule as the span of the fermion symbol values. -/
lemma derivSubmodule_eq_span (n : ℕ) :
    h.derivSubmodule n = Submodule.span ℂ
      (⋃ (i : Fin 3) (l : Fin n → Fin 1 ⊕ Fin 3),
        Set.range (d i l) ∪ Set.range (bard i l) ∪
        Set.range (u i l) ∪ Set.range (baru i l) ∪
        Set.range (Q i l) ∪ Set.range (barQ i l) ∪
        Set.range (L i l) ∪ Set.range (barL i l) ∪
        Set.range (e i l) ∪ Set.range (bare i l)) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr fun x hx => ?_)
  · rw [derivSubmodule]
    refine iSup_le fun i => iSup_le fun l => sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
      (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (⟨φ, rfl⟩)))))))))⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨φ, rfl⟩))))))))⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨φ, rfl⟩)))))))⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨φ, rfl⟩))))))⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨φ, rfl⟩)))))⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨φ, rfl⟩))))⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨φ, rfl⟩)))⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨φ, rfl⟩))⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_left _ (Set.mem_union_right _ ⟨φ, rfl⟩)⟩⟩)
    · rintro x ⟨φ, rfl⟩
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨l,
        Set.mem_union_right _ ⟨φ, rfl⟩⟩⟩)
  · simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hx
    obtain ⟨i, l, (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
        ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩)⟩ := hx
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (⟨φ, rfl⟩)))))))))))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨φ, rfl⟩))))))))))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨φ, rfl⟩)))))))))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨φ, rfl⟩))))))))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨φ, rfl⟩)))))))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨φ, rfl⟩))))))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨φ, rfl⟩)))))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨φ, rfl⟩))))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨φ, rfl⟩)))
    · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem l
        (Submodule.mem_sup_right ⟨φ, rfl⟩))

/-- Any two elements of the fermion derivative submodules anticommute: the pairwise
  anticommutation of the symbols extends bilinearly to the spans. -/
lemma anticomm_of_mem_derivSubmodule {n m : ℕ} {x y : B}
    (hx : x ∈ h.derivSubmodule n) (hy : y ∈ h.derivSubmodule m) :
    x * y = -(y * x) := by
  rw [derivSubmodule_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem a ha =>
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at ha
    obtain ⟨i, l, (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
        ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩)⟩ := ha
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · exact h.d_anticomm_d i i' l l' φ φ'
        · exact h.d_anticomm_bard i i' l l' φ φ'
        · exact h.d_anticomm_u i i' l l' φ φ'
        · exact h.d_anticomm_baru i i' l l' φ φ'
        · exact h.d_anticomm_Q i i' l l' φ φ'
        · exact h.d_anticomm_barQ i i' l l' φ φ'
        · exact h.d_anticomm_L i i' l l' φ φ'
        · exact h.d_anticomm_barL i i' l l' φ φ'
        · exact h.d_anticomm_e i i' l l' φ φ'
        · exact h.d_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_bard i' i l' l φ' φ, neg_neg]
        · exact h.bard_anticomm_bard i i' l l' φ φ'
        · exact h.bard_anticomm_u i i' l l' φ φ'
        · exact h.bard_anticomm_baru i i' l l' φ φ'
        · exact h.bard_anticomm_Q i i' l l' φ φ'
        · exact h.bard_anticomm_barQ i i' l l' φ φ'
        · exact h.bard_anticomm_L i i' l l' φ φ'
        · exact h.bard_anticomm_barL i i' l l' φ φ'
        · exact h.bard_anticomm_e i i' l l' φ φ'
        · exact h.bard_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_u i' i l' l φ' φ, neg_neg]
        · rw [h.bard_anticomm_u i' i l' l φ' φ, neg_neg]
        · exact h.u_anticomm_u i i' l l' φ φ'
        · exact h.u_anticomm_baru i i' l l' φ φ'
        · exact h.u_anticomm_Q i i' l l' φ φ'
        · exact h.u_anticomm_barQ i i' l l' φ φ'
        · exact h.u_anticomm_L i i' l l' φ φ'
        · exact h.u_anticomm_barL i i' l l' φ φ'
        · exact h.u_anticomm_e i i' l l' φ φ'
        · exact h.u_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_baru i' i l' l φ' φ, neg_neg]
        · rw [h.bard_anticomm_baru i' i l' l φ' φ, neg_neg]
        · rw [h.u_anticomm_baru i' i l' l φ' φ, neg_neg]
        · exact h.baru_anticomm_baru i i' l l' φ φ'
        · exact h.baru_anticomm_Q i i' l l' φ φ'
        · exact h.baru_anticomm_barQ i i' l l' φ φ'
        · exact h.baru_anticomm_L i i' l l' φ φ'
        · exact h.baru_anticomm_barL i i' l l' φ φ'
        · exact h.baru_anticomm_e i i' l l' φ φ'
        · exact h.baru_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_Q i' i l' l φ' φ, neg_neg]
        · rw [h.bard_anticomm_Q i' i l' l φ' φ, neg_neg]
        · rw [h.u_anticomm_Q i' i l' l φ' φ, neg_neg]
        · rw [h.baru_anticomm_Q i' i l' l φ' φ, neg_neg]
        · exact h.Q_anticomm_Q i i' l l' φ φ'
        · exact h.Q_anticomm_barQ i i' l l' φ φ'
        · exact h.Q_anticomm_L i i' l l' φ φ'
        · exact h.Q_anticomm_barL i i' l l' φ φ'
        · exact h.Q_anticomm_e i i' l l' φ φ'
        · exact h.Q_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_barQ i' i l' l φ' φ, neg_neg]
        · rw [h.bard_anticomm_barQ i' i l' l φ' φ, neg_neg]
        · rw [h.u_anticomm_barQ i' i l' l φ' φ, neg_neg]
        · rw [h.baru_anticomm_barQ i' i l' l φ' φ, neg_neg]
        · rw [h.Q_anticomm_barQ i' i l' l φ' φ, neg_neg]
        · exact h.barQ_anticomm_barQ i i' l l' φ φ'
        · exact h.barQ_anticomm_L i i' l l' φ φ'
        · exact h.barQ_anticomm_barL i i' l l' φ φ'
        · exact h.barQ_anticomm_e i i' l l' φ φ'
        · exact h.barQ_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_L i' i l' l φ' φ, neg_neg]
        · rw [h.bard_anticomm_L i' i l' l φ' φ, neg_neg]
        · rw [h.u_anticomm_L i' i l' l φ' φ, neg_neg]
        · rw [h.baru_anticomm_L i' i l' l φ' φ, neg_neg]
        · rw [h.Q_anticomm_L i' i l' l φ' φ, neg_neg]
        · rw [h.barQ_anticomm_L i' i l' l φ' φ, neg_neg]
        · exact h.L_anticomm_L i i' l l' φ φ'
        · exact h.L_anticomm_barL i i' l l' φ φ'
        · exact h.L_anticomm_e i i' l l' φ φ'
        · exact h.L_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_barL i' i l' l φ' φ, neg_neg]
        · rw [h.bard_anticomm_barL i' i l' l φ' φ, neg_neg]
        · rw [h.u_anticomm_barL i' i l' l φ' φ, neg_neg]
        · rw [h.baru_anticomm_barL i' i l' l φ' φ, neg_neg]
        · rw [h.Q_anticomm_barL i' i l' l φ' φ, neg_neg]
        · rw [h.barQ_anticomm_barL i' i l' l φ' φ, neg_neg]
        · rw [h.L_anticomm_barL i' i l' l φ' φ, neg_neg]
        · exact h.barL_anticomm_barL i i' l l' φ φ'
        · exact h.barL_anticomm_e i i' l l' φ φ'
        · exact h.barL_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_e i' i l' l φ' φ, neg_neg]
        · rw [h.bard_anticomm_e i' i l' l φ' φ, neg_neg]
        · rw [h.u_anticomm_e i' i l' l φ' φ, neg_neg]
        · rw [h.baru_anticomm_e i' i l' l φ' φ, neg_neg]
        · rw [h.Q_anticomm_e i' i l' l φ' φ, neg_neg]
        · rw [h.barQ_anticomm_e i' i l' l φ' φ, neg_neg]
        · rw [h.L_anticomm_e i' i l' l φ' φ, neg_neg]
        · rw [h.barL_anticomm_e i' i l' l φ' φ, neg_neg]
        · exact h.e_anticomm_e i i' l l' φ φ'
        · exact h.e_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
    · induction hy using Submodule.span_induction with
      | mem b hb =>
        simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hb
        obtain ⟨i', l', (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)⟩ := hb
        · rw [h.d_anticomm_bare i' i l' l φ' φ, neg_neg]
        · rw [h.bard_anticomm_bare i' i l' l φ' φ, neg_neg]
        · rw [h.u_anticomm_bare i' i l' l φ' φ, neg_neg]
        · rw [h.baru_anticomm_bare i' i l' l φ' φ, neg_neg]
        · rw [h.Q_anticomm_bare i' i l' l φ' φ, neg_neg]
        · rw [h.barQ_anticomm_bare i' i l' l φ' φ, neg_neg]
        · rw [h.L_anticomm_bare i' i l' l φ' φ, neg_neg]
        · rw [h.barL_anticomm_bare i' i l' l φ' φ, neg_neg]
        · rw [h.e_anticomm_bare i' i l' l φ' φ, neg_neg]
        · exact h.bare_anticomm_bare i i' l l' φ φ'
      | zero => simp
      | add b₁ b₂ _ _ ih₁ ih₂ => rw [mul_add, ih₁, ih₂, add_mul, neg_add]
      | smul c b _ ih => rw [mul_smul_comm, ih, smul_mul_assoc, smul_neg]
  | zero => simp
  | add a₁ a₂ _ _ ih₁ ih₂ => rw [add_mul, ih₁, ih₂, mul_add, neg_add]
  | smul c a _ ih => rw [smul_mul_assoc, ih, mul_smul_comm, smul_neg]

/-- The fermion derivative submodules commute with one another as submodules: the
  sign from anticommutation is absorbed by the span. -/
lemma derivSubmodule_mul_comm (n m : ℕ) :
    h.derivSubmodule n * h.derivSubmodule m = h.derivSubmodule m * h.derivSubmodule n := by
  refine le_antisymm ?_ ?_ <;>
  · rw [Submodule.mul_le]
    intro x hx y hy
    rw [h.anticomm_of_mem_derivSubmodule hx hy]
    exact Submodule.neg_mem _ (Submodule.mul_mem_mul hy hx)

end IsFermionSector

end StandardModel
