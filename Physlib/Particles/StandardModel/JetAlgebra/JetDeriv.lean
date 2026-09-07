/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.JetDeriv
/-!
# The total derivative on the jet algebra of the Standard Model

## i. Overview

The formal total derivative on the jet algebra of the Standard Model is the sum of the
total derivatives of the three sector algebras, each acting on its own tensor factor. It
obeys the Leibniz rule, its components commute, and through each sector inclusion it
restricts to that sector's own derivative — for a single direction and for an iterated
multiset of directions alike.

The Leibniz rule and the commutation are assembled from the sector facts through abstract
lemmas proved at small types, instantiated in term mode — rewriting inside the full tensor
product is prohibitively slow.

## ii. Key results

- `JetAlgebra.jetDeriv` : the formal total derivative.
- `JetAlgebra.jetDeriv_mul` : the Leibniz rule.
- `JetAlgebra.jetDeriv_comm` : the total derivatives commute.
- `JetAlgebra.jetDeriv_includeGauge`, `jetDeriv_includeFermion`, `jetDeriv_includeHiggs` :
  the restrictions to the three sectors.
- `JetAlgebra.iteratedD_includeFermion`, `iteratedD_includeHiggs` : the same for the
  iterated derivative.

## iii. Table of contents

- A. The formal total derivative
  - A.1. The action on pure tensors
  - A.2. The action on the three sectors
- B. Derivations on tensor products
- C. The Leibniz rule
- D. Commutativity
- E. The iterated derivative

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

## A. The formal total derivative

-/

/-- **The formal total derivative on the jet algebra of the Standard Model**: the sum of
  the total derivatives of the three sectors, each acting on its own factor. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra :=
  TensorProduct.map (TensorProduct.map (FermionicAlgebra.jetDeriv μ) LinearMap.id)
      LinearMap.id
    + TensorProduct.map (TensorProduct.map LinearMap.id (BosonicAlgebra.jetDeriv μ))
        LinearMap.id
    + TensorProduct.map LinearMap.id (GaugeJetAlgebra.complexJetDeriv μ)

/-!

### A.1. The action on pure tensors

-/

lemma jetDeriv_tmul (μ : Fin 1 ⊕ Fin 3) (f : FermionJetAlgebra) (h : HiggsJetAlgebra)
    (g : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    jetDeriv μ ((f ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] g)
      = ((FermionicAlgebra.jetDeriv μ f) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] g
        + (f ⊗ₜ[ℂ] (BosonicAlgebra.jetDeriv μ h)) ⊗ₜ[ℂ] g
        + (f ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] (GaugeJetAlgebra.complexJetDeriv μ g) := rfl

/-!

### A.2. The action on the three sectors

Each sector inclusion sends a sector element to a pure tensor whose other two factors are
`1`, and the total derivative annihilates `1` in every factor; so only the sector's own
derivative survives, and each inclusion intertwines the two derivatives.

-/

/-- The gauge sector's derivative annihilates the unit of the complexified gauge jet
  algebra. -/
private lemma complexJetDeriv_one (μ : Fin 1 ⊕ Fin 3) :
    GaugeJetAlgebra.complexJetDeriv μ (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) = 0 := by
  rw [show (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) = (1 : ℂ) ⊗ₜ[ℝ] (1 : GaugeJetAlgebra) from rfl,
    GaugeJetAlgebra.complexJetDeriv_tmul, GaugeJetAlgebra.jetDeriv_one,
    TensorProduct.tmul_zero]

/-- The derivative acts on the fermionic sector through the fermionic sector's own
  derivative. -/
lemma jetDeriv_includeFermion (μ : Fin 1 ⊕ Fin 3) (f : FermionJetAlgebra) :
    jetDeriv μ (includeFermion f) = includeFermion (FermionicAlgebra.jetDeriv μ f) := by
  have hincl : ∀ x : FermionJetAlgebra, includeFermion x
      = (x ⊗ₜ[ℂ] (1 : HiggsJetAlgebra)) ⊗ₜ[ℂ] (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) :=
    fun _ => rfl
  rw [hincl f, jetDeriv_tmul,
    show BosonicAlgebra.jetDeriv (V := HiggsVec) μ (1 : HiggsJetAlgebra) = 0 from
      BosonicAlgebra.jetDeriv_one μ,
    complexJetDeriv_one, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, add_zero, add_zero]
  exact (hincl (FermionicAlgebra.jetDeriv μ f)).symm

/-- The derivative acts on the Higgs sector through the Higgs sector's own derivative. -/
lemma jetDeriv_includeHiggs (μ : Fin 1 ⊕ Fin 3) (h : HiggsJetAlgebra) :
    jetDeriv μ (includeHiggs h) = includeHiggs (BosonicAlgebra.jetDeriv μ h) := by
  have hincl : ∀ x : HiggsJetAlgebra, includeHiggs x
      = ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) :=
    fun _ => rfl
  rw [hincl h, jetDeriv_tmul,
    show FermionicAlgebra.jetDeriv (V := FermionSpace) μ (1 : FermionJetAlgebra) = 0 from
      FermionicAlgebra.jetDeriv_one μ,
    complexJetDeriv_one, TensorProduct.zero_tmul, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, zero_add, add_zero]
  exact (hincl (BosonicAlgebra.jetDeriv μ h)).symm

/-- The derivative acts on the gauge sector through the gauge sector's own derivative. -/
lemma jetDeriv_includeGauge (μ : Fin 1 ⊕ Fin 3) (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    jetDeriv μ (includeGauge y) = includeGauge (GaugeJetAlgebra.complexJetDeriv μ y) := by
  rw [includeGauge_apply, jetDeriv_tmul,
    show FermionicAlgebra.jetDeriv (V := FermionSpace) μ (1 : FermionJetAlgebra) = 0 from
      FermionicAlgebra.jetDeriv_one μ,
    show BosonicAlgebra.jetDeriv (V := HiggsVec) μ (1 : HiggsJetAlgebra) = 0 from
      BosonicAlgebra.jetDeriv_one μ,
    TensorProduct.zero_tmul, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
    TensorProduct.zero_tmul, zero_add, zero_add, includeGauge_apply]

/-!

## B. Derivations on tensor products

-/

/-- A derivation of the left factor extends to a derivation of the tensor product. -/
lemma _root_.TensorProduct.map_derivation_left {A B : Type*} [Ring A] [Algebra ℂ A]
    [Ring B] [Algebra ℂ B] (D : A →ₗ[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) (x y : A ⊗[ℂ] B) :
    TensorProduct.map D LinearMap.id (x * y)
      = TensorProduct.map D LinearMap.id x * y
        + x * TensorProduct.map D LinearMap.id y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, h₁, h₂, add_mul, add_mul]
    abel
  | tmul a₁ b₁ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, h₁, h₂, mul_add, mul_add]
      abel
    | tmul a₂ b₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.id_apply, LinearMap.id_apply, hD, TensorProduct.add_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]

/-- A derivation of the right factor extends to a derivation of the tensor product. -/
lemma _root_.TensorProduct.map_derivation_right {A B : Type*} [Ring A] [Algebra ℂ A]
    [Ring B] [Algebra ℂ B] (D : B →ₗ[ℂ] B)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) (x y : A ⊗[ℂ] B) :
    TensorProduct.map LinearMap.id D (x * y)
      = TensorProduct.map LinearMap.id D x * y
        + x * TensorProduct.map LinearMap.id D y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, h₁, h₂, add_mul, add_mul]
    abel
  | tmul a₁ b₁ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, h₁, h₂, mul_add, mul_add]
      abel
    | tmul a₂ b₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.id_apply, LinearMap.id_apply, hD, TensorProduct.tmul_add,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]

/-!

## C. The Leibniz rule

-/

/-- The sum of three derivations is a derivation: the purely additive assembly, stated
  abstractly so it can be instantiated without rewriting inside a large type. -/
private lemma add₃_derivation {R : Type*} [NonUnitalNonAssocRing R]
    {D₁ D₂ D₃ : R → R} {x y : R}
    (h₁ : D₁ (x * y) = D₁ x * y + x * D₁ y)
    (h₂ : D₂ (x * y) = D₂ x * y + x * D₂ y)
    (h₃ : D₃ (x * y) = D₃ x * y + x * D₃ y) :
    D₁ (x * y) + D₂ (x * y) + D₃ (x * y)
      = (D₁ x + D₂ x + D₃ x) * y + x * (D₁ y + D₂ y + D₃ y) := by
  rw [h₁, h₂, h₃, add_mul, add_mul, mul_add, mul_add]
  abel

/-- **The Leibniz rule** for the total derivative on the jet algebra. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y := by
  have h₁ := TensorProduct.map_derivation_left
    (B := ℂ ⊗[ℝ] GaugeJetAlgebra)
    (TensorProduct.map (FermionicAlgebra.jetDeriv μ) LinearMap.id)
    (TensorProduct.map_derivation_left (FermionicAlgebra.jetDeriv μ)
      (FermionicAlgebra.jetDeriv_mul μ)) x y
  have h₂ := TensorProduct.map_derivation_left
    (B := ℂ ⊗[ℝ] GaugeJetAlgebra)
    (TensorProduct.map LinearMap.id (BosonicAlgebra.jetDeriv μ))
    (TensorProduct.map_derivation_right (BosonicAlgebra.jetDeriv μ)
      (BosonicAlgebra.jetDeriv_mul μ)) x y
  have h₃ := TensorProduct.map_derivation_right
    (A := FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra)
    (GaugeJetAlgebra.complexJetDeriv μ)
    (GaugeJetAlgebra.complexJetDeriv_mul μ) x y
  exact add₃_derivation h₁ h₂ h₃

/-!

## D. Commutativity

-/

/-- The sum of three maps pairwise commuting with the sum of three others commutes with
  it: the purely additive assembly, stated abstractly so it can be instantiated without
  rewriting inside a large type. -/
private lemma add₃_comp_comm {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {A₁ A₂ A₃ B₁ B₂ B₃ : M →ₗ[ℂ] M}
    (h11 : A₁.comp B₁ = B₁.comp A₁) (h12 : A₁.comp B₂ = B₂.comp A₁)
    (h13 : A₁.comp B₃ = B₃.comp A₁) (h21 : A₂.comp B₁ = B₁.comp A₂)
    (h22 : A₂.comp B₂ = B₂.comp A₂) (h23 : A₂.comp B₃ = B₃.comp A₂)
    (h31 : A₃.comp B₁ = B₁.comp A₃) (h32 : A₃.comp B₂ = B₂.comp A₃)
    (h33 : A₃.comp B₃ = B₃.comp A₃) :
    (A₁ + A₂ + A₃).comp (B₁ + B₂ + B₃) = (B₁ + B₂ + B₃).comp (A₁ + A₂ + A₃) := by
  simp only [LinearMap.add_comp, LinearMap.comp_add, h11, h12, h13, h21, h22, h23, h31,
    h32, h33]
  abel

/-- The total derivatives on the jet algebra commute. -/
lemma jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (jetDeriv μ).comp (jetDeriv ν) = (jetDeriv ν).comp (jetDeriv μ) := by
  have hW : ∀ D D' : (FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra) →ₗ[ℂ]
      (FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra),
      (TensorProduct.map D (LinearMap.id (M := ℂ ⊗[ℝ] GaugeJetAlgebra))).comp
        (TensorProduct.map D' LinearMap.id)
      = TensorProduct.map (D.comp D') LinearMap.id := fun D D' => by
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
  have hG : ∀ D D' : (ℂ ⊗[ℝ] GaugeJetAlgebra) →ₗ[ℂ] (ℂ ⊗[ℝ] GaugeJetAlgebra),
      (TensorProduct.map (LinearMap.id (M := FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra))
        D).comp (TensorProduct.map LinearMap.id D')
      = TensorProduct.map LinearMap.id (D.comp D') := fun D D' => by
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
  have hWG : ∀ (D : (FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra) →ₗ[ℂ]
      (FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra))
      (D' : (ℂ ⊗[ℝ] GaugeJetAlgebra) →ₗ[ℂ] (ℂ ⊗[ℝ] GaugeJetAlgebra)),
      (TensorProduct.map D LinearMap.id).comp (TensorProduct.map LinearMap.id D')
      = (TensorProduct.map LinearMap.id D').comp (TensorProduct.map D LinearMap.id) :=
    fun D D' => by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.id_comp, LinearMap.comp_id, LinearMap.comp_id]
  have hFH : ∀ (D : FermionJetAlgebra →ₗ[ℂ] FermionJetAlgebra)
      (D' : HiggsJetAlgebra →ₗ[ℂ] HiggsJetAlgebra),
      (TensorProduct.map D LinearMap.id).comp (TensorProduct.map LinearMap.id D')
      = (TensorProduct.map LinearMap.id D').comp (TensorProduct.map D LinearMap.id) :=
    fun D D' => by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
      LinearMap.id_comp, LinearMap.comp_id, LinearMap.comp_id]
  have hFF : ∀ D D' : FermionJetAlgebra →ₗ[ℂ] FermionJetAlgebra,
      (TensorProduct.map D (LinearMap.id (M := HiggsJetAlgebra))).comp
        (TensorProduct.map D' LinearMap.id)
      = TensorProduct.map (D.comp D') LinearMap.id := fun D D' => by
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
  have hHH : ∀ D D' : HiggsJetAlgebra →ₗ[ℂ] HiggsJetAlgebra,
      (TensorProduct.map (LinearMap.id (M := FermionJetAlgebra)) D).comp
        (TensorProduct.map LinearMap.id D')
      = TensorProduct.map LinearMap.id (D.comp D') := fun D D' => by
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
  have h11 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m (LinearMap.id (M := ℂ ⊗[ℝ] GaugeJetAlgebra)))
      ((hFF _ _).trans
        ((congrArg (fun d => TensorProduct.map d (LinearMap.id (M := HiggsJetAlgebra)))
          (FermionicAlgebra.jetDeriv_comm μ ν)).trans (hFF _ _).symm))).trans
      (hW _ _).symm)
  have h22 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m (LinearMap.id (M := ℂ ⊗[ℝ] GaugeJetAlgebra)))
      ((hHH _ _).trans
        ((congrArg (fun d => TensorProduct.map (LinearMap.id (M := FermionJetAlgebra)) d)
          (BosonicAlgebra.jetDeriv_comm μ ν)).trans (hHH _ _).symm))).trans
      (hW _ _).symm)
  have h33 := (hG _ _).trans
    ((congrArg (fun d => TensorProduct.map
        (LinearMap.id (M := FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra)) d)
      (GaugeJetAlgebra.complexJetDeriv_comm μ ν)).trans (hG _ _).symm)
  have h12 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m (LinearMap.id (M := ℂ ⊗[ℝ] GaugeJetAlgebra)))
      (hFH (FermionicAlgebra.jetDeriv μ) (BosonicAlgebra.jetDeriv ν))).trans
      (hW _ _).symm)
  have h21 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m (LinearMap.id (M := ℂ ⊗[ℝ] GaugeJetAlgebra)))
      (hFH (FermionicAlgebra.jetDeriv ν) (BosonicAlgebra.jetDeriv μ)).symm).trans
      (hW _ _).symm)
  exact add₃_comp_comm h11 h12 (hWG _ _) h21 h22 (hWG _ _) (hWG _ _).symm
    (hWG _ _).symm h33

/-!

## E. The iterated derivative

Iterating the sector restrictions of section A.2 along a multiset of directions: the
iterated total derivative restricts to the sector's own iterated derivative. These are the
forms the generator families of each sector consume.

-/

/-- The iterated total derivative acts on the fermionic sector through the fermionic
  sector's own iterated derivative. -/
lemma iteratedD_includeFermion (s : Multiset (Fin 1 ⊕ Fin 3)) (f : FermionJetAlgebra) :
    Lorentz.iteratedD jetDeriv jetDeriv_comm s (includeFermion f)
      = includeFermion (FermionicAlgebra.iteratedJetDeriv s f) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Lorentz.iteratedD_zero, FermionicAlgebra.iteratedJetDeriv_zero,
      LinearMap.id_apply, LinearMap.id_apply]
  | cons κ s ih =>
    rw [Lorentz.iteratedD_cons, FermionicAlgebra.iteratedJetDeriv_cons,
      LinearMap.comp_apply, LinearMap.comp_apply, ih, jetDeriv_includeFermion]

/-- The iterated total derivative acts on the Higgs sector through the Higgs sector's own
  iterated derivative. -/
lemma iteratedD_includeHiggs (s : Multiset (Fin 1 ⊕ Fin 3)) (h : HiggsJetAlgebra) :
    Lorentz.iteratedD jetDeriv jetDeriv_comm s (includeHiggs h)
      = includeHiggs (BosonicAlgebra.iteratedJetDeriv s h) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Lorentz.iteratedD_zero, BosonicAlgebra.iteratedJetDeriv_zero,
      LinearMap.id_apply, LinearMap.id_apply]
  | cons κ s ih =>
    rw [Lorentz.iteratedD_cons, BosonicAlgebra.iteratedJetDeriv_cons,
      LinearMap.comp_apply, LinearMap.comp_apply, ih, jetDeriv_includeHiggs]

end JetAlgebra

end StandardModel
