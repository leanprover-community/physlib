/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.JetDeriv
/-!
# The total derivative on the jet algebra of the Standard Model

## i. Overview

The formal total derivative on the jet algebra of the Standard Model is the sum of the
total derivatives of its three factors, each acting on its own tensor factor. On the two
matter factors it is the free-algebra derivation extending the derivative shift
`∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the generator space of the field datum — an even derivation
of the exterior algebra on the fermionic side, an ordinary derivation of the symmetric
algebra on the bosonic side — and on the connection factor it is the generic gauge-boson
derivative. It obeys the Leibniz rule, its components commute, and through each sector
inclusion it restricts to that sector's own derivative, for a single direction and for an
iterated multiset of directions alike.

The Leibniz rule and the commutation are assembled from the factor facts through abstract
lemmas proved at small types and instantiated, which keeps the proofs outside the full
tensor product.

## ii. Key results

- `JetAlgebra.jetDeriv` : the formal total derivative.
- `JetAlgebra.jetDeriv_mul` : the Leibniz rule.
- `JetAlgebra.jetDeriv_comm` : the total derivatives commute.
- `JetAlgebra.jetDeriv_includeGauge`, `jetDeriv_includeFermion`, `jetDeriv_includeHiggs` :
  the restrictions to the three sectors.
- `JetAlgebra.iteratedD_includeFermion`, `iteratedD_includeHiggs`,
  `iteratedD_includeGauge` : the same for the
  iterated derivative.

## iii. Table of contents

- A. The formal total derivative
  - A.1. The action on pure tensors
  - A.2. The action on the three factors
  - A.3. The action on the three sectors
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

/-- The total derivative on the fermionic factor: the even derivation of the exterior
  algebra extending the derivative shift on the fermionic generator space of the datum. -/
noncomputable abbrev jetDerivFermionFactor (μ : Fin 1 ⊕ Fin 3) :
    ExteriorAlgebra ℂ fieldData.FermionGenerators →ₗ[ℂ]
      ExteriorAlgebra ℂ fieldData.FermionGenerators :=
  ExteriorAlgebra.derivationOfLinear (fieldData.jetDerivFermion μ)

/-- The total derivative on the bosonic factor: the derivation of the symmetric algebra
  extending the derivative shift on the bosonic generator space of the datum. -/
noncomputable abbrev jetDerivBosonFactor (μ : Fin 1 ⊕ Fin 3) :
    SymmetricAlgebra ℂ fieldData.BosonGenerators →ₗ[ℂ]
      SymmetricAlgebra ℂ fieldData.BosonGenerators :=
  SymmetricAlgebra.derivationOfLinear (fieldData.jetDerivBoson μ)

/-- **The formal total derivative on the jet algebra of the Standard Model**: the sum of
  the total derivatives of the three factors, each acting on its own factor. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra :=
  TensorProduct.map (TensorProduct.map (jetDerivFermionFactor μ) LinearMap.id)
      LinearMap.id
    + TensorProduct.map (TensorProduct.map LinearMap.id (jetDerivBosonFactor μ))
        LinearMap.id
    + TensorProduct.map LinearMap.id
        (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ)

/-!

### A.1. The action on pure tensors

-/

lemma jetDeriv_tmul (μ : Fin 1 ⊕ Fin 3) (f : ExteriorAlgebra ℂ fieldData.FermionGenerators)
    (h : SymmetricAlgebra ℂ fieldData.BosonGenerators)
    (g : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) :
    jetDeriv μ ((f ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] g)
      = ((jetDerivFermionFactor μ f) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] g
        + (f ⊗ₜ[ℂ] (jetDerivBosonFactor μ h)) ⊗ₜ[ℂ] g
        + (f ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ g) :=
  rfl

/-!

### A.2. The action on the three factors

Each factor inclusion sends a factor element to a pure tensor whose other two factors are
`1`, and the total derivative annihilates `1` in every factor; so only that factor's own
derivative survives.

-/

/-- The three-factor derivation on a pure tensor, with the second and third derivatives
  annihilating their entries. Like the assemblies of sections B–D it is proved at abstract
  types and instantiated, so that the unit of a factor is never unfolded: the free algebras
  are quotients by congruences. -/
private lemma deriv₃_tmul_left {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (D : A →ₗ[ℂ] A) (E : B →ₗ[ℂ] B) (F : C →ₗ[ℂ] C) {b : B} {c : C}
    (hE : E b = 0) (hF : F c = 0) (a : A) :
    (TensorProduct.map (TensorProduct.map D (LinearMap.id (M := B)))
          (LinearMap.id (M := C))
        + TensorProduct.map (TensorProduct.map (LinearMap.id (M := A)) E)
          (LinearMap.id (M := C))
        + TensorProduct.map (LinearMap.id (M := A ⊗[ℂ] B)) F) ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)
      = (D a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c := by
  simp [hE, hF]

/-- The same with only the middle derivative surviving. -/
private lemma deriv₃_tmul_mid {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (D : A →ₗ[ℂ] A) (E : B →ₗ[ℂ] B) (F : C →ₗ[ℂ] C) {a : A} {c : C}
    (hD : D a = 0) (hF : F c = 0) (b : B) :
    (TensorProduct.map (TensorProduct.map D (LinearMap.id (M := B)))
          (LinearMap.id (M := C))
        + TensorProduct.map (TensorProduct.map (LinearMap.id (M := A)) E)
          (LinearMap.id (M := C))
        + TensorProduct.map (LinearMap.id (M := A ⊗[ℂ] B)) F) ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)
      = (a ⊗ₜ[ℂ] E b) ⊗ₜ[ℂ] c := by
  simp [hD, hF]

/-- The same with only the third derivative surviving. -/
private lemma deriv₃_tmul_right {A B C : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (D : A →ₗ[ℂ] A) (E : B →ₗ[ℂ] B) (F : C →ₗ[ℂ] C) {a : A} {b : B}
    (hD : D a = 0) (hE : E b = 0) (c : C) :
    (TensorProduct.map (TensorProduct.map D (LinearMap.id (M := B)))
          (LinearMap.id (M := C))
        + TensorProduct.map (TensorProduct.map (LinearMap.id (M := A)) E)
          (LinearMap.id (M := C))
        + TensorProduct.map (LinearMap.id (M := A ⊗[ℂ] B)) F) ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c)
      = (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] F c := by
  simp [hD, hE]

/-- Composition of two factorwise maps on the left factor, at abstract types. -/
private lemma map_comp_map_left {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (D D' : A →ₗ[ℂ] A) :
    (TensorProduct.map D (LinearMap.id (M := B))).comp
        (TensorProduct.map D' (LinearMap.id (M := B)))
      = TensorProduct.map (D.comp D') (LinearMap.id (M := B)) := by
  rw [← TensorProduct.map_comp, LinearMap.id_comp]

/-- Composition of two factorwise maps on the right factor, at abstract types. -/
private lemma map_comp_map_right {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (D D' : B →ₗ[ℂ] B) :
    (TensorProduct.map (LinearMap.id (M := A)) D).comp
        (TensorProduct.map (LinearMap.id (M := A)) D')
      = TensorProduct.map (LinearMap.id (M := A)) (D.comp D') := by
  rw [← TensorProduct.map_comp, LinearMap.id_comp]

/-- Maps on opposite factors commute, at abstract types. -/
private lemma map_left_comm_map_right {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (D : A →ₗ[ℂ] A) (D' : B →ₗ[ℂ] B) :
    (TensorProduct.map D (LinearMap.id (M := B))).comp
        (TensorProduct.map (LinearMap.id (M := A)) D')
      = (TensorProduct.map (LinearMap.id (M := A)) D').comp
        (TensorProduct.map D (LinearMap.id (M := B))) := by
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
    LinearMap.id_comp, LinearMap.comp_id, LinearMap.comp_id]

/-- A linear map intertwining two commuting families intertwines their iterates.
  Proved at abstract types and instantiated in term mode, so that the induction never runs
  inside the jet algebra. -/
private lemma iteratedD_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A)
    (hD : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ))
    (E : (Fin 1 ⊕ Fin 3) → B →ₗ[ℂ] B)
    (hE : ∀ μ ν, (E μ).comp (E ν) = (E ν).comp (E μ))
    (φ : A →ₗ[ℂ] B) (hφ : ∀ μ x, φ (D μ x) = E μ (φ x))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (x : A) :
    φ (Lorentz.iteratedD D hD s x) = Lorentz.iteratedD E hE s (φ x) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Lorentz.iteratedD_zero, Lorentz.iteratedD_zero, LinearMap.id_apply,
      LinearMap.id_apply]
  | cons κ s ih =>
    rw [Lorentz.iteratedD_cons, Lorentz.iteratedD_cons, LinearMap.comp_apply,
      LinearMap.comp_apply, hφ, ih]

/-- The connection factor's derivative annihilates the unit of the complexified
  gauge-boson jet algebra. -/
private lemma complexJetDeriv_one (μ : Fin 1 ⊕ Fin 3) :
    _root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ
        (1 : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) = 0 :=
  (congrArg (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ)
      Algebra.TensorProduct.one_def).trans
    ((_root_.LocalGaugeFieldAlgebra.complexJetDeriv_tmul μ 1 1).trans
      ((congrArg (fun z : _root_.LocalGaugeFieldAlgebra GaugeAlgebra => (1 : ℂ) ⊗ₜ[ℝ] z)
          (_root_.LocalGaugeFieldAlgebra.jetDeriv_one μ)).trans
        (TensorProduct.tmul_zero _ _)))

/-- The derivative acts on the fermionic factor through that factor's own derivation. The
  factor inclusions are unfolded through the generic `GaugeFieldData` rules rather than by
  `rfl`: at the Standard Model datum the definitional unfolding of the units has to see
  through the unexposed ring congruence of the symmetric algebra. -/
lemma jetDeriv_includeFermionFactor (μ : Fin 1 ⊕ Fin 3)
    (f : ExteriorAlgebra ℂ fieldData.FermionGenerators) :
    jetDeriv μ (fieldData.includeFermion f)
      = fieldData.includeFermion (jetDerivFermionFactor μ f) :=
  (congrArg (jetDeriv μ) (GaugeFieldData.includeFermion_apply f)).trans
    ((deriv₃_tmul_left _ _ _ (SymmetricAlgebra.derivationOfLinear_one _)
        (complexJetDeriv_one μ) f).trans
      (GaugeFieldData.includeFermion_apply (jetDerivFermionFactor μ f)).symm)

/-- The derivative acts on the bosonic factor through that factor's own derivation. -/
lemma jetDeriv_includeBosonFactor (μ : Fin 1 ⊕ Fin 3)
    (h : SymmetricAlgebra ℂ fieldData.BosonGenerators) :
    jetDeriv μ (fieldData.includeBoson h)
      = fieldData.includeBoson (jetDerivBosonFactor μ h) :=
  (congrArg (jetDeriv μ) (GaugeFieldData.includeBoson_apply h)).trans
    ((deriv₃_tmul_mid _ _ _ (ExteriorAlgebra.derivationOfLinear_one _)
        (complexJetDeriv_one μ) h).trans
      (GaugeFieldData.includeBoson_apply (jetDerivBosonFactor μ h)).symm)

/-- The derivative acts on the connection factor through the generic gauge-boson
  derivative. -/
lemma jetDeriv_includeConnection (μ : Fin 1 ⊕ Fin 3)
    (y : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) :
    jetDeriv μ (fieldData.includeConnection y)
      = fieldData.includeConnection
          (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ y) :=
  (congrArg (jetDeriv μ)
      ((GaugeFieldData.includeConnection_apply y).trans
        (congrArg (fun w : fieldData.MatterAlgebra => w ⊗ₜ[ℂ] y)
          GaugeFieldData.one_matterAlgebra))).trans
    ((deriv₃_tmul_right _ _ _ (ExteriorAlgebra.derivationOfLinear_one _)
        (SymmetricAlgebra.derivationOfLinear_one _) y).trans
      ((congrArg
          (fun w : fieldData.MatterAlgebra =>
            (w ⊗ₜ[ℂ] _root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ y
              : JetAlgebra))
          GaugeFieldData.one_matterAlgebra.symm).trans
        (GaugeFieldData.includeConnection_apply
          (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ y)).symm))

/-!

### A.3. The action on the three sectors

The three sector inclusions factor through the sector equivalences, which are maps of differential algebras; so the derivative restricts to each
sector's own derivative under its existing name.

-/

/-- The derivative acts on the fermionic sector through the fermionic sector's own
  derivative. -/
lemma jetDeriv_includeFermion (μ : Fin 1 ⊕ Fin 3) (f : FermionJetAlgebra) :
    jetDeriv μ (includeFermion f) = includeFermion (FermionicAlgebra.jetDeriv μ f) :=
  (congrArg (jetDeriv μ) (includeFermion_apply_equiv f)).trans
    ((jetDeriv_includeFermionFactor μ (fermionAlgebraEquiv f)).trans
      ((congrArg fieldData.includeFermion (fermionAlgebraEquiv_jetDeriv μ f).symm).trans
        (includeFermion_apply_equiv (FermionicAlgebra.jetDeriv μ f)).symm))

/-- The derivative acts on the Higgs sector through the Higgs sector's own derivative. -/
lemma jetDeriv_includeHiggs (μ : Fin 1 ⊕ Fin 3) (h : HiggsJetAlgebra) :
    jetDeriv μ (includeHiggs h) = includeHiggs (BosonicAlgebra.jetDeriv μ h) :=
  (congrArg (jetDeriv μ) (includeHiggs_apply_equiv h)).trans
    ((jetDeriv_includeBosonFactor μ (higgsAlgebraEquiv h)).trans
      ((congrArg fieldData.includeBoson (higgsAlgebraEquiv_jetDeriv μ h).symm).trans
        (includeHiggs_apply_equiv (BosonicAlgebra.jetDeriv μ h)).symm))

/-- The derivative acts on the gauge sector through the gauge sector's own derivative. The
  gauge sector inclusion is the connection inclusion of the datum, the Standard Model gauge
  bosons being the generic ones at `GaugeAlgebra`. -/
lemma jetDeriv_includeGauge (μ : Fin 1 ⊕ Fin 3)
    (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) :
    jetDeriv μ (includeGauge y)
      = includeGauge (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ y) :=
  jetDeriv_includeConnection μ y

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
    (B := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)
    (TensorProduct.map (jetDerivFermionFactor μ) LinearMap.id)
    (TensorProduct.map_derivation_left (jetDerivFermionFactor μ)
      (ExteriorAlgebra.derivationOfLinear_mul _)) x y
  have h₂ := TensorProduct.map_derivation_left
    (B := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)
    (TensorProduct.map LinearMap.id (jetDerivBosonFactor μ))
    (TensorProduct.map_derivation_right (jetDerivBosonFactor μ)
      (SymmetricAlgebra.derivationOfLinear_mul _)) x y
  have h₃ := TensorProduct.map_derivation_right
    (A := ExteriorAlgebra ℂ fieldData.FermionGenerators ⊗[ℂ]
      SymmetricAlgebra ℂ fieldData.BosonGenerators)
    (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra μ)
    (_root_.LocalGaugeFieldAlgebra.complexJetDeriv_mul μ) x y
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
  have hW := fun (D D' : fieldData.MatterAlgebra →ₗ[ℂ] fieldData.MatterAlgebra) =>
    map_comp_map_left (B := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) D D'
  have hG := fun (D D' : (ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) →ₗ[ℂ]
      (ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)) =>
    map_comp_map_right (A := fieldData.MatterAlgebra) D D'
  have hWG := fun (D : fieldData.MatterAlgebra →ₗ[ℂ] fieldData.MatterAlgebra)
      (D' : (ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra) →ₗ[ℂ]
        (ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)) =>
    map_left_comm_map_right D D'
  have hFH := fun (D : ExteriorAlgebra ℂ fieldData.FermionGenerators →ₗ[ℂ]
        ExteriorAlgebra ℂ fieldData.FermionGenerators)
      (D' : SymmetricAlgebra ℂ fieldData.BosonGenerators →ₗ[ℂ]
        SymmetricAlgebra ℂ fieldData.BosonGenerators) =>
    map_left_comm_map_right D D'
  have hFF := fun (D D' : ExteriorAlgebra ℂ fieldData.FermionGenerators →ₗ[ℂ]
      ExteriorAlgebra ℂ fieldData.FermionGenerators) =>
    map_comp_map_left (B := SymmetricAlgebra ℂ fieldData.BosonGenerators) D D'
  have hHH := fun (D D' : SymmetricAlgebra ℂ fieldData.BosonGenerators →ₗ[ℂ]
      SymmetricAlgebra ℂ fieldData.BosonGenerators) =>
    map_comp_map_right (A := ExteriorAlgebra ℂ fieldData.FermionGenerators) D D'
  have hfermion : (jetDerivFermionFactor μ).comp (jetDerivFermionFactor ν)
      = (jetDerivFermionFactor ν).comp (jetDerivFermionFactor μ) :=
    LinearMap.ext fun z => ExteriorAlgebra.derivationOfLinear_comm_apply
      (fieldData.jetDerivFermion_comm μ ν) z
  have hboson : (jetDerivBosonFactor μ).comp (jetDerivBosonFactor ν)
      = (jetDerivBosonFactor ν).comp (jetDerivBosonFactor μ) :=
    LinearMap.ext fun z => SymmetricAlgebra.derivationOfLinear_comm_apply
      (fieldData.jetDerivBoson_comm μ ν) z
  have h11 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m
        (LinearMap.id (M := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)))
      ((hFF _ _).trans
        ((congrArg (fun d => TensorProduct.map d
            (LinearMap.id (M := SymmetricAlgebra ℂ fieldData.BosonGenerators)))
          hfermion).trans (hFF _ _).symm))).trans
      (hW _ _).symm)
  have h22 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m
        (LinearMap.id (M := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)))
      ((hHH _ _).trans
        ((congrArg (fun d => TensorProduct.map
            (LinearMap.id (M := ExteriorAlgebra ℂ fieldData.FermionGenerators)) d)
          hboson).trans (hHH _ _).symm))).trans
      (hW _ _).symm)
  have h33 := (hG _ _).trans
    ((congrArg (fun d => TensorProduct.map
        (LinearMap.id (M := ExteriorAlgebra ℂ fieldData.FermionGenerators ⊗[ℂ]
          SymmetricAlgebra ℂ fieldData.BosonGenerators)) d)
      (_root_.LocalGaugeFieldAlgebra.complexJetDeriv_comm μ ν)).trans (hG _ _).symm)
  have h12 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m
        (LinearMap.id (M := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)))
      (hFH (jetDerivFermionFactor μ) (jetDerivBosonFactor ν))).trans
      (hW _ _).symm)
  have h21 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m
        (LinearMap.id (M := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)))
      (hFH (jetDerivFermionFactor ν) (jetDerivBosonFactor μ)).symm).trans
      (hW _ _).symm)
  exact add₃_comp_comm h11 h12 (hWG _ _) h21 h22 (hWG _ _) (hWG _ _).symm
    (hWG _ _).symm h33

/-!

## E. The iterated derivative

Iterating the sector restrictions of section A.3 along a multiset of directions: the
iterated total derivative restricts to the sector's own iterated derivative. These are the
forms the generator families of each sector consume.

-/

/-- The iterated total derivative acts on the fermionic sector through the fermionic
  sector's own iterated derivative. -/
lemma iteratedD_includeFermion (s : Multiset (Fin 1 ⊕ Fin 3)) (f : FermionJetAlgebra) :
    Lorentz.iteratedD jetDeriv jetDeriv_comm s (includeFermion f)
      = includeFermion (FermionicAlgebra.iteratedJetDeriv s f) := by
  have h := iteratedD_map (A := FermionJetAlgebra) (B := JetAlgebra)
    FermionicAlgebra.jetDeriv FermionicAlgebra.jetDeriv_comm jetDeriv jetDeriv_comm
    includeFermion.toLinearMap (fun μ x => (jetDeriv_includeFermion μ x).symm) s f
  exact h.symm

/-- The iterated total derivative acts on the Higgs sector through the Higgs sector's own
  iterated derivative. -/
lemma iteratedD_includeHiggs (s : Multiset (Fin 1 ⊕ Fin 3)) (h : HiggsJetAlgebra) :
    Lorentz.iteratedD jetDeriv jetDeriv_comm s (includeHiggs h)
      = includeHiggs (BosonicAlgebra.iteratedJetDeriv s h) := by
  have hmap := iteratedD_map (A := HiggsJetAlgebra) (B := JetAlgebra)
    BosonicAlgebra.jetDeriv BosonicAlgebra.jetDeriv_comm jetDeriv jetDeriv_comm
    includeHiggs.toLinearMap (fun μ x => (jetDeriv_includeHiggs μ x).symm) s h
  exact hmap.symm

/-- The iterated total derivative acts on the gauge sector through the gauge sector's own
  iterated derivative. Like its two siblings this instantiates the abstract
  `iteratedD_map` rather than running the induction inside the jet algebra. -/
lemma iteratedD_includeGauge (s : Multiset (Fin 1 ⊕ Fin 3))
    (y : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra GaugeAlgebra)) :
    Lorentz.iteratedD jetDeriv jetDeriv_comm s (includeGauge y)
      = includeGauge (Lorentz.iteratedD
          (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra)
          _root_.LocalGaugeFieldAlgebra.complexJetDeriv_comm s y) := by
  have hmap := iteratedD_map (A := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra GaugeAlgebra)
    (B := JetAlgebra) (_root_.LocalGaugeFieldAlgebra.complexJetDeriv GaugeAlgebra)
    _root_.LocalGaugeFieldAlgebra.complexJetDeriv_comm jetDeriv jetDeriv_comm
    includeGauge.toLinearMap (fun μ x => (jetDeriv_includeGauge μ x).symm) s y
  exact hmap.symm

end JetAlgebra

end StandardModel
