/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.Symbols
public import PhyslibAlpha.Mathematics.AlgebraRepresentation
public import PhyslibAlpha.Mathematics.ExteriorAlgebra
public import PhyslibAlpha.Mathematics.ForMathlib.RingTheory.TensorProduct.Derivation
public import PhyslibAlpha.Mathematics.SymmetricAlgebra
public import PhyslibAlpha.Relativity.IsLorentzDeriv
/-!
# The total derivative on the local field algebra

The formal total derivative `∂_μ` on the local field algebra of a field datum, its Leibniz
rule, its action on the symbols and its Lorentz covariance.

## i. Overview

The formal total derivative on the local field algebra of a field datum `T` is the sum of
the total derivatives of its three factors, each acting on its own tensor factor. On the two
matter factors it is the free-algebra derivation extending the derivative shift
`∂_s ψ_α ↦ ∂_{s + {μ}} ψ_α` of the generator space of the datum, an even derivation of the
exterior algebra on the fermionic side and an ordinary derivation of the symmetric algebra on
the bosonic side. On the connection factor it is the derivative of the complexified
gauge-boson algebra. It obeys the Leibniz rule, its components commute, and on each factor
it is that factor's own derivative.

On a matter symbol the total derivative appends the direction `μ` to the derivative label,
`∂_μ (∂_s ψ^φ) = ∂_{s + {μ}} ψ^φ`, so the symbol `∂_s ψ^φ` is the iterated total derivative
along `s` of the undifferentiated symbol. On the connection factor the iterated total
derivative is the iterated derivative of the gauge-boson algebra.

The total derivative is a Lorentz vector. The Lorentz action of the datum intertwines `∂_μ`
with `∑_a Λ_{a μ} ∂_a`. This is proved for the action written factor by factor, through the
covariance of the derivation extending a linear endomorphism on each free-algebra factor,
and transported to `T.repLorentzGroup`, which agrees with it.

The Leibniz rule, the commutation and the covariance are assembled from the factor facts
through abstract lemmas proved at small types and instantiated, which keeps the proofs
outside the full tensor product. The name `totalDeriv` distinguishes the derivative from the
`jetDeriv` on `V`-valued jets.

## ii. Key results

- `GaugeFieldData.totalDeriv` : the formal total derivative.
- `GaugeFieldData.totalDeriv_mul` : the Leibniz rule.
- `GaugeFieldData.totalDeriv_comm` : the total derivatives commute.
- `GaugeFieldData.totalDeriv_includeFermionFactor`, `totalDeriv_includeBosonFactor`,
  `totalDeriv_includeConnection` : the restrictions to the three factors.
- `GaugeFieldData.iteratedD_includeConnection` : the iterated derivative on the connection
  factor.
- `GaugeFieldData.totalDeriv_fermionSymbol`, `totalDeriv_bosonSymbol` and their conjugates :
  the total derivative appends a direction to the derivative label.
- `GaugeFieldData.iteratedD_fermionSymbol`, `iteratedD_bosonSymbol` and their conjugates :
  the iterated total derivative appends a multiset of directions.
- `GaugeFieldData.repLorentzGroup_totalDeriv` : the total derivative is a Lorentz vector.

## iii. Table of contents

- A. The formal total derivative
  - A.1. The action on the three factors
- B. The Leibniz rule
- C. Commutativity
- D. The iterated derivative on the connection factor
- E. The derivative shift on a component space
- F. The total derivative of the matter generators
- G. The total derivative of the matter symbols
- H. The iterated total derivative of the matter symbols
- I. Lorentz covariance
  - I.1. The factorwise action
  - I.2. Multiplicativity
  - I.3. The action on the three factors
  - I.4. The total derivative is a Lorentz vector for the factorwise action
  - I.5. Agreement with the generic action

## iv. References

* None.

-/

@[expose] public section

open TensorProduct Matrix MatrixGroups

namespace GaugeFieldData

variable {κ : Type} [Fintype κ] [DecidableEq κ] {G : GlobalGaugeGroup κ} (T : GaugeFieldData G)

/-!

## A. The formal total derivative

-/

/-- The total derivative on the fermionic factor, the even derivation of the exterior
  algebra extending the derivative shift on the fermionic generator space of the datum. -/
noncomputable abbrev totalDerivFermionFactor (μ : Fin 1 ⊕ Fin 3) :
    ExteriorAlgebra ℂ T.FermionGenerators →ₗ[ℂ]
      ExteriorAlgebra ℂ T.FermionGenerators :=
  ExteriorAlgebra.derivationOfLinear (T.jetDerivFermion μ)

/-- The total derivative on the bosonic factor, the derivation of the symmetric algebra
  extending the derivative shift on the bosonic generator space of the datum. -/
noncomputable abbrev totalDerivBosonFactor (μ : Fin 1 ⊕ Fin 3) :
    SymmetricAlgebra ℂ T.BosonGenerators →ₗ[ℂ]
      SymmetricAlgebra ℂ T.BosonGenerators :=
  SymmetricAlgebra.derivationOfLinear (T.jetDerivBoson μ)

/-- The formal total derivative on the local field algebra, the sum of the total
  derivatives of the three factors, each acting on its own factor. -/
noncomputable def totalDeriv (μ : Fin 1 ⊕ Fin 3) :
    T.LocalFieldAlgebra →ₗ[ℂ] T.LocalFieldAlgebra :=
  TensorProduct.map (TensorProduct.map (T.totalDerivFermionFactor μ) LinearMap.id)
      LinearMap.id
    + TensorProduct.map (TensorProduct.map LinearMap.id (T.totalDerivBosonFactor μ))
        LinearMap.id
    + TensorProduct.map LinearMap.id
        (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G μ)


variable {T}

/-!

### A.1. The action on the three factors

Each factor inclusion sends a factor element to a pure tensor whose other two factors are
`1`, and the total derivative annihilates `1` in every factor; so only that factor's own
derivative survives.

-/

/-- The three-factor derivation on a pure tensor, with the second and third derivatives
  annihilating their entries. Like the assemblies of sections B and C it is proved at abstract
  types and instantiated, so that the unit of a factor is never unfolded, the free algebras
  being quotients by congruences. -/
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
  inside the local field algebra. -/
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
  gauge-boson algebra. -/
private lemma complexJetDeriv_one (μ : Fin 1 ⊕ Fin 3) :
    _root_.LocalGaugeFieldAlgebra.complexJetDeriv G μ
        (1 : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G) = 0 :=
  (congrArg (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G μ)
      Algebra.TensorProduct.one_def).trans
    ((_root_.LocalGaugeFieldAlgebra.complexJetDeriv_tmul μ 1 1).trans
      ((congrArg (fun z : _root_.LocalGaugeFieldAlgebra G => (1 : ℂ) ⊗ₜ[ℝ] z)
          (_root_.LocalGaugeFieldAlgebra.jetDeriv_one μ)).trans
        (TensorProduct.tmul_zero _ _)))

/-- The derivative acts on the fermionic factor through that factor's own derivation. The
  factor inclusions are unfolded through the generic `GaugeFieldData` rules rather than by
  `rfl`, since at a concrete datum the definitional unfolding of the units has to see
  through the unexposed ring congruence of the symmetric algebra. -/
lemma totalDeriv_includeFermionFactor (μ : Fin 1 ⊕ Fin 3)
    (f : ExteriorAlgebra ℂ T.FermionGenerators) :
    T.totalDeriv μ (T.includeFermion f)
      = T.includeFermion (T.totalDerivFermionFactor μ f) :=
  (congrArg (T.totalDeriv μ) (GaugeFieldData.includeFermion_apply f)).trans
    ((deriv₃_tmul_left _ _ _ (SymmetricAlgebra.derivationOfLinear_one _)
        (complexJetDeriv_one μ) f).trans
      (GaugeFieldData.includeFermion_apply (T.totalDerivFermionFactor μ f)).symm)

/-- The derivative acts on the bosonic factor through that factor's own derivation. -/
lemma totalDeriv_includeBosonFactor (μ : Fin 1 ⊕ Fin 3)
    (h : SymmetricAlgebra ℂ T.BosonGenerators) :
    T.totalDeriv μ (T.includeBoson h)
      = T.includeBoson (T.totalDerivBosonFactor μ h) :=
  (congrArg (T.totalDeriv μ) (GaugeFieldData.includeBoson_apply h)).trans
    ((deriv₃_tmul_mid _ _ _ (ExteriorAlgebra.derivationOfLinear_one _)
        (complexJetDeriv_one μ) h).trans
      (GaugeFieldData.includeBoson_apply (T.totalDerivBosonFactor μ h)).symm)

/-- The derivative acts on the connection factor through the generic gauge-boson
  derivative. -/
lemma totalDeriv_includeConnection (μ : Fin 1 ⊕ Fin 3)
    (y : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G) :
    T.totalDeriv μ (T.includeConnection y)
      = T.includeConnection
          (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G μ y) :=
  (congrArg (T.totalDeriv μ)
      ((GaugeFieldData.includeConnection_apply y).trans
        (congrArg (fun w : T.MatterAlgebra => w ⊗ₜ[ℂ] y)
          GaugeFieldData.one_matterAlgebra))).trans
    ((deriv₃_tmul_right _ _ _ (ExteriorAlgebra.derivationOfLinear_one _)
        (SymmetricAlgebra.derivationOfLinear_one _) y).trans
      ((congrArg
          (fun w : T.MatterAlgebra =>
            (w ⊗ₜ[ℂ] _root_.LocalGaugeFieldAlgebra.complexJetDeriv G μ y :
              T.LocalFieldAlgebra))
          GaugeFieldData.one_matterAlgebra.symm).trans
        (GaugeFieldData.includeConnection_apply
          (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G μ y)).symm))

/-!

## B. The Leibniz rule

-/

/-- The sum of three derivations is a derivation, the purely additive assembly, stated
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

/-- The Leibniz rule for the total derivative on the local field algebra. -/
lemma totalDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : T.LocalFieldAlgebra) :
    T.totalDeriv μ (x * y) = T.totalDeriv μ x * y + x * T.totalDeriv μ y := by
  have h₁ := TensorProduct.map_derivation_left
    (B := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)
    (TensorProduct.map (T.totalDerivFermionFactor μ) LinearMap.id)
    (TensorProduct.map_derivation_left (T.totalDerivFermionFactor μ)
      (ExteriorAlgebra.derivationOfLinear_mul _)) x y
  have h₂ := TensorProduct.map_derivation_left
    (B := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)
    (TensorProduct.map LinearMap.id (T.totalDerivBosonFactor μ))
    (TensorProduct.map_derivation_right (T.totalDerivBosonFactor μ)
      (SymmetricAlgebra.derivationOfLinear_mul _)) x y
  have h₃ := TensorProduct.map_derivation_right
    (A := ExteriorAlgebra ℂ T.FermionGenerators ⊗[ℂ]
      SymmetricAlgebra ℂ T.BosonGenerators)
    (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G μ)
    (_root_.LocalGaugeFieldAlgebra.complexJetDeriv_mul μ) x y
  exact add₃_derivation h₁ h₂ h₃

/-!

## C. Commutativity

-/

/-- The sum of three maps pairwise commuting with the sum of three others commutes with
  it, the purely additive assembly, stated abstractly so it can be instantiated without
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

/-- Commuting maps on the left factor still commute after tensoring with the identity. -/
private lemma map_left_comm_of_comm {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {D D' : A →ₗ[ℂ] A} (h : D.comp D' = D'.comp D) :
    (TensorProduct.map D (LinearMap.id (M := B))).comp
        (TensorProduct.map D' (LinearMap.id (M := B)))
      = (TensorProduct.map D' (LinearMap.id (M := B))).comp
        (TensorProduct.map D (LinearMap.id (M := B))) := by
  rw [map_comp_map_left, map_comp_map_left, h]

/-- Commuting maps on the right factor still commute after tensoring with the identity. -/
private lemma map_right_comm_of_comm {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {D D' : B →ₗ[ℂ] B} (h : D.comp D' = D'.comp D) :
    (TensorProduct.map (LinearMap.id (M := A)) D).comp
        (TensorProduct.map (LinearMap.id (M := A)) D')
      = (TensorProduct.map (LinearMap.id (M := A)) D').comp
        (TensorProduct.map (LinearMap.id (M := A)) D) := by
  rw [map_comp_map_right, map_comp_map_right, h]

variable (T) in
/-- The total derivatives on the fermionic factor commute. -/
lemma totalDerivFermionFactor_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (T.totalDerivFermionFactor μ).comp (T.totalDerivFermionFactor ν)
      = (T.totalDerivFermionFactor ν).comp (T.totalDerivFermionFactor μ) :=
  LinearMap.ext fun z => ExteriorAlgebra.derivationOfLinear_comm_apply
    (T.jetDerivFermion_comm μ ν) z

variable (T) in
/-- The total derivatives on the bosonic factor commute. -/
lemma totalDerivBosonFactor_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (T.totalDerivBosonFactor μ).comp (T.totalDerivBosonFactor ν)
      = (T.totalDerivBosonFactor ν).comp (T.totalDerivBosonFactor μ) :=
  LinearMap.ext fun z => SymmetricAlgebra.derivationOfLinear_comm_apply
    (T.jetDerivBoson_comm μ ν) z

variable (T) in
/-- The total derivatives on the local field algebra commute. -/
lemma totalDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) :
    (T.totalDeriv μ).comp (T.totalDeriv ν) = (T.totalDeriv ν).comp (T.totalDeriv μ) := by
  have hW := fun (D D' : T.MatterAlgebra →ₗ[ℂ] T.MatterAlgebra) =>
    map_comp_map_left (B := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G) D D'
  have hWG := fun (D : T.MatterAlgebra →ₗ[ℂ] T.MatterAlgebra)
      (D' : (ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G) →ₗ[ℂ]
        (ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)) =>
    map_left_comm_map_right D D'
  have hFH := fun (D : ExteriorAlgebra ℂ T.FermionGenerators →ₗ[ℂ]
        ExteriorAlgebra ℂ T.FermionGenerators)
      (D' : SymmetricAlgebra ℂ T.BosonGenerators →ₗ[ℂ]
        SymmetricAlgebra ℂ T.BosonGenerators) =>
    map_left_comm_map_right D D'
  have h11 := map_left_comm_of_comm (B := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)
    (map_left_comm_of_comm (B := SymmetricAlgebra ℂ T.BosonGenerators)
      (T.totalDerivFermionFactor_comm μ ν))
  have h22 := map_left_comm_of_comm (B := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)
    (map_right_comm_of_comm (A := ExteriorAlgebra ℂ T.FermionGenerators)
      (T.totalDerivBosonFactor_comm μ ν))
  have h33 := map_right_comm_of_comm (A := T.MatterAlgebra)
    (_root_.LocalGaugeFieldAlgebra.complexJetDeriv_comm (G := G) μ ν)
  have h12 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m
        (LinearMap.id (M := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)))
      (hFH (T.totalDerivFermionFactor μ) (T.totalDerivBosonFactor ν))).trans
      (hW _ _).symm)
  have h21 := (hW _ _).trans
    ((congrArg (fun m => TensorProduct.map m
        (LinearMap.id (M := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)))
      (hFH (T.totalDerivFermionFactor ν) (T.totalDerivBosonFactor μ)).symm).trans
      (hW _ _).symm)
  exact add₃_comp_comm h11 h12 (hWG _ _) h21 h22 (hWG _ _) (hWG _ _).symm
    (hWG _ _).symm h33

/-!

## D. The iterated derivative on the connection factor

Iterating the restriction of section A.2 to the connection factor along a multiset of
directions: there the iterated total derivative is the iterated derivative of the
complexified gauge-boson algebra.

-/

/-- The iterated total derivative acts on the connection factor through the gauge sector's
  own iterated derivative. It instantiates the abstract `iteratedD_map` rather than running
  the induction inside the local field algebra. -/
lemma iteratedD_includeConnection (s : Multiset (Fin 1 ⊕ Fin 3))
    (y : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G) :
    Lorentz.iteratedD T.totalDeriv T.totalDeriv_comm s (T.includeConnection y)
      = T.includeConnection (Lorentz.iteratedD
          (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G)
          _root_.LocalGaugeFieldAlgebra.complexJetDeriv_comm s y) := by
  have hmap := iteratedD_map (A := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)
    (B := T.LocalFieldAlgebra)
    (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G)
    _root_.LocalGaugeFieldAlgebra.complexJetDeriv_comm T.totalDeriv T.totalDeriv_comm
    T.includeConnection.toLinearMap
    (fun μ x => (totalDeriv_includeConnection μ x).symm) s y
  exact hmap.symm

/-!

## E. The derivative shift on a component space

-/

/-- On an unconjugated component `∂_s φ` the derivative shift appends the direction `μ` to
  the derivative label. -/
private lemma fieldDerivSpace_jetDeriv_inl {M : G.MatterField} (μ : Fin 1 ⊕ Fin 3)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ M.V) :
    FieldDerivSpace.jetDeriv μ
        ((SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0) : FieldDerivSpace M)
      = (SpaceTimeDerivAlgebraℂ.basis (μ ::ₘ s) ⊗ₜ[ℂ] φ, 0) := by
  refine Prod.ext ((FieldDerivSpace.jetDeriv_fst_tmul μ _ φ 0).trans ?_)
    ((FieldDerivSpace.jetDeriv_snd μ _).trans (map_zero _))
  show (SpaceTimeDerivAlgebraℂ.basis s * SpaceTimeDerivAlgebraℂ.basis {μ}) ⊗ₜ[ℂ] φ
    = SpaceTimeDerivAlgebraℂ.basis (μ ::ₘ s) ⊗ₜ[ℂ] φ
  rw [SpaceTimeDerivAlgebraℂ.basis_mul, add_comm, Multiset.singleton_add]

/-- On a conjugate component `∂_s φ̄` the derivative shift appends the direction `μ` to the
  derivative label. -/
private lemma fieldDerivSpace_jetDeriv_inr {M : G.MatterField} (μ : Fin 1 ⊕ Fin 3)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule M.V)) :
    FieldDerivSpace.jetDeriv μ
        ((0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ) : FieldDerivSpace M)
      = (0, SpaceTimeDerivAlgebraℂ.basis (μ ::ₘ s) ⊗ₜ[ℂ] φ) := by
  refine Prod.ext ((FieldDerivSpace.jetDeriv_fst μ _).trans (map_zero _))
    ((FieldDerivSpace.jetDeriv_snd_tmul μ 0 _ φ).trans ?_)
  show (SpaceTimeDerivAlgebraℂ.basis s * SpaceTimeDerivAlgebraℂ.basis {μ}) ⊗ₜ[ℂ] φ
    = SpaceTimeDerivAlgebraℂ.basis (μ ::ₘ s) ⊗ₜ[ℂ] φ
  rw [SpaceTimeDerivAlgebraℂ.basis_mul, add_comm, Multiset.singleton_add]

/-!

## F. The total derivative of the matter generators

A matter generator lies in its free-algebra factor, where the total derivative is the
derivation extending the derivative shift of the generator space. On a degree-one element
that derivation is the shift itself, which acts species by species.

-/

/-- The total derivative of a fermionic generator is the generator of the shifted
  component. -/
lemma totalDeriv_ιFermion (μ : Fin 1 ⊕ Fin 3) (i : T.FermionSpecies)
    (x : FieldDerivSpace (T.fermion i)) :
    T.totalDeriv μ (T.ιFermion i x)
      = T.ιFermion i (FieldDerivSpace.jetDeriv μ x) :=
  (totalDeriv_includeFermionFactor μ (ExteriorAlgebra.ι ℂ (T.inclFermion i x))).trans
    (congrArg T.includeFermion
      ((ExteriorAlgebra.derivationOfLinear_ι (T.jetDerivFermion μ)
          (T.inclFermion i x)).trans
        (congrArg (ExteriorAlgebra.ι ℂ)
          (GaugeFieldData.jetDerivFermion_inclFermion μ i x))))

/-- The total derivative of a bosonic generator is the generator of the shifted
  component. -/
lemma totalDeriv_ιBoson (μ : Fin 1 ⊕ Fin 3) (j : T.BosonSpecies)
    (y : FieldDerivSpace (T.boson j)) :
    T.totalDeriv μ (T.ιBoson j y)
      = T.ιBoson j (FieldDerivSpace.jetDeriv μ y) :=
  (totalDeriv_includeBosonFactor μ
      (SymmetricAlgebra.ι ℂ T.BosonGenerators (T.inclBoson j y))).trans
    (congrArg T.includeBoson
      ((SymmetricAlgebra.derivationOfLinear_ι (T.jetDerivBoson μ)
          (T.inclBoson j y)).trans
        (congrArg (SymmetricAlgebra.ι ℂ T.BosonGenerators)
          (GaugeFieldData.jetDerivBoson_inclBoson μ j y))))

/-!

## G. The total derivative of the matter symbols

-/

/-- The total derivative appends the direction `μ` to the derivative label of a fermionic
  symbol, `∂_μ (∂_s ψ^φ) = ∂_{s + {μ}} ψ^φ`. -/
lemma totalDeriv_fermionSymbol (μ : Fin 1 ⊕ Fin 3) (i : T.FermionSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.totalDeriv μ (T.fermionSymbol i s φ) = T.fermionSymbol i (μ ::ₘ s) φ :=
  (totalDeriv_ιFermion μ i (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0)).trans
    (congrArg (T.ιFermion i)
      (fieldDerivSpace_jetDeriv_inl (M := T.fermion i) μ s φ))

/-- The total derivative appends the direction `μ` to the derivative label of a conjugate
  fermionic symbol. -/
lemma totalDeriv_conjFermionSymbol (μ : Fin 1 ⊕ Fin 3) (i : T.FermionSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.totalDeriv μ (T.conjFermionSymbol i s φ)
      = T.conjFermionSymbol i (μ ::ₘ s) φ :=
  (totalDeriv_ιFermion μ i (0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ)).trans
    (congrArg (T.ιFermion i)
      (fieldDerivSpace_jetDeriv_inr (M := T.fermion i) μ s φ))

/-- The total derivative appends the direction `μ` to the derivative label of a bosonic
  symbol, `∂_μ (∂_s φ) = ∂_{s + {μ}} φ`. -/
lemma totalDeriv_bosonSymbol (μ : Fin 1 ⊕ Fin 3) (j : T.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.totalDeriv μ (T.bosonSymbol j s φ) = T.bosonSymbol j (μ ::ₘ s) φ :=
  (totalDeriv_ιBoson μ j (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ, 0)).trans
    (congrArg (T.ιBoson j)
      (fieldDerivSpace_jetDeriv_inl (M := T.boson j) μ s φ))

/-- The total derivative appends the direction `μ` to the derivative label of a conjugate
  bosonic symbol. -/
lemma totalDeriv_conjBosonSymbol (μ : Fin 1 ⊕ Fin 3) (j : T.BosonSpecies)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.totalDeriv μ (T.conjBosonSymbol j s φ)
      = T.conjBosonSymbol j (μ ::ₘ s) φ :=
  (totalDeriv_ιBoson μ j (0, SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ)).trans
    (congrArg (T.ιBoson j)
      (fieldDerivSpace_jetDeriv_inr (M := T.boson j) μ s φ))

/-!

## H. The iterated total derivative of the matter symbols

-/

/-- A family indexed by derivative labels on which each operator of a commuting family
  appends its direction is shifted by the iterated operator. Proved at an abstract algebra
  and instantiated, so that the induction never runs inside the local field algebra. -/
private lemma iteratedD_of_shift {A : Type} [Ring A] [Algebra ℂ A]
    (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (hD : ∀ μ ν, (D μ).comp (D ν) = (D ν).comp (D μ))
    (f : Multiset (Fin 1 ⊕ Fin 3) → A) (hf : ∀ μ r, D μ (f r) = f (μ ::ₘ r))
    (s r : Multiset (Fin 1 ⊕ Fin 3)) : Lorentz.iteratedD D hD s (f r) = f (s + r) := by
  induction s using Multiset.induction_on with
  | empty => rw [Lorentz.iteratedD_zero, LinearMap.id_apply, zero_add]
  | cons μ s ih => rw [Lorentz.iteratedD_cons, LinearMap.comp_apply, ih, hf, Multiset.cons_add]

/-- The iterated total derivative along `s` appends `s` to the derivative label of a
  fermionic symbol. For `r = 0` it says that `∂_s ψ^φ` is the iterated total derivative of
  the undifferentiated symbol `ψ^φ`. -/
lemma iteratedD_fermionSymbol (i : T.FermionSpecies) (s r : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.FermionValue i)) :
    Lorentz.iteratedD T.totalDeriv T.totalDeriv_comm s (T.fermionSymbol i r φ)
      = T.fermionSymbol i (s + r) φ :=
  iteratedD_of_shift T.totalDeriv T.totalDeriv_comm (fun r => T.fermionSymbol i r φ)
    (fun μ r => totalDeriv_fermionSymbol μ i r φ) s r

/-- The iterated total derivative along `s` appends `s` to the derivative label of a
  conjugate fermionic symbol. -/
lemma iteratedD_conjFermionSymbol (i : T.FermionSpecies)
    (s r : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    Lorentz.iteratedD T.totalDeriv T.totalDeriv_comm s (T.conjFermionSymbol i r φ)
      = T.conjFermionSymbol i (s + r) φ :=
  iteratedD_of_shift T.totalDeriv T.totalDeriv_comm (fun r => T.conjFermionSymbol i r φ)
    (fun μ r => totalDeriv_conjFermionSymbol μ i r φ) s r

/-- The iterated total derivative along `s` appends `s` to the derivative label of a bosonic
  symbol. -/
lemma iteratedD_bosonSymbol (j : T.BosonSpecies) (s r : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (T.BosonValue j)) :
    Lorentz.iteratedD T.totalDeriv T.totalDeriv_comm s (T.bosonSymbol j r φ)
      = T.bosonSymbol j (s + r) φ :=
  iteratedD_of_shift T.totalDeriv T.totalDeriv_comm (fun r => T.bosonSymbol j r φ)
    (fun μ r => totalDeriv_bosonSymbol μ j r φ) s r

/-- The iterated total derivative along `s` appends `s` to the derivative label of a
  conjugate bosonic symbol. -/
lemma iteratedD_conjBosonSymbol (j : T.BosonSpecies) (s r : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    Lorentz.iteratedD T.totalDeriv T.totalDeriv_comm s (T.conjBosonSymbol j r φ)
      = T.conjBosonSymbol j (s + r) φ :=
  iteratedD_of_shift T.totalDeriv T.totalDeriv_comm (fun r => T.conjBosonSymbol j r φ)
    (fun μ r => totalDeriv_conjBosonSymbol μ j r φ) s r

/-!

## I. Lorentz covariance

### I.1. The factorwise action

-/

variable (T) in
/-- The Lorentz action on the fermionic factor, the exterior-algebra functor applied to
  the species-wise Lorentz action on the fermionic generator space. -/
private noncomputable abbrev repLorentzFermionFactor :
    Representation ℂ SL(2,ℂ) (ExteriorAlgebra ℂ T.FermionGenerators) :=
  T.repLorentzFermion.exteriorAlgebra

variable (T) in
/-- The Lorentz action on the bosonic factor. -/
private noncomputable abbrev repLorentzBosonFactor :
    Representation ℂ SL(2,ℂ) (SymmetricAlgebra ℂ T.BosonGenerators) :=
  T.repLorentzBoson.symmetricAlgebra

variable (T) in
/-- The Lorentz action on the local field algebra presented factor by factor, where the three
  factors transform independently. It agrees with `T.repLorentzGroup`. -/
private noncomputable def repLorentzFactorwise : Representation ℂ SL(2,ℂ) T.LocalFieldAlgebra :=
  ((repLorentzFermionFactor T).tprod (repLorentzBosonFactor T)).tprod
    (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup G)

private lemma repLorentzFactorwise_tmul (Λ : SL(2,ℂ))
    (w : ExteriorAlgebra ℂ T.FermionGenerators ⊗[ℂ]
      SymmetricAlgebra ℂ T.BosonGenerators)
    (g : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G) :
    repLorentzFactorwise T Λ (w ⊗ₜ[ℂ] g)
      = (((repLorentzFermionFactor T).tprod (repLorentzBosonFactor T)) Λ w)
          ⊗ₜ[ℂ] (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup G Λ g) := rfl

/-!

### I.2. Multiplicativity

-/

/-- The factorwise Lorentz action is multiplicative. -/
private lemma repLorentzFactorwise_apply_mul (Λ : SL(2,ℂ)) (x y : T.LocalFieldAlgebra) :
    repLorentzFactorwise T Λ (x * y) = repLorentzFactorwise T Λ x * repLorentzFactorwise T Λ y :=
  Representation.tprod_apply_mul _ _
    (Representation.tprod_apply_mul _ _
      (fun Λ' a b => Representation.exteriorAlgebra_apply_mul _ Λ' a b)
      (fun Λ' a b => Representation.symmetricAlgebra_apply_mul _ Λ' a b))
    (fun Λ' a b =>
      _root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup_apply_mul Λ' a b) Λ x y

/-!

### I.3. The action on the three factors

-/

/-- The Lorentz action on the complexified gauge sector fixes the unit. -/
private lemma complexRepLorentzGroup_one (Λ : SL(2,ℂ)) :
    (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup G) Λ
      (1 : ℂ ⊗[ℝ] (LocalGaugeFieldAlgebra G)) = 1 :=
  (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup_tmul Λ 1 1).trans
    (congrArg (fun x => (1 : ℂ) ⊗ₜ[ℝ] x)
      (_root_.LocalGaugeFieldAlgebra.repLorentzGroup_apply_one Λ))

/-- The matter factor of the Lorentz action fixes the unit, by the same abstract
  instantiation as in the gauge action. -/
private lemma repLorentzFactorwise_matter_one (Λ : SL(2,ℂ)) :
    ((repLorentzFermionFactor T).tprod (repLorentzBosonFactor T)) Λ
        (1 : T.MatterAlgebra) = 1 :=
  Representation.tprod_apply_one _ _ Λ
    (Representation.exteriorAlgebra_apply_one _ Λ)
    (Representation.symmetricAlgebra_apply_one _ Λ)

/-- The Lorentz action restricts to the generic connection factor. -/
private lemma repLorentzFactorwise_includeConnection (Λ : SL(2,ℂ))
    (y : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G) :
    repLorentzFactorwise T Λ (T.includeConnection y)
      = T.includeConnection
          (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup G Λ y) :=
  (congrArg (repLorentzFactorwise T Λ) (GaugeFieldData.includeConnection_apply y)).trans
    ((Representation.tprod_apply_one_tmul _ _ Λ (repLorentzFactorwise_matter_one Λ) y).trans
      (GaugeFieldData.includeConnection_apply
        (_root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup G Λ y)).symm)

/-- The Lorentz action restricts to the fermionic factor, where it is the
  exterior-algebra functor applied to the species-wise action of the datum. -/
private lemma repLorentzFactorwise_includeFermionFactor (Λ : SL(2,ℂ))
    (a : ExteriorAlgebra ℂ T.FermionGenerators) :
    repLorentzFactorwise T Λ (T.includeFermion a)
      = T.includeFermion (repLorentzFermionFactor T Λ a) :=
  (congrArg (repLorentzFactorwise T Λ) (GaugeFieldData.includeFermion_apply a)).trans
    ((Representation.tprod_apply_tmul_one _ _ Λ _
        (complexRepLorentzGroup_one Λ)).trans
      ((congrArg (fun w : T.MatterAlgebra =>
            ((w ⊗ₜ[ℂ] (1 : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)) :
              T.LocalFieldAlgebra))
          (Representation.tprod_apply_tmul_one _ _ Λ a
            (Representation.symmetricAlgebra_apply_one _ Λ))).trans
        (GaugeFieldData.includeFermion_apply (repLorentzFermionFactor T Λ a)).symm))

/-- The Lorentz action restricts to the bosonic factor, where it is the
  symmetric-algebra functor applied to the species-wise action of the datum. -/
private lemma repLorentzFactorwise_includeBosonFactor (Λ : SL(2,ℂ))
    (b : SymmetricAlgebra ℂ T.BosonGenerators) :
    repLorentzFactorwise T Λ (T.includeBoson b)
      = T.includeBoson (repLorentzBosonFactor T Λ b) :=
  (congrArg (repLorentzFactorwise T Λ) (GaugeFieldData.includeBoson_apply b)).trans
    ((Representation.tprod_apply_tmul_one _ _ Λ _
        (complexRepLorentzGroup_one Λ)).trans
      ((congrArg (fun w : T.MatterAlgebra =>
            ((w ⊗ₜ[ℂ] (1 : ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G)) :
              T.LocalFieldAlgebra))
          (Representation.tprod_apply_one_tmul _ _ Λ
            (Representation.exteriorAlgebra_apply_one _ Λ) b)).trans
        (GaugeFieldData.includeBoson_apply (repLorentzBosonFactor T Λ b)).symm))

/-!

### I.4. The total derivative is a Lorentz vector for the factorwise action

-/

/-- A factorwise sum of Lorentz-vector derivatives on a tensor product is a Lorentz
  vector, the abstract two-factor assembly, proved by tensor induction at abstract types
  so that it can be instantiated on the local field algebra without rewriting inside it. -/
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
  induction x using TensorProduct.inductionOn with
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

/-- The total derivative is the derivative of the matter factor plus that of the connection
  factor. -/
private lemma totalDeriv_eq_matter_add_connection (ν : Fin 1 ⊕ Fin 3) :
    TensorProduct.map
      (TensorProduct.map (T.totalDerivFermionFactor ν) LinearMap.id
        + TensorProduct.map LinearMap.id (T.totalDerivBosonFactor ν))
      (LinearMap.id (M := ℂ ⊗[ℝ] _root_.LocalGaugeFieldAlgebra G))
      + TensorProduct.map LinearMap.id
        (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G ν)
      = T.totalDeriv ν :=
  congrArg (fun m => m + TensorProduct.map LinearMap.id
    (_root_.LocalGaugeFieldAlgebra.complexJetDeriv G ν))
    (TensorProduct.map_add_left _ _ _)

/-- The derivative of the matter factor is a Lorentz vector for the factorwise action. -/
private lemma repLorentzMatterFactor_deriv (Λ : SL(2,ℂ)) (ν : Fin 1 ⊕ Fin 3)
    (w : ExteriorAlgebra ℂ T.FermionGenerators ⊗[ℂ] SymmetricAlgebra ℂ T.BosonGenerators) :
    ((repLorentzFermionFactor T).tprod (repLorentzBosonFactor T)) Λ
      ((TensorProduct.map (T.totalDerivFermionFactor ν)
          (LinearMap.id (M := SymmetricAlgebra ℂ T.BosonGenerators))
        + TensorProduct.map
          (LinearMap.id (M := ExteriorAlgebra ℂ T.FermionGenerators))
          (T.totalDerivBosonFactor ν)) w)
    = ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a ν : ℝ) : ℂ) •
        (TensorProduct.map (T.totalDerivFermionFactor a)
          (LinearMap.id (M := SymmetricAlgebra ℂ T.BosonGenerators))
          + TensorProduct.map
            (LinearMap.id (M := ExteriorAlgebra ℂ T.FermionGenerators))
            (T.totalDerivBosonFactor a))
        (((repLorentzFermionFactor T).tprod (repLorentzBosonFactor T)) Λ w) := by
  -- The two factor covariances are stated without a type ascription: instantiating the
  -- abstract lemma against an expected type leaves the family and the coefficients as
  -- metavariables, and solving them at this carrier does not terminate.
  have hFermion := fun (ν : Fin 1 ⊕ Fin 3)
      (z : ExteriorAlgebra ℂ T.FermionGenerators) =>
    ExteriorAlgebra.exteriorAlgebra_derivationOfLinear T.repLorentzFermion Λ
      (fun a => T.jetDerivFermion a) ν
      (fun a => (((Lorentz.SL2C.toLorentzGroup Λ).1 a ν : ℝ) : ℂ))
      (fun w => GaugeFieldData.repLorentzFermion_jetDerivFermion Λ ν w) z
  have hBoson := fun (ν : Fin 1 ⊕ Fin 3)
      (z : SymmetricAlgebra ℂ T.BosonGenerators) =>
    SymmetricAlgebra.symmetricAlgebra_derivationOfLinear T.repLorentzBoson Λ
      (fun a => T.jetDerivBoson a) ν
      (fun a => (((Lorentz.SL2C.toLorentzGroup Λ).1 a ν : ℝ) : ℂ))
      (fun w => GaugeFieldData.repLorentzBoson_jetDerivBoson Λ ν w) z
  exact tprod_deriv_sum _ _ _ _ _ Λ ν (fun κ z => hFermion κ z) (fun κ z => hBoson κ z) w

/-- The total derivative is a Lorentz vector for the factorwise action. -/
private lemma repLorentzFactorwise_totalDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (x : T.LocalFieldAlgebra) :
    repLorentzFactorwise T Λ (T.totalDeriv μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        T.totalDeriv a (repLorentzFactorwise T Λ x) :=
  (congrArg
    (fun (L : T.LocalFieldAlgebra →ₗ[ℂ] T.LocalFieldAlgebra) =>
      repLorentzFactorwise T Λ (L x))
    (totalDeriv_eq_matter_add_connection μ).symm).trans
    ((tprod_deriv_sum _ _ _ _ _ Λ μ (repLorentzMatterFactor_deriv Λ)
      (fun κ z => _root_.LocalGaugeFieldAlgebra.complexRepLorentzGroup_jetDeriv Λ κ z) x).trans
    (Finset.sum_congr rfl fun a _ => congrArg
      (fun (L : T.LocalFieldAlgebra →ₗ[ℂ] T.LocalFieldAlgebra) =>
        (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • L (repLorentzFactorwise T Λ x))
      (totalDeriv_eq_matter_add_connection a)))

/-!

### I.5. Agreement with the generic action

-/

/-- The Lorentz action fixes the unit. -/
private lemma repLorentzFactorwise_apply_one (Λ : SL(2,ℂ)) :
    repLorentzFactorwise T Λ (1 : T.LocalFieldAlgebra) = 1 :=
  (congrArg (repLorentzFactorwise T Λ) Algebra.TensorProduct.one_def).trans
    (((repLorentzFactorwise_tmul Λ 1 1).trans (congrArg₂ (TensorProduct.tmul ℂ)
      (repLorentzFactorwise_matter_one Λ) (complexRepLorentzGroup_one Λ))).trans
      Algebra.TensorProduct.one_def.symm)

/-- On each element the factorwise Lorentz action is the generic action of the datum. -/
private lemma repLorentzFactorwise_apply_eq (Λ : SL(2,ℂ)) (x : T.LocalFieldAlgebra) :
    repLorentzFactorwise T Λ x = T.repLorentzGroup Λ x := by
  let Φ : T.LocalFieldAlgebra →ₐ[ℂ] T.LocalFieldAlgebra :=
    AlgHom.ofLinearMap (repLorentzFactorwise T Λ) (repLorentzFactorwise_apply_one Λ)
      (repLorentzFactorwise_apply_mul Λ)
  have h : Φ = T.repLorentzAlgHom Λ := by
    refine GaugeFieldData.algHom_ext (fun i y => ?_) (fun j y => ?_) (fun v => ?_)
    · show repLorentzFactorwise T Λ
          (T.includeFermion (ExteriorAlgebra.ι ℂ (T.inclFermion i y)))
        = T.repLorentzAlgHom Λ (T.ιFermion i y)
      rw [repLorentzFactorwise_includeFermionFactor, Representation.exteriorAlgebra_ι,
        GaugeFieldData.repLorentzAlgHom_ιFermion, GaugeFieldData.repLorentzFermion_inclFermion]
      rfl
    · show repLorentzFactorwise T Λ
          (T.includeBoson (SymmetricAlgebra.ι ℂ _ (T.inclBoson j y)))
        = T.repLorentzAlgHom Λ (T.ιBoson j y)
      rw [repLorentzFactorwise_includeBosonFactor, Representation.symmetricAlgebra_ι,
        GaugeFieldData.repLorentzAlgHom_ιBoson, GaugeFieldData.repLorentzBoson_inclBoson]
      rfl
    · show repLorentzFactorwise T Λ (T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G) v))
        = T.repLorentzAlgHom Λ (T.includeConnection ((1 : ℂ) ⊗ₜ[ℝ]
          SymmetricAlgebra.ι ℝ (GaugeBoson.FieldDerivSpace G) v))
      exact (repLorentzFactorwise_includeConnection Λ _).trans
        (GaugeFieldData.repLorentzAlgHom_includeConnection Λ _).symm
  exact AlgHom.congr_fun h x

variable (T) in
/-- The factorwise Lorentz action is the generic action `T.repLorentzGroup` of the
  field datum. -/
private lemma repLorentzFactorwise_eq : repLorentzFactorwise T = T.repLorentzGroup :=
  MonoidHom.ext fun Λ => LinearMap.ext fun x => repLorentzFactorwise_apply_eq Λ x

/-- The total derivative is a Lorentz vector. The Lorentz action intertwines the total
  derivative through the columns of the Lorentz matrix. -/
lemma repLorentzGroup_totalDeriv (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (x : T.LocalFieldAlgebra) :
    T.repLorentzGroup Λ (T.totalDeriv μ x) =
      ∑ a, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
        T.totalDeriv a (T.repLorentzGroup Λ x) := by
  rw [← repLorentzFactorwise_eq T]
  exact repLorentzFactorwise_totalDeriv Λ μ x

/-- The total derivatives on the local field algebra form a Lorentz derivative for the
  Lorentz action of the field datum. -/
instance instIsLorentzDerivTotalDeriv : Lorentz.IsLorentzDeriv T.repLorentzGroup T.totalDeriv where
  rep_deriv := repLorentzGroup_totalDeriv _ _ _

end GaugeFieldData
