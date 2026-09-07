/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Fermions.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.HiggsBoson.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.Basic
/-!
# The jet algebra of the Standard Model

## i. Overview

The full jet algebra of the Standard Model — the algebra in which a Standard Model
Lagrangian lives — is the tensor product of its three sector algebras: the fermionic jet
algebra `FermionJetAlgebra`, the Higgs jet algebra `HiggsJetAlgebra`, and the
(complexified) gauge-boson jet algebra `GaugeJetAlgebra`. The bosonic factors commute with
everything, so the ordinary tensor product is correct; the anticommutativity of the
fermions lives entirely inside the fermionic factor.

This file defines the algebra and its three sector inclusions, and proves that the gauge
sector is central. The Lorentz action, the jet gauge action, the formal total derivative
and the mass-dimension scaling are assembled factorwise in the sibling files.

## ii. Key results

- `JetAlgebra` : the jet algebra of the Standard Model.
- `JetAlgebra.includeFermion`, `includeHiggs`, `includeGauge` : the sector inclusions.
- `JetAlgebra.includeGauge_commute` : the gauge sector is central.
- `Representation.tprod_apply_mul` : multiplicativity of tensor-product representations,
  the generic assembly used by the action files.

## iii. Table of contents

- A. The jet algebra of the Standard Model
  - A.1. The sector inclusions
  - A.2. Centrality of the gauge sector
- B. Tensor products of multiplicative representations

-/

@[expose] public section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups

/-!

## A. The jet algebra of the Standard Model

-/

/-- **The jet algebra of the Standard Model**: the tensor product of the fermionic, Higgs
  and gauge-boson jet algebras. A Standard Model Lagrangian is an element of this
  algebra. -/
abbrev JetAlgebra : Type :=
  (FermionJetAlgebra ⊗[ℂ] HiggsJetAlgebra) ⊗[ℂ] (ℂ ⊗[ℝ] GaugeJetAlgebra)

namespace JetAlgebra

/-!

### A.1. The sector inclusions

-/

/-- The inclusion of the fermionic sector. -/
noncomputable def includeFermion : FermionJetAlgebra →ₐ[ℂ] JetAlgebra :=
  (Algebra.TensorProduct.includeLeft
    (R := ℂ) (S := ℂ) (B := ℂ ⊗[ℝ] GaugeJetAlgebra)).comp
    Algebra.TensorProduct.includeLeft

/-- The inclusion of the Higgs sector. -/
noncomputable def includeHiggs : HiggsJetAlgebra →ₐ[ℂ] JetAlgebra :=
  (Algebra.TensorProduct.includeLeft
    (R := ℂ) (S := ℂ) (B := ℂ ⊗[ℝ] GaugeJetAlgebra)).comp
    Algebra.TensorProduct.includeRight

/-- The inclusion of the gauge sector. -/
noncomputable def includeGauge : (ℂ ⊗[ℝ] GaugeJetAlgebra) →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.includeRight

lemma includeGauge_apply (y : ℂ ⊗[ℝ] GaugeJetAlgebra) :
    includeGauge y
      = ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] (1 : HiggsJetAlgebra)) ⊗ₜ[ℂ] y := rfl

/-!

### A.2. Centrality of the gauge sector

-/

/-- The right factor of a tensor product with a commutative right factor is central:
  the abstract statement, proved by tensor induction at abstract types so that it can be
  instantiated on the jet algebra without rewriting inside it. -/
private lemma tensor_includeRight_comm {A B : Type*} [Ring A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (y : B) (x : A ⊗[ℂ] B) :
    x * Algebra.TensorProduct.includeRight (R := ℂ) (A := A) y
      = Algebra.TensorProduct.includeRight (R := ℂ) (A := A) y * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, mul_zero]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  | tmul w g =>
    rw [show (Algebra.TensorProduct.includeRight (R := ℂ) (A := A) y : A ⊗[ℂ] B)
        = (1 : A) ⊗ₜ[ℂ] y from rfl,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul, mul_comm g y]

/-- The image of the gauge sector is central: gauge-boson symbols commute with
  everything, as bosons must. -/
lemma includeGauge_commute (y : ℂ ⊗[ℝ] GaugeJetAlgebra) (x : JetAlgebra) :
    x * includeGauge y = includeGauge y * x :=
  tensor_includeRight_comm y x

/-!

## B. Tensor products of multiplicative representations

-/

/-- The tensor product of two multiplicative representations on algebras is
  multiplicative. -/
lemma _root_.Representation.tprod_apply_mul {k G A B : Type*} [CommSemiring k] [Monoid G]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (ρ : Representation k G A) (σ : Representation k G B)
    (hρ : ∀ (g : G) (x y : A), ρ g (x * y) = ρ g x * ρ g y)
    (hσ : ∀ (g : G) (x y : B), σ g (x * y) = σ g x * σ g y)
    (g : G) (x y : A ⊗[k] B) :
    (ρ.tprod σ) g (x * y) = (ρ.tprod σ) g x * (ρ.tprod σ) g y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  | tmul a₁ b₁ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | tmul a₂ b₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul,
        show (ρ.tprod σ) g (a₁ ⊗ₜ[k] b₁) = ρ g a₁ ⊗ₜ[k] σ g b₁ from rfl,
        show (ρ.tprod σ) g (a₂ ⊗ₜ[k] b₂) = ρ g a₂ ⊗ₜ[k] σ g b₂ from rfl,
        show (ρ.tprod σ) g ((a₁ * a₂) ⊗ₜ[k] (b₁ * b₂))
          = ρ g (a₁ * a₂) ⊗ₜ[k] σ g (b₁ * b₂) from rfl,
        hρ, hσ, Algebra.TensorProduct.tmul_mul_tmul]

end JetAlgebra

end StandardModel
