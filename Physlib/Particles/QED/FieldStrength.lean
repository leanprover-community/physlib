/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Fields
/-!
# Properties of the field strength

## i. Overview

The structural theorems about the electromagnetic field strength in the jet
algebras of QED: antisymmetry, the expression of the field strength through
the potential coordinates, and the **Bianchi identity**

`∂_λ F_{μν} + ∂_μ F_{νλ} + ∂_ν F_{λμ} = 0`,

the homogeneous half of Maxwell's equations.  In the jet algebra the Bianchi
identity is exact and purely combinatorial: each term is a difference of
second-derivative coordinates, and the six coordinates cancel in pairs because
multiset addition is commutative — Clairaut's theorem is built into the
indexing.

This file contains no definitions, only theorems about the fields of
`Physlib.Particles.QED.Fields`.

## ii. Key results

- `Photon.JetAlgebra.fieldStrength_antisymm`,
  `JetAlgebra.fieldStrength_antisymm` : antisymmetry of the field strength.
- `JetAlgebra.fieldStrength_eq_sub` : the field strength through the
  potential coordinates, `F_{μν} = ∂_μ A_ν - ∂_ν A_μ`.
- `Photon.JetAlgebra.fieldStrength_bianchi`,
  `JetAlgebra.fieldStrength_bianchi` : **the Bianchi identity**.

## iii. Table of contents

- A. The field strength in the photon jet algebra
  - A.1. Antisymmetry
  - A.2. The Bianchi identity
- B. The field strength in the QED jet algebra

## iv. References

The fields are defined in `Physlib.Particles.QED.Fields`.  The inhomogeneous half of
Maxwell's equations is dynamical (it needs the variation of the Lagrangian)
and is not part of the jet-algebra kinematics.

-/

@[expose] public section

namespace QED

open TensorProduct

namespace Photon

namespace JetAlgebra

/-!

## A. The field strength in the photon jet algebra

### A.1. Antisymmetry

-/

theorem fieldStrength_antisymm (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength s μ ν = -fieldStrength s ν μ := by
  simp [fieldStrength]

@[simp]
theorem fieldStrength_self (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    fieldStrength s μ μ = 0 := by
  simp [fieldStrength]

/-!

### A.2. The Bianchi identity

Each field strength is a difference of two second-derivative coordinates; the
cyclic sum produces six coordinates which cancel in pairs, because the
multisets `s + {μ} + {ν}` and `s + {ν} + {μ}` are equal.

-/

/-- **The Bianchi identity** `∂_lam F_{μν} + ∂_μ F_{ν lam} + ∂_ν F_{lam μ} = 0`
  in the photon jet algebra: the homogeneous Maxwell equations hold exactly,
  for every derivative order `s`. -/
theorem fieldStrength_bianchi (s : Multiset (Fin 1 ⊕ Fin 3))
    (lam μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength (s + {lam}) μ ν + fieldStrength (s + {μ}) ν lam +
      fieldStrength (s + {ν}) lam μ = 0 := by
  have h : ∀ a b : Fin 1 ⊕ Fin 3, s + {a} + {b} = s + {b} + {a} := fun a b => by
    rw [add_assoc, add_assoc, add_comm ({a} : Multiset (Fin 1 ⊕ Fin 3))]
  simp only [fieldStrength]
  rw [h lam μ, h lam ν, h μ ν]
  ring

end JetAlgebra

end Photon

namespace JetAlgebra

/-!

## B. The field strength in the QED jet algebra

The theorems of section A, transported through the inclusion of the photon
factor into the QED jet algebra.

-/

/-- The field strength is the antisymmetrised derivative of the potential,
  `∂_s F_{μν} = ∂_s ∂_μ A_ν - ∂_s ∂_ν A_μ`. -/
theorem fieldStrength_eq_sub (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength s μ ν = A (s + {μ}) ν - A (s + {ν}) μ := by
  rw [fieldStrength, Photon.JetAlgebra.fieldStrength, TensorProduct.tmul_sub,
    sub_tmul]
  rfl

theorem fieldStrength_antisymm (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength s μ ν = -fieldStrength s ν μ := by
  simp only [fieldStrength]
  rw [Photon.JetAlgebra.fieldStrength_antisymm, TensorProduct.tmul_neg, neg_tmul]

@[simp]
theorem fieldStrength_self (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    fieldStrength s μ μ = 0 := by
  simp only [fieldStrength, Photon.JetAlgebra.fieldStrength_self,
    TensorProduct.tmul_zero, zero_tmul]

/-- **The Bianchi identity** in the QED jet algebra. -/
theorem fieldStrength_bianchi (s : Multiset (Fin 1 ⊕ Fin 3))
    (lam μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength (s + {lam}) μ ν + fieldStrength (s + {μ}) ν lam +
      fieldStrength (s + {ν}) lam μ = 0 := by
  simp only [fieldStrength]
  rw [← add_tmul, ← add_tmul, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add,
    Photon.JetAlgebra.fieldStrength_bianchi, TensorProduct.tmul_zero, zero_tmul]

/-!

## C. The total derivative on the fields

-/

/-- The first-order field-strength jet is the total derivative of the
  zeroth-order one, in the photon jet algebra. -/
theorem _root_.QED.Photon.JetAlgebra.fieldStrength_singleton_eq_jetDeriv
    (ρ μ ν : Fin 1 ⊕ Fin 3) :
    Photon.JetAlgebra.fieldStrength {ρ} μ ν =
      Photon.JetAlgebra.jetDeriv ρ (Photon.JetAlgebra.fieldStrength 0 μ ν) := by
  rw [Photon.JetAlgebra.fieldStrength, Photon.JetAlgebra.fieldStrength, map_sub,
    Photon.JetAlgebra.jetDeriv_coord, Photon.JetAlgebra.jetDeriv_coord,
    zero_add, zero_add,
    show ({ρ} : Multiset (Fin 1 ⊕ Fin 3)) + {μ} = {μ} + {ρ} from
      Multiset.add_comm _ _,
    show ({ρ} : Multiset (Fin 1 ⊕ Fin 3)) + {ν} = {ν} + {ρ} from
      Multiset.add_comm _ _]

/-- The total derivative appends the derivative index to the photon jet
  coordinate. -/
@[simp]
theorem jetDeriv_A (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) :
    jetDeriv ρ (A s μ) = A (s + {ρ}) μ := by
  simp only [A]
  rw [jetDeriv_tmul, Electron.JetAlgebra.jetDeriv_one, tmul_zero, add_zero,
    LinearMap.baseChange_tmul, Photon.JetAlgebra.jetDeriv_coord]

/-- The total derivative appends the derivative index to the electron jet
  coordinate. -/
@[simp]
theorem jetDeriv_ψ (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (α : Fin 2 ⊕ Fin 2) :
    jetDeriv ρ (ψ s α) = ψ (s + {ρ}) α := by
  simp only [ψ]
  rw [jetDeriv_tmul, show (1 : ℂ ⊗[ℝ] Photon.JetAlgebra) =
      (1 : ℂ) ⊗ₜ[ℝ] (1 : Photon.JetAlgebra) from rfl, LinearMap.baseChange_tmul,
    Photon.JetAlgebra.jetDeriv_one, TensorProduct.tmul_zero, zero_tmul, zero_add,
    Electron.JetAlgebra.jetDeriv_ofGenerator]
  rfl

@[simp]
theorem jetDeriv_barψ (ρ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (α : Fin 2 ⊕ Fin 2) :
    jetDeriv ρ (barψ s α) = barψ (s + {ρ}) α := by
  simp only [barψ]
  rw [jetDeriv_tmul, show (1 : ℂ ⊗[ℝ] Photon.JetAlgebra) =
      (1 : ℂ) ⊗ₜ[ℝ] (1 : Photon.JetAlgebra) from rfl, LinearMap.baseChange_tmul,
    Photon.JetAlgebra.jetDeriv_one, TensorProduct.tmul_zero, zero_tmul, zero_add,
    Electron.JetAlgebra.jetDeriv_ofGenerator]
  rfl

end JetAlgebra

end QED
