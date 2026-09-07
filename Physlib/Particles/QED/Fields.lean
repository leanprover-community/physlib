/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Basic
public import Physlib.Relativity.PauliMatrices.Basic
/-!
# The fields of quantum electrodynamics

## i. Overview

The fields of QED, defined on top of the jet algebras of `Physlib.Particles.QED.Basic`:
the photon and electron jet coordinates as elements of the QED jet algebra,
the field strength, the Maxwell term, the Dirac γ matrices in the chiral
representation, and the covariant derivatives of the electron and its
conjugate.

This file contains only definitions; the theorems about these fields are
proved in `Physlib.Particles.QED.FermionStatistics`, `Physlib.Particles.QED.FieldStrength`,
`Physlib.Particles.QED.GammaMatrices`, `Physlib.Particles.QED.GaugeInvariance` and
`Physlib.Particles.QED.Evaluation`, and the Lagrangian built from them is defined in
`Physlib.Particles.QED.Lagrangian`.

## ii. Key results

- `Photon.JetAlgebra.fieldStrength`, `Photon.JetAlgebra.maxwellTerm` : the
  field strength and the Maxwell term in the photon jet algebra.
- `JetAlgebra.A`, `JetAlgebra.ψ`, `JetAlgebra.barψ` : the jet coordinates of
  QED.
- `JetAlgebra.fieldStrength`, `JetAlgebra.maxwellTerm` : the field strength
  and the Maxwell term in the QED jet algebra.
- `JetAlgebra.gammaMatrix`, `JetAlgebra.kineticGamma` : the γ matrices in the
  chiral representation and the contraction matrices `γ⁰ γ^μ`.
- `JetAlgebra.covDψ`, `JetAlgebra.covDbarψ` : the covariant derivatives.

## iii. Table of contents

- A. The field strength and Maxwell term of the photon
- B. The jet coordinates of QED
- C. The γ matrices in the chiral representation
- D. The covariant derivatives

## iv. References

The jet algebras are defined in `Physlib.Particles.QED.Basic`; the Lagrangian is
defined in `Physlib.Particles.QED.Lagrangian`.

-/

@[expose] public section

namespace QED

open minkowskiMatrix
open scoped PauliMatrix

namespace Photon

namespace JetAlgebra

/-!

## A. The field strength and Maxwell term of the photon

-/

/-- The formal field strength `∂_s F_{μν} = ∂_s ∂_μ A_ν - ∂_s ∂_ν A_μ`. -/
noncomputable def fieldStrength (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    JetAlgebra :=
  coord (s + {μ}) ν - coord (s + {ν}) μ

/-- The formal Maxwell term `F_{μν} F^{μν}`, both indices raised with the
  (diagonal) Minkowski metric. -/
noncomputable def maxwellTerm : JetAlgebra :=
  ∑ μ, ∑ ν, (η μ μ * η ν ν) • (fieldStrength 0 μ ν * fieldStrength 0 μ ν)

/-- The Maxwell operator `∂_μ F^{μν}`: the divergence of the field strength
  with raised indices.  Its vanishing is the vacuum Maxwell equation; its
  evaluation on an honest potential is the Euler–Lagrange gradient of the
  Maxwell action — see `Physlib.Particles.QED.Evaluation`. -/
noncomputable def maxwellOperator (ν : Fin 1 ⊕ Fin 3) : JetAlgebra :=
  ∑ μ, (η μ μ * η ν ν) • fieldStrength {μ} μ ν

end JetAlgebra

end Photon

namespace JetAlgebra

/-!

## B. The jet coordinates of QED

The photon jet coordinate `∂_s A_μ` and the electron jet coordinates
`∂_s ψ_α`, `∂_s ψ̄_α`, as elements of the QED jet algebra, together with the
field strength and the Maxwell term.

-/

/-- The photon jet coordinate `∂_s A_μ` in the QED jet algebra. -/
noncomputable def A (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    JetAlgebra :=
  ((1 : ℂ) ⊗ₜ[ℝ] Photon.JetAlgebra.coord s μ) ⊗ⱼ 1

/-- The electron jet coordinate `∂_s ψ_α` in the QED jet algebra. -/
noncomputable def ψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) :
    JetAlgebra :=
  1 ⊗ⱼ Electron.JetAlgebra.ofGenerator (.dψ s α)

/-- The conjugate electron jet coordinate `∂_s ψ̄_α` in the QED jet algebra. -/
noncomputable def barψ (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2 ⊕ Fin 2) :
    JetAlgebra :=
  1 ⊗ⱼ Electron.JetAlgebra.ofGenerator (.dbarψ s α)

/-- The formal field strength `∂_s F_{μν}` in the QED jet algebra. -/
noncomputable def fieldStrength (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) : JetAlgebra :=
  ((1 : ℂ) ⊗ₜ[ℝ] Photon.JetAlgebra.fieldStrength s μ ν) ⊗ⱼ 1

/-- The formal Maxwell term `F_{μν} F^{μν}` in the QED jet algebra.  Its
  evaluation on an honest electromagnetic potential is the Maxwell Lagrangian;
  see `Physlib.Particles.QED.Evaluation`. -/
noncomputable def maxwellTerm : JetAlgebra :=
  ((1 : ℂ) ⊗ₜ[ℝ] Photon.JetAlgebra.maxwellTerm) ⊗ⱼ 1

/-!

## C. The γ matrices in the chiral representation

In the chiral representation `γ^μ = ((0, σ^μ), (σ̄^μ, 0))` with
`σ^μ = (1, σ^i)` and `σ̄^μ = (1, -σ^i)`; since the Minkowski matrix is
diagonal, `σ̄^μ = η_{μμ} σ^μ` with no sum over `μ`.

-/

/-- The Dirac γ matrices in the chiral (Weyl) representation:
  `γ^μ = ((0, σ^μ), (σ̄^μ, 0))`, acting on the Dirac index `Fin 2 ⊕ Fin 2`
  whose summands are the left- and right-handed Weyl components. -/
noncomputable def gammaMatrix (μ : Fin 1 ⊕ Fin 3) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 0 (σ μ) (η μ μ • σ μ) 0

/-- The contraction matrices `γ⁰ γ^μ = ((σ̄^μ, 0), (0, σ^μ))` of the Dirac
  kinetic term `i ψ† (γ⁰ γ^μ) D_μ ψ`; see
  `Physlib.Particles.QED.GammaMatrices.kineticGamma_eq_gammaMatrix_mul`. -/
noncomputable def kineticGamma (μ : Fin 1 ⊕ Fin 3) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks (η μ μ • σ μ) 0 0 (σ μ)

/-!

## D. The covariant derivatives

The electron has electric charge `-1`, so `D_μ ψ = ∂_μ ψ + i e A_μ ψ` and
`D_μ ψ̄ = ∂_μ ψ̄ - i e A_μ ψ̄`, with `e` the electric coupling.

-/

/-- The covariant derivative jet `(D_μ ψ)_α = ∂_μ ψ_α + i e A_μ ψ_α` of the
  electron. -/
noncomputable def covDψ (e : ℝ) (μ : Fin 1 ⊕ Fin 3) (α : Fin 2 ⊕ Fin 2) :
    JetAlgebra :=
  ψ {μ} α + (Complex.I * e) • (A 0 μ * ψ 0 α)

/-- The covariant derivative jet `(D_μ ψ̄)_α = ∂_μ ψ̄_α - i e A_μ ψ̄_α` of the
  conjugate electron. -/
noncomputable def covDbarψ (e : ℝ) (μ : Fin 1 ⊕ Fin 3) (α : Fin 2 ⊕ Fin 2) :
    JetAlgebra :=
  barψ {μ} α - (Complex.I * e) • (A 0 μ * barψ 0 α)

end JetAlgebra

end QED
