/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.QED.Fields
/-!
# The QED Lagrangian

## i. Overview

The Lagrangian of quantum electrodynamics as an element of the QED jet
algebra:

`L = - 1/4 F_{μν} F^{μν} + i ψ̄ γ^μ D_μ ψ - m ψ̄ ψ`,

with `D_μ ψ = ∂_μ ψ + i e A_μ ψ` the covariant derivative of the electron
(electric charge `-1`) and the γ matrices taken in the chiral (Weyl)
representation.  Here `ψ̄` denotes the conjugate jet coordinates `ψ†`; the
`γ⁰` of `ψ̄ = ψ† γ⁰` is kept explicitly in the contraction matrices
`γ⁰ γ^μ` and `γ⁰`.

This file contains only definitions; the gauge invariance of every term and
of the full Lagrangian is proved in `Physlib.Particles.QED.GaugeInvariance`.

## ii. Key results

- `JetAlgebra.diracKineticTerm`, `JetAlgebra.diracKineticTermBar` : the Dirac
  kinetic terms `i ψ̄ γ^μ D_μ ψ` and `-i (D_μ ψ̄) γ⁰ γ^μ ψ`.
- `JetAlgebra.electronMassTerm` : the Dirac mass term `ψ̄ ψ`.
- `JetAlgebra.diracCurrent` : the Dirac current `J^μ = ψ̄ γ^μ ψ`.
- `JetAlgebra.lagrangian` : the QED Lagrangian.

## iii. Table of contents

- A. The Dirac kinetic terms and the mass term
- B. The QED Lagrangian

## iv. References

The fields are defined in `Physlib.Particles.QED.Fields`; gauge invariance is proved in
`Physlib.Particles.QED.GaugeInvariance`.

-/

@[expose] public section

namespace QED

open minkowskiMatrix

namespace JetAlgebra

/-!

## A. The Dirac kinetic terms and the mass term

-/

/-- The Dirac kinetic term `i ψ̄ γ^μ D_μ ψ = i ψ†_α (γ⁰ γ^μ)_{αβ} (D_μ ψ)_β`
  of the electron. -/
noncomputable def diracKineticTerm (e : ℝ) : JetAlgebra :=
  Complex.I • ∑ μ, ∑ α, ∑ β, kineticGamma μ α β • (barψ 0 α * covDψ e μ β)

/-- The conjugate Dirac kinetic term
  `-i (D_μ ψ̄) γ⁰ γ^μ ψ = -i (D_μ ψ̄)_α (γ⁰ γ^μ)_{αβ} ψ_β`; the hermitian form
  of the kinetic term is the average of `diracKineticTerm` and this term. -/
noncomputable def diracKineticTermBar (e : ℝ) : JetAlgebra :=
  (-Complex.I) • ∑ μ, ∑ α, ∑ β, kineticGamma μ α β • (covDbarψ e μ α * ψ 0 β)

/-- The Dirac mass term `ψ̄ ψ = ψ†_α (γ⁰)_{αβ} ψ_β` of the electron.  This is
  the dimension-three term available because the electron is a Dirac fermion:
  its two Weyl components have the same electric charge, so the bilinear
  pairing them against the conjugate components is charge neutral. -/
noncomputable def electronMassTerm : JetAlgebra :=
  ∑ α, ∑ β, gammaMatrix (Sum.inl 0) α β • (barψ 0 α * ψ 0 β)

/-- The Dirac current `J^μ = ψ̄ γ^μ ψ = ψ†_α (γ⁰ γ^μ)_{αβ} ψ_β` of the
  electron: the Noether current of the `U(1)_em` phase symmetry.  Its coupling
  `- e J^μ A_μ` to the photon is the entire interaction of QED — this is the
  jet-algebra counterpart of the current coupling of
  `Physlib.Electromagnetism.Dynamics`; see `Physlib.Particles.QED.CurrentCoupling`. -/
noncomputable def diracCurrent (μ : Fin 1 ⊕ Fin 3) : JetAlgebra :=
  ∑ α, ∑ β, kineticGamma μ α β • (barψ 0 α * ψ 0 β)

/-!

## B. The QED Lagrangian

-/

/-!

## B'. The equations of motion

The Euler–Lagrange equations of the QED Lagrangian, as elements of the jet
algebra whose vanishing expresses the equations of motion.  Deriving them
*variationally* from `lagrangian` requires a variational calculus on the jet
algebra, which is future work; here they are definitions, and
`Physlib.Particles.QED.CurrentCoupling` proves the Noether identity that the
divergence of the Dirac current is a combination of them.

-/

/-- The Dirac-equation element `γ⁰ (i γ^μ D_μ - m) ψ`, row `α`: its vanishing
  is the interacting Dirac equation. -/
noncomputable def diracEquation (e m : ℝ) (α : Fin 2 ⊕ Fin 2) : JetAlgebra :=
  Complex.I • ∑ μ, ∑ β, kineticGamma μ α β • covDψ e μ β -
    (m : ℂ) • ∑ β, gammaMatrix (Sum.inl 0) α β • ψ 0 β

/-- The adjoint Dirac-equation element `i (D_μ ψ̄) γ⁰ γ^μ + m ψ̄ γ⁰`,
  column `β`: its vanishing is the interacting adjoint Dirac equation. -/
noncomputable def diracAdjEquation (e m : ℝ) (β : Fin 2 ⊕ Fin 2) : JetAlgebra :=
  Complex.I • ∑ μ, ∑ α, kineticGamma μ α β • covDbarψ e μ α +
    (m : ℂ) • ∑ α, gammaMatrix (Sum.inl 0) α β • barψ 0 α

/-! TODO: Derive `diracEquation`, `diracAdjEquation` and `qedMaxwellEquation` variationally: -/
/-! TODO: define the Euler–Lagrange operator on the jet algebra (the variational derivative -/
/-! TODO: with respect to each jet coordinate) and prove they are the EL equations of -/
/-! TODO: `lagrangian`, following `Physlib.Electromagnetism.Dynamics.IsExtrema` concretely. -/
/-! TODO: Define the theta term `θ ε^{μνρσ} F_{μν} F_{ρσ}` and prove it is gauge invariant and -/
/-! TODO: a total derivative for `jetDeriv`, as in the lepton–gauge sector's theta term. -/
/-! TODO: Quantize: instantiate the field species of `Physlib.QFT.PerturbationTheory` with the -/
/-! TODO: photon and electron of this file, towards the Feynman rules of QED. -/

/-- The QED Maxwell-equation element `∂_μ F^{μν} - e J^ν`: its vanishing is
  the inhomogeneous Maxwell equation sourced by the Dirac current. -/
noncomputable def qedMaxwellEquation (e : ℝ) (ν : Fin 1 ⊕ Fin 3) : JetAlgebra :=
  (∑ μ, ((η μ μ * η ν ν : ℝ) : ℂ) • fieldStrength {μ} μ ν) -
    (e : ℂ) • diracCurrent ν

/-- The QED Lagrangian
  `L = - 1/4 F_{μν} F^{μν} + i ψ̄ γ^μ D_μ ψ - m ψ̄ ψ`
  with electric coupling `e` and electron mass `m`, as an element of the QED
  jet algebra.  Evaluated on an honest electromagnetic potential, the first
  term is the Maxwell Lagrangian of `Physlib.Electromagnetism`; see
  `Physlib.Particles.QED.Evaluation`. -/
noncomputable def lagrangian (e m : ℝ) : JetAlgebra :=
  (-(1 : ℂ)/4) • maxwellTerm + diracKineticTerm e - (m : ℂ) • electronMassTerm

end JetAlgebra

end QED
