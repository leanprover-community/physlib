/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Defs
public import PhyslibAlpha.Relativity.General.GravitationalConstant
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

/-!

# Scalar–Tensor–Vector Gravity (MOG / STVG)

Structural properties of Moffat's Modified Gravity (MOG) Yukawa-enhanced potential.

## i. Overview

MOG (Scalar–Tensor–Vector Gravity) introduces a massive vector field mediating a repulsive
Yukawa correction whose net effect is a radius-dependent enhancement of Newton's constant:

`Φ(r) = -(G M / r) (1 + α (1 - e^{-μ r}))`.

The enhancement equals `1` at `r = 0`, reduces to Newtonian gravity at `α = 0` or `μ = 0`, is
strictly bounded in `[1, 1 + α)` for `α > 0` and `μ r ≥ 0`, and approaches `1 + α` asymptotically
at large radius when `μ > 0`.

## ii. Key results

- `MOGTheory`, `MOGTheory.yukawaEnhancementFactor`, `MOGTheory.potential` : MOG theory
  parameterized by `α` and `μ`, enhancement factor, and gravitational potential on
  `G : GravitationalConstant`.
- `MOGTheory.yukawaEnhancementFactor_zero`, `MOGTheory.yukawaEnhancementFactor_alpha_zero`,
  `MOGTheory.yukawaEnhancementFactor_mu_zero` : Newtonian reductions at `r = 0`, `α = 0`, and
  `μ = 0`.
- `MOGTheory.yukawaEnhancementFactor_bounds` : for `T.α > 0` and `T.μ * r ≥ 0`,
  `1 ≤ T.yukawaEnhancementFactor r < 1 + T.α`.
- `MOGTheory.yukawaEnhancementFactor_tendsto_atTop` : for `T.μ > 0`,
  `T.yukawaEnhancementFactor r → 1 + T.α` as `r → ∞`.
- `stvgActionDensity`, `procaResidual`, `mogEinsteinResidual`, `IsMogSolution` : the gravitational
  sector of the STVG action density, the Proca and modified Einstein equations as residuals, and a
  point at which both hold.

## iii. Table of contents

- A. The MOG enhancement factor and potential
- B. Bounds, Newtonian limits, and asymptotic behaviour
- C. The STVG action and field equations at a point

## iv. References

* J. W. Moffat, *Scalar-Tensor-Vector Gravity Theory*, *Journal of Cosmology and Astroparticle
  Physics* (2006), Sec. 2-4 (https://arxiv.org/pdf/gr-qc/0506021#page=3). [ref: Moffat2006STVG]
* J. W. Moffat, *A Modified Gravity and Its Consequences for the Solar System, Astrophysics and
  Cosmology*, *International Journal of Modern Physics D* 16, pp. 2075-2097 (2007), Sec. 2
  (https://arxiv.org/pdf/gr-qc/0608074#page=2). [ref: Moffat2007MOG]
* Sreekanth Harikumar, *Moffat MOdified Gravity (MOG)*, *Universe* 8(5), 259 (2022), Sec. 2-3
  (https://www.mdpi.com/2218-1997/8/5/259/pdf#page=2). [ref: Harikumar2022MOG]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace MOG

/-!

## A. The MOG enhancement factor and potential

In `MOGTheory`, a repulsive massive vector field shifts the effective Newtonian attraction by the
exponential Yukawa factor `1 + α (1 - e^{-μ r})`. This module formalises only the
one-parameter Yukawa form (coupling `α`, inverse range `μ`); it does not derive
`α` or `μ` from the STVG action, and MOG remains a phenomenological alternative to dark matter
whose standing is assessed empirically (e.g. galaxy rotation curves and cluster lensing), not by
these algebraic identities alone.

-/

/-- Moffat's Modified Gravity (MOG / STVG) theory parameterized by coupling strength `α` and
inverse Yukawa range `μ`. -/
structure MOGTheory where
  /-- Dimensionless gravitational enhancement parameter `α`. -/
  α : ℝ
  /-- Inverse Yukawa range parameter `μ`. -/
  μ : ℝ

/-- The MOG enhancement factor `1 + α (1 - e^{-μ r})` of a `MOGTheory`, as a function of the
distance `r`. -/
noncomputable def MOGTheory.yukawaEnhancementFactor (T : MOGTheory) (r : ℝ) : ℝ :=
  1 + T.α * (1 - Real.exp (-(T.μ * r)))

/-- The MOG gravitational potential `-(G M / r)` times the enhancement factor, for a `MOGTheory`,
a Newtonian constant `G : GravitationalConstant`, a source mass `M` and a distance `r`. -/
noncomputable def MOGTheory.potential (T : MOGTheory) (G : GravitationalConstant)
    (M r : ℝ) : ℝ :=
  -((G.val * M) / r) * T.yukawaEnhancementFactor r

/-!

## B. Bounds, Newtonian limits, and asymptotic behaviour

At short distances or vanishing vector couplings the enhancement factor collapses to `1`, while at
large radii it saturates asymptotically at `1 + T.α`.

-/

/-- At `r = 0`, the MOG enhancement factor is exactly `1`. -/
lemma MOGTheory.yukawaEnhancementFactor_zero (T : MOGTheory) :
    T.yukawaEnhancementFactor 0 = 1 := by
  simp [MOGTheory.yukawaEnhancementFactor]

/-- At `T.α = 0`, MOG reduces to Newtonian gravity (`yukawaEnhancementFactor = 1`). -/
lemma MOGTheory.yukawaEnhancementFactor_alpha_zero (μ r : ℝ) :
    (⟨0, μ⟩ : MOGTheory).yukawaEnhancementFactor r = 1 := by
  simp [MOGTheory.yukawaEnhancementFactor]

/-- At `T.μ = 0`, MOG reduces to Newtonian gravity (`yukawaEnhancementFactor = 1`). -/
lemma MOGTheory.yukawaEnhancementFactor_mu_zero (α r : ℝ) :
    (⟨α, 0⟩ : MOGTheory).yukawaEnhancementFactor r = 1 := by
  simp [MOGTheory.yukawaEnhancementFactor]

/-- For positive `T.α` and `T.μ * r ≥ 0`, the MOG enhancement factor lies in `[1, 1 + T.α)`: a
single Yukawa vector cannot absorb a mass discrepancy larger than `1 + T.α`. -/
lemma MOGTheory.yukawaEnhancementFactor_bounds (T : MOGTheory) (r : ℝ) (hα : 0 < T.α)
    (hμr : 0 ≤ T.μ * r) :
    1 ≤ T.yukawaEnhancementFactor r ∧ T.yukawaEnhancementFactor r < 1 + T.α := by
  have hpos : 0 < Real.exp (-(T.μ * r)) := Real.exp_pos _
  have hle : Real.exp (-(T.μ * r)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  constructor
  · simp only [MOGTheory.yukawaEnhancementFactor]
    nlinarith
  · simp only [MOGTheory.yukawaEnhancementFactor]
    nlinarith

/-- For `T.μ > 0`, the MOG enhancement factor tends asymptotically to `1 + T.α` at large
radius. -/
lemma MOGTheory.yukawaEnhancementFactor_tendsto_atTop (T : MOGTheory) (hμ : 0 < T.μ) :
    Filter.Tendsto (fun r : ℝ => T.yukawaEnhancementFactor r) Filter.atTop (nhds (1 + T.α)) := by
  have hmul : Filter.Tendsto (fun r : ℝ => T.μ * r) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hμ Filter.tendsto_id
  have hneg : Filter.Tendsto (fun r : ℝ => -(T.μ * r)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hmul
  have hexp : Filter.Tendsto (fun r : ℝ => Real.exp (-(T.μ * r))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have h1 : Filter.Tendsto (fun r : ℝ => 1 + T.α * (1 - Real.exp (-(T.μ * r))))
      Filter.atTop (nhds (1 + T.α * (1 - 0))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp))
  simpa [MOGTheory.yukawaEnhancementFactor] using h1

/-!

## C. The STVG action and field equations at a point

The gravitational sector combines the Einstein term with a Proca mass term and a scalar potential.
Varying it gives the Proca equation for the massive vector and a modified Einstein equation whose
vector and scalar stress contributions are supplied as data, so the equations are stated as
residuals rather than derived.

-/

/-- The gravitational sector of the STVG action density at a point:
`R / (16 π G) - B² / 4 + μ² φ² / 2 - V`, with `G` the running coupling, `B²` the squared field
strength, `φ² = φ_μ φ^μ` and `V` the scalar potential. The matter coupling is not included. -/
noncomputable def stvgActionDensity (G R B2 phiSq mu V : ℝ) : ℝ :=
  R / (16 * Real.pi * G) - B2 / 4 + mu ^ 2 * phiSq / 2 - V

/-- The Proca field equation `div B + μ² φ = 0` in one frame component, with the divergence of the
field strength and the vector component supplied. -/
noncomputable def procaResidual (divB mu phiComp : ℝ) : ℝ :=
  divB + mu ^ 2 * phiComp

/-- At zero mass the Proca equation is the Maxwell equation `div B = 0`. -/
lemma procaResidual_mu_zero_eq_zero_iff (divB phiComp : ℝ) :
    procaResidual divB 0 phiComp = 0 ↔ divB = 0 := by
  simp [procaResidual]

/-- One component of the modified Einstein equation `G_{μν} = 8 π G T_{μν}`, with the vector and
scalar stress contributions folded into `Ecouple`. -/
noncomputable def mogEinsteinResidual (G Ecouple T : ℝ) : ℝ :=
  Ecouple - 8 * Real.pi * G * T

/-- The modified Einstein equation holds exactly when the coupled Einstein tensor equals `8 π G`
times the source. -/
lemma mogEinsteinResidual_eq_zero_iff (G Ecouple T : ℝ) :
    mogEinsteinResidual G Ecouple T = 0 ↔ Ecouple = 8 * Real.pi * G * T := by
  rw [mogEinsteinResidual, sub_eq_zero]

/-- A point at which the STVG field equations hold. -/
structure IsMogSolution (G Ecouple T divB mu phiComp : ℝ) : Prop where
  /-- The modified Einstein equation holds. -/
  einstein_eq : mogEinsteinResidual G Ecouple T = 0
  /-- The Proca equation holds. -/
  proca_eq : procaResidual divB mu phiComp = 0

end MOG

end Modified

end GeneralRelativity
