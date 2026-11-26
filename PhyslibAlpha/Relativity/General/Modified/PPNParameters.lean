/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Modified.BransDicke
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Parameterized Post-Newtonian (PPN) solar-system formalism

The ten Will–Nordtvedt PPN parameters, fully conservative and semiconservative theory classes,
embeddings of General Relativity, Brans–Dicke, metric `f(R)`, and Nordström gravity, and classic
weak-field observables (light deflection, Shapiro time delay, perihelion precession, and the
Nordtvedt Strong Equivalence Principle parameter `η_N`).

## i. Overview

The Parameterized Post-Newtonian (PPN) formalism of Nordtvedt and Will characterizes metric theories
of gravity in the weak-field, slow-motion solar-system regime by ten dimensionless real parameters
`(γ, β, ξ, α₁, α₂, α₃, ζ₁, ζ₂, ζ₃, ζ₄)`:
- `γ` measures the spatial curvature produced per unit rest mass.
- `β` measures the degree of nonlinearity in the superposition law for gravity (`g_{00}`).
- `ξ` measures preferred-location effects (Whitehead term).
- `α₁, α₂, α₃` measure preferred-frame (Lorentz-violating) effects.
- `ζ₁, ζ₂, ζ₃, ζ₄` (together with `α₃`) measure violations of global energy-momentum and angular
  momentum conservation.

This module defines `PPNParameters`, the conservation predicates `IsFullyConservative` and
`IsSemiconservative`, the canonical PPN embeddings of General Relativity, `BransDickeTheory`
(bridged to `GeneralRelativity.Modified.BransDicke`), unscreened metric `f(R)` gravity, and
Nordström scalar gravity, and the four benchmark solar-system observable factors.

## ii. Key results

- `PPNParameters`, `IsFullyConservative`, `IsSemiconservative`,
  `IsFullyConservative.isSemiconservative` : Will–Nordtvedt 10-parameter structure and conservation
  hierarchy.
- `grPPN`, `bransDickePPN`, `fRMetricPPN`, `nordstromPPN` : PPN parameter vectors of General
  Relativity, `BransDickeTheory` (`γ = (1 + ω)/(2 + ω)`), metric `f(R)` (`γ = 1/2`), and
  Nordström (`γ = -1`).
- `lightDeflectionFactor`, `shapiroDelayFactor`, `perihelionPrecessionFactor`,
  `nordtvedtParameter` : solar-system observable factors and Strong Equivalence Principle parameter
  `η_N`.
- `lightDeflectionFactor_gr`, `lightDeflectionFactor_nordstrom`,
  `perihelionPrecessionFactor_gr`, `perihelionPrecessionFactor_bransDicke` : exact observable
  values.
- `nordtvedtParameter_gr`, `nordtvedtParameter_bransDicke`, `nordtvedtParameter_fRMetric`,
  `cassini_deviation_bransDickePPN` : Strong Equivalence Principle and Cassini solar-system bounds.

## iii. Table of contents

- A. The ten Will–Nordtvedt PPN parameters and conservation classes
- B. Embeddings of General Relativity and modified gravity theories
- C. Solar-system observables and the Nordtvedt SEP parameter

## iv. References

* Kenneth Nordtvedt, *Equivalence Principle for Massive Bodies. II. Theory*, *Physical Review*
  (1968), Sec. II. [ref: Nordtvedt1968]
* Clifford M. Will, *Theoretical Frameworks for Testing Relativistic Gravity. II. Parametrized
  Post-Newtonian Hydrodynamics and the Nordtvedt Effect*, *The Astrophysical Journal* (1971), Sec.
  II. [ref: Will1971PPN]
* Clifford M. Will and Kenneth Nordtvedt, *Conservation Laws and Preferred Frames in Relativistic
  Gravity. II. Experimental Evidence to Rule Out Preferred-Frame Theories of Gravity*, *The
  Astrophysical Journal* 177, pp. 775-792 (1972). [ref: WillNordtvedt1972]
* Bruno Bertotti, Luciano Iess, and Paolo Tortora, *A Test of General Relativity Using Radio Links
  with the Cassini Spacecraft*, *Nature* 425, pp. 374-376 (2003). [ref: BertottiIessTortora2003]
* Clifford M. Will, *The Confrontation between General Relativity and Experiment*, *Living Reviews
  in Relativity* 17, 4 (2014), Sec. 3 (https://arxiv.org/pdf/1403.7377#page=25). [ref: Will2014]
* Clifford M. Will, *Theory and Experiment in Gravitational Physics* (2018), Ch. 4–5.
  [ref: will_2018_tegp]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace PPN

/-!

## A. The ten Will–Nordtvedt PPN parameters and conservation classes

These definitions encode the ten dimensionless post-Newtonian parameters and the standard hierarchy
separating Lagrangian (semiconservative) theories from fully conservative theories.

-/

/-- The ten dimensionless Will–Nordtvedt Parameterized Post-Newtonian (PPN) parameters of a metric
theory of gravitation. -/
structure PPNParameters where
  /-- Spatial curvature per unit mass (`γ = 1` in GR). -/
  gamma : ℝ
  /-- Nonlinearity in gravitational superposition (`β = 1` in GR). -/
  beta : ℝ
  /-- Preferred-location (Whitehead) parameter (`ξ = 0` in GR). -/
  xi : ℝ
  /-- First preferred-frame parameter (`α₁ = 0` in Lorentz-invariant theories). -/
  alpha1 : ℝ
  /-- Second preferred-frame parameter (`α₂ = 0` in Lorentz-invariant theories). -/
  alpha2 : ℝ
  /-- Third preferred-frame and conservation-violation parameter (`α₃ = 0` in GR). -/
  alpha3 : ℝ
  /-- First energy-momentum non-conservation parameter (`ζ₁ = 0` in GR). -/
  zeta1 : ℝ
  /-- Second energy-momentum non-conservation parameter (`ζ₂ = 0` in GR). -/
  zeta2 : ℝ
  /-- Third energy-momentum non-conservation parameter (`ζ₃ = 0` in GR). -/
  zeta3 : ℝ
  /-- Fourth energy-momentum non-conservation parameter (`ζ₄ = 0` in GR). -/
  zeta4 : ℝ

/-- A metric theory is fully conservative (possessing global 4-momentum and angular momentum
conservation and no preferred-frame effects) when `α₁ = α₂ = α₃ = ζ₁ = ζ₂ = ζ₃ = ζ₄ = 0`. -/
def IsFullyConservative (P : PPNParameters) : Prop :=
  P.alpha1 = 0 ∧ P.alpha2 = 0 ∧ P.alpha3 = 0 ∧
    P.zeta1 = 0 ∧ P.zeta2 = 0 ∧ P.zeta3 = 0 ∧ P.zeta4 = 0

/-- A metric theory is semiconservative (derived from a covariant action principle, so total
4-momentum is conserved) when `α₃ = ζ₁ = ζ₂ = ζ₃ = ζ₄ = 0`. -/
def IsSemiconservative (P : PPNParameters) : Prop :=
  P.alpha3 = 0 ∧ P.zeta1 = 0 ∧ P.zeta2 = 0 ∧ P.zeta3 = 0 ∧ P.zeta4 = 0

/-- Every fully conservative PPN parameter set is semiconservative. -/
lemma IsFullyConservative.isSemiconservative {P : PPNParameters} (h : IsFullyConservative P) :
    IsSemiconservative P :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-!

## B. Embeddings of General Relativity and modified gravity theories

Each classical weak-field gravity model maps into `PPNParameters`, allowing unified comparison of
conservation classes across General Relativity, `BransDickeTheory`, metric `f(R)`, and Nordström.

-/

/-- PPN parameters of Einstein's General Relativity: `γ = 1, β = 1`, all other parameters `0`. -/
def grPPN : PPNParameters where
  gamma := 1
  beta := 1
  xi := 0
  alpha1 := 0
  alpha2 := 0
  alpha3 := 0
  zeta1 := 0
  zeta2 := 0
  zeta3 := 0
  zeta4 := 0

/-- PPN parameters of a massless `BransDickeTheory`: `γ = T.gamma`, `β = 1`, all other parameters
`0`. -/
noncomputable def bransDickePPN (T : BransDicke.BransDickeTheory) : PPNParameters where
  gamma := T.gamma
  beta := 1
  xi := 0
  alpha1 := 0
  alpha2 := 0
  alpha3 := 0
  zeta1 := 0
  zeta2 := 0
  zeta3 := 0
  zeta4 := 0

/-- PPN parameters of unscreened metric `f(R)` gravity (`ω = 0` Brans–Dicke limit):
`γ = 1/2, β = 1`, all other parameters `0`. -/
noncomputable def fRMetricPPN : PPNParameters where
  gamma := 1 / 2
  beta := 1
  xi := 0
  alpha1 := 0
  alpha2 := 0
  alpha3 := 0
  zeta1 := 0
  zeta2 := 0
  zeta3 := 0
  zeta4 := 0

/-- PPN parameters of Nordström conformally flat scalar gravity:
`γ = -1, β = 1 / 2`, all other parameters `0`. -/
noncomputable def nordstromPPN : PPNParameters where
  gamma := -1
  beta := 1 / 2
  xi := 0
  alpha1 := 0
  alpha2 := 0
  alpha3 := 0
  zeta1 := 0
  zeta2 := 0
  zeta3 := 0
  zeta4 := 0

/-- General Relativity is a fully conservative PPN theory. -/
lemma grPPN_isFullyConservative : IsFullyConservative grPPN :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Brans–Dicke scalar–tensor gravity is a fully conservative PPN theory for every
`BransDickeTheory`. -/
lemma bransDickePPN_isFullyConservative (T : BransDicke.BransDickeTheory) :
    IsFullyConservative (bransDickePPN T) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At `ω = 0`, `bransDickePPN ⟨0⟩` coincides with `fRMetricPPN`. -/
lemma bransDickePPN_zero_eq_fRMetricPPN : bransDickePPN ⟨0⟩ = fRMetricPPN := by
  simp [bransDickePPN, fRMetricPPN, BransDicke.BransDickeTheory.gamma, BransDicke.fR_gamma]

/-!

## C. Solar-system observables and the Nordtvedt SEP parameter

Light deflection, Shapiro delay, perihelion precession, and lunar-laser-ranging SEP bounds depend
algebraically on the post-Newtonian parameters carried by `PPNParameters`.

-/

/-- Dimensionless gravitational light-deflection factor `(1 + γ) / 2` relative to the General
Relativity deflection angle `4 G M / (c² b)`. -/
@[simp]
noncomputable def lightDeflectionFactor (P : PPNParameters) : ℝ :=
  (1 + P.gamma) / 2

/-- Dimensionless Shapiro radar time-delay factor `(1 + γ) / 2` relative to General Relativity. -/
@[simp]
noncomputable def shapiroDelayFactor (P : PPNParameters) : ℝ :=
  (1 + P.gamma) / 2

/-- Dimensionless perihelion precession factor `(2 + 2 γ - β) / 3` relative to the General
Relativity advance `6 π G M / (c² a (1 - e²))` for a fully conservative theory. -/
@[simp]
noncomputable def perihelionPrecessionFactor (P : PPNParameters) : ℝ :=
  (2 + 2 * P.gamma - P.beta) / 3

/-- The Nordtvedt parameter `η_N = 4 β - γ - 3 - (10/3) ξ - α₁ + (2/3) α₂ - (2/3) ζ₁ - (1/3) ζ₂`
governing violations of the Strong Equivalence Principle (gravitational self-energy contribution to
passive-to-active gravitational mass ratio) in lunar laser ranging. -/
@[simp]
noncomputable def nordtvedtParameter (P : PPNParameters) : ℝ :=
  4 * P.beta - P.gamma - 3 - (10 / 3) * P.xi - P.alpha1 + (2 / 3) * P.alpha2
    - (2 / 3) * P.zeta1 - (1 / 3) * P.zeta2

/-- In General Relativity, the light-deflection factor is `1`. -/
lemma lightDeflectionFactor_gr : lightDeflectionFactor grPPN = 1 := by
  simp only [lightDeflectionFactor, grPPN]
  norm_num

/-- In Nordström's conformally flat scalar gravity (`γ = -1`), gravitational light deflection
vanishes identically (`(1 + γ)/2 = 0`). -/
lemma lightDeflectionFactor_nordstrom : lightDeflectionFactor nordstromPPN = 0 := by
  simp only [lightDeflectionFactor, nordstromPPN]
  norm_num

/-- In unscreened metric `f(R)` gravity (`γ = 1/2`), light deflection is `3/4` of the General
Relativity prediction. -/
lemma lightDeflectionFactor_fRMetric : lightDeflectionFactor fRMetricPPN = 3 / 4 := by
  simp only [lightDeflectionFactor, fRMetricPPN]
  norm_num

/-- In General Relativity, the perihelion precession factor is `1`. -/
lemma perihelionPrecessionFactor_gr : perihelionPrecessionFactor grPPN = 1 := by
  simp only [perihelionPrecessionFactor, grPPN]
  norm_num

/-- In Nordström's theory (`γ = -1, β = 1/2`), the perihelion precession factor is `-1/6`
(retrograde advance of `-1/6` times the Einstein value). -/
lemma perihelionPrecessionFactor_nordstrom :
    perihelionPrecessionFactor nordstromPPN = -1 / 6 := by
  simp only [perihelionPrecessionFactor, nordstromPPN]
  norm_num

/-- In Brans–Dicke theory (`2 + T.ω ≠ 0`), the perihelion precession factor is
`(4 + 3 ω) / (6 + 3 ω)`. -/
lemma perihelionPrecessionFactor_bransDicke (T : BransDicke.BransDickeTheory)
    (hω : 2 + T.ω ≠ 0) :
    perihelionPrecessionFactor (bransDickePPN T) = (4 + 3 * T.ω) / (6 + 3 * T.ω) := by
  have h3 : 6 + 3 * T.ω ≠ 0 := by intro h; apply hω; linarith
  simp only [perihelionPrecessionFactor, bransDickePPN, BransDicke.BransDickeTheory.gamma]
  rw [BransDicke.gamma_eq_one_sub T.ω hω, div_eq_div_iff (by norm_num) h3]
  field_simp [hω]
  ring

/-- General Relativity satisfies the Strong Equivalence Principle identically (`η_N = 0`). -/
lemma nordtvedtParameter_gr : nordtvedtParameter grPPN = 0 := by
  simp only [nordtvedtParameter, grPPN]
  norm_num

/-- In Brans–Dicke gravity (`2 + T.ω ≠ 0`), the Nordtvedt Strong Equivalence Principle violation
parameter is `η_N = 1 / (2 + ω)`. -/
lemma nordtvedtParameter_bransDicke (T : BransDicke.BransDickeTheory) (hω : 2 + T.ω ≠ 0) :
    nordtvedtParameter (bransDickePPN T) = 1 / (2 + T.ω) := by
  simp only [nordtvedtParameter, bransDickePPN, BransDicke.BransDickeTheory.gamma]
  rw [BransDicke.gamma_eq_one_sub T.ω hω]
  ring

/-- In unscreened metric `f(R)` gravity (`γ = 1/2, β = 1`), the Nordtvedt parameter is
`η_N = 1/2`. -/
lemma nordtvedtParameter_fRMetric : nordtvedtParameter fRMetricPPN = 1 / 2 := by
  simp only [nordtvedtParameter, fRMetricPPN]
  norm_num

/-- Cassini solar-system bound lifted to `bransDickePPN`: `T.ω > 40000` implies
`grPPN.gamma - (bransDickePPN T).gamma < 1 / 40000` and
`nordtvedtParameter (bransDickePPN T) < 1 / 40000`. -/
lemma cassini_deviation_bransDickePPN (T : BransDicke.BransDickeTheory) (hω : 40000 < T.ω) :
    grPPN.gamma - (bransDickePPN T).gamma < 1 / 40000 ∧
      nordtvedtParameter (bransDickePPN T) < 1 / 40000 := by
  have h1 := BransDicke.cassini_deviation T.ω hω
  have h2 : 2 + T.ω ≠ 0 := by linarith
  have h3 := nordtvedtParameter_bransDicke T h2
  have h4 := BransDicke.gamma_eq_one_sub T.ω h2
  rw [h3]
  simp only [grPPN, bransDickePPN, BransDicke.BransDickeTheory.gamma] at *
  constructor <;> linarith

end PPN

end Modified

end GeneralRelativity
