/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Physlib.Thermodynamics.FundamentalRelation.Basic

/-!
# Intensive parameters from a fundamental relation

## i. Overview

In the entropy representation, a simple system is described by a fundamental relation
`S = S(U, V, N)`, where `U` is internal energy, `V` is volume, and `N` is particle number.
For a `FundamentalRelation Φ`, this file names the three coordinate entropy partials, defines
the intensive parameters temperature, pressure, and chemical potential, identifies the total
derivative of `S`, and proves a determination result for fundamental relations.

## ii. Key results

- `FundamentalRelation.dS_dU`, `dS_dV`, `dS_dN` — entropy partial derivatives at a positive
  extensive state.
- `FundamentalRelation.temperature`, `pressure`, `chemicalPotential` — intensive parameters
  in the entropy representation.
- `FundamentalRelation.temperature_pos` — positivity of temperature from
  `FundamentalRelation.dS_dU_pos`.
- `FundamentalRelation.fderiv_S_apply` — the total derivative of `S` as
  `a * ∂S/∂U + b * ∂S/∂V + c * ∂S/∂N`.
- `FundamentalRelation.eq_of_dS_dU_dS_dV_eq_of_eq_at` — exact equality from entropy partials
  and one reference value.

## iii. Table of contents

- A. Entropy partial derivatives
- B. Intensive parameters
- C. Coordinate derivatives and the total differential
- D. Uniqueness from entropy partials

## iv. References

- H.B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed., Wiley
  (1985). -/

@[expose] public section

namespace Thermodynamics

open scoped ContDiff

noncomputable section

/-! ## A. Entropy partial derivatives

For a `FundamentalRelation Φ`, this section names the three coordinate derivatives `∂S/∂U`,
`∂S/∂V`, and `∂S/∂N`. The coordinate partials of the fundamental relation are defined by
fixing two extensive coordinates and differentiating with respect to the third. These are
ordinary one-variable `deriv`s evaluated at a positive `ExtensiveState`. -/

/-- The energy partial derivative `∂S/∂U` at a positive extensive state.

In the entropy differential, this is the coefficient `1 / T` of `dU`. -/
def FundamentalRelation.dS_dU (Φ : FundamentalRelation) (e : ExtensiveState) : ℝ :=
  deriv (fun u => Φ.S u e.V e.N) e.U

/-- The volume partial derivative `∂S/∂V` at a positive extensive state.

In the entropy differential, this is the coefficient `P / T` of `dV`. -/
def FundamentalRelation.dS_dV (Φ : FundamentalRelation) (e : ExtensiveState) : ℝ :=
  deriv (fun v => Φ.S e.U v e.N) e.V

/-- The particle-number partial derivative `∂S/∂N` at a positive extensive state.

In the entropy differential, this is the coefficient `-μ / T` of `dN`. -/
def FundamentalRelation.dS_dN (Φ : FundamentalRelation) (e : ExtensiveState) : ℝ :=
  deriv (fun n => Φ.S e.U e.V n) e.N

/-! ## B. Intensive parameters

The intensive parameters are obtained from the entropy differential

`dS = (1 / T) dU + (P / T) dV - (μ / T) dN`.

They are recovered from the entropy partials by solving

`∂S/∂U = 1 / T`, `∂S/∂V = P / T`, and `∂S/∂N = -μ / T`.

This section defines the corresponding temperature, pressure, and chemical potential, and
proves `T > 0` from the assumed positivity of `∂S/∂U`. The definitions here are real-valued
coordinate functions on positive extensive states; no particular equation of state is
assumed. -/

/-- Temperature as the reciprocal of the energy derivative of entropy:
`T = (∂S/∂U)⁻¹`. -/
def FundamentalRelation.temperature (Φ : FundamentalRelation) (e : ExtensiveState) : ℝ :=
  (Φ.dS_dU e)⁻¹

/-- Pressure from the entropy representation: `P = T * ∂S/∂V`. -/
def FundamentalRelation.pressure (Φ : FundamentalRelation) (e : ExtensiveState) : ℝ :=
  Φ.temperature e * Φ.dS_dV e

/-- Chemical potential from the entropy representation: `μ = -T * ∂S/∂N`. -/
def FundamentalRelation.chemicalPotential (Φ : FundamentalRelation) (e : ExtensiveState) : ℝ :=
  -Φ.temperature e * Φ.dS_dN e

/-- Temperature is positive on positive extensive states.

This is the reciprocal form of Postulate III's monotonicity condition `∂S/∂U > 0`, recorded
here as `FundamentalRelation.dS_dU_pos`. -/
lemma FundamentalRelation.temperature_pos (Φ : FundamentalRelation) (e : ExtensiveState) :
    0 < Φ.temperature e := by
  have h := Φ.dS_dU_pos e.U e.V e.N e.hU e.hV e.hN
  simpa [FundamentalRelation.temperature, FundamentalRelation.dS_dU] using inv_pos.mpr h

/-! ## C. Coordinate derivatives and the total differential

The smoothness field of `FundamentalRelation` is a joint regularity statement for
`S(U, V, N)` on the positive orthant. The lemmas in this section extract differentiability of
the one-coordinate maps and then compute the Fréchet derivative in terms of the three
coordinate partials. -/

/-- The positive orthant is open in `ℝ × ℝ × ℝ`.

This lets the joint `ContDiffOn` hypothesis be used as differentiability at each positive
extensive state. -/
lemma isOpen_posOrthant : IsOpen posOrthant := by
  have hset : posOrthant =
      {p : ℝ × ℝ × ℝ | 0 < p.1} ∩ {p | 0 < p.2.1} ∩ {p | 0 < p.2.2} := by
    ext p
    simp only [posOrthant, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [hset]
  exact ((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd))).inter
    (isOpen_lt continuous_const (continuous_snd.comp continuous_snd))

/-- The one-coordinate map `u ↦ S(u, V, N)` is differentiable at a positive extensive
state. -/
lemma FundamentalRelation.differentiableAt_slice_U (Φ : FundamentalRelation)
    (e : ExtensiveState) :
    DifferentiableAt ℝ (fun u => Φ.S u e.V e.N) e.U := by
  change DifferentiableAt ℝ ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
    fun u : ℝ => (u, (e.V, e.N))) e.U
  have hmem : (e.U, e.V, e.N) ∈ posOrthant := e.mem_posOrthant
  have hjoint : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2)
      (e.U, e.V, e.N) :=
    (Φ.smooth.contDiffAt (isOpen_posOrthant.mem_nhds hmem)).differentiableAt (by norm_num)
  have hline : DifferentiableAt ℝ (fun u : ℝ => (u, e.V, e.N)) e.U := by
    fun_prop
  exact hjoint.comp e.U hline

/-- The one-coordinate map `v ↦ S(U, v, N)` is differentiable at a positive extensive
state. -/
lemma FundamentalRelation.differentiableAt_slice_V (Φ : FundamentalRelation)
    (e : ExtensiveState) :
    DifferentiableAt ℝ (fun v => Φ.S e.U v e.N) e.V := by
  change DifferentiableAt ℝ ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
    fun v : ℝ => (e.U, (v, e.N))) e.V
  have hmem : (e.U, e.V, e.N) ∈ posOrthant := e.mem_posOrthant
  have hjoint : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2)
      (e.U, e.V, e.N) :=
    (Φ.smooth.contDiffAt (isOpen_posOrthant.mem_nhds hmem)).differentiableAt (by norm_num)
  have hline : DifferentiableAt ℝ (fun v : ℝ => (e.U, v, e.N)) e.V := by
    fun_prop
  exact hjoint.comp e.V hline

/-- The one-coordinate map `n ↦ S(U, V, n)` is differentiable at a positive extensive
state. -/
lemma FundamentalRelation.differentiableAt_slice_N (Φ : FundamentalRelation)
    (e : ExtensiveState) :
    DifferentiableAt ℝ (fun n => Φ.S e.U e.V n) e.N := by
  change DifferentiableAt ℝ ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
    fun n : ℝ => (e.U, (e.V, n))) e.N
  have hmem : (e.U, e.V, e.N) ∈ posOrthant := e.mem_posOrthant
  have hjoint : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2)
      (e.U, e.V, e.N) :=
    (Φ.smooth.contDiffAt (isOpen_posOrthant.mem_nhds hmem)).differentiableAt (by norm_num)
  have hline : DifferentiableAt ℝ (fun n : ℝ => (e.U, e.V, n)) e.N := by
    fun_prop
  exact hjoint.comp e.N hline

/-- The definition of `∂S/∂U` gives the corresponding `HasDerivAt` statement in the energy
coordinate. -/
lemma FundamentalRelation.hasDerivAt_dS_dU (Φ : FundamentalRelation) (e : ExtensiveState) :
    HasDerivAt (fun u => Φ.S u e.V e.N) (Φ.dS_dU e) e.U :=
  (Φ.differentiableAt_slice_U e).hasDerivAt

/-- The definition of `∂S/∂V` gives the corresponding `HasDerivAt` statement in the volume
coordinate. -/
lemma FundamentalRelation.hasDerivAt_dS_dV (Φ : FundamentalRelation) (e : ExtensiveState) :
    HasDerivAt (fun v => Φ.S e.U v e.N) (Φ.dS_dV e) e.V :=
  (Φ.differentiableAt_slice_V e).hasDerivAt

/-- The definition of `∂S/∂N` gives the corresponding `HasDerivAt` statement in the
particle-number coordinate. -/
lemma FundamentalRelation.hasDerivAt_dS_dN (Φ : FundamentalRelation) (e : ExtensiveState) :
    HasDerivAt (fun n => Φ.S e.U e.V n) (Φ.dS_dN e) e.N :=
  (Φ.differentiableAt_slice_N e).hasDerivAt

/-- The joint entropy map is Fréchet-differentiable at a positive extensive state. -/
lemma FundamentalRelation.hasFDerivAt_joint (Φ : FundamentalRelation) (e : ExtensiveState) :
    HasFDerivAt (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2)
      (fderiv ℝ (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) (e.U, e.V, e.N))
      (e.U, e.V, e.N) := by
  have hmem : (e.U, e.V, e.N) ∈ posOrthant := e.mem_posOrthant
  have hdiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) (e.U, e.V, e.N) :=
    (Φ.smooth.contDiffAt (isOpen_posOrthant.mem_nhds hmem)).differentiableAt (by norm_num)
  exact hdiff.hasFDerivAt

/-- The total derivative of `S` expressed through its coordinate partials:

`D S(e) (a, b, c) = a * ∂S/∂U + b * ∂S/∂V + c * ∂S/∂N`.

This is the formal version of `dS = (1/T)dU + (P/T)dV - (μ/T)dN`. -/
lemma FundamentalRelation.fderiv_S_apply (Φ : FundamentalRelation) (e : ExtensiveState)
    (a b c : ℝ) :
    (fderiv ℝ (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) (e.U, e.V, e.N))
        (a, b, c)
      = a * Φ.dS_dU e + b * Φ.dS_dV e + c * Φ.dS_dN e := by
  set D := fderiv ℝ (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2)
    (e.U, e.V, e.N) with hD
  have hfderiv : HasFDerivAt (fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2)
      D (e.U, e.V, e.N) :=
    Φ.hasFDerivAt_joint e
  have hDU : D (1, 0, 0) = Φ.dS_dU e := by
    have hline : HasDerivAt (fun u : ℝ => (u, e.V, e.N)) (1, 0, 0) e.U :=
      (hasDerivAt_id e.U).prodMk (hasDerivAt_const e.U (e.V, e.N))
    have hcomp : HasDerivAt (fun u => Φ.S u e.V e.N) (D (1, 0, 0)) e.U := by
      change HasDerivAt ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
        fun u : ℝ => (u, (e.V, e.N))) (D (1, 0, 0)) e.U
      exact hfderiv.comp_hasDerivAt e.U hline
    exact hcomp.unique (Φ.hasDerivAt_dS_dU e)
  have hDV : D (0, 1, 0) = Φ.dS_dV e := by
    have hline : HasDerivAt (fun v : ℝ => (e.U, v, e.N)) (0, 1, 0) e.V :=
      (hasDerivAt_const e.V e.U).prodMk
        ((hasDerivAt_id e.V).prodMk (hasDerivAt_const e.V e.N))
    have hcomp : HasDerivAt (fun v => Φ.S e.U v e.N) (D (0, 1, 0)) e.V := by
      change HasDerivAt ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
        fun v : ℝ => (e.U, (v, e.N))) (D (0, 1, 0)) e.V
      exact hfderiv.comp_hasDerivAt e.V hline
    exact hcomp.unique (Φ.hasDerivAt_dS_dV e)
  have hDN : D (0, 0, 1) = Φ.dS_dN e := by
    have hline : HasDerivAt (fun n : ℝ => (e.U, e.V, n)) (0, 0, 1) e.N :=
      (hasDerivAt_const e.N e.U).prodMk
        ((hasDerivAt_const e.N e.V).prodMk (hasDerivAt_id e.N))
    have hcomp : HasDerivAt (fun n => Φ.S e.U e.V n) (D (0, 0, 1)) e.N := by
      change HasDerivAt ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
        fun n : ℝ => (e.U, (e.V, n))) (D (0, 0, 1)) e.N
      exact hfderiv.comp_hasDerivAt e.N hline
    exact hcomp.unique (Φ.hasDerivAt_dS_dN e)
  have hsplit : ((a, b, c) : ℝ × ℝ × ℝ)
      = a • (1, 0, 0) + b • (0, 1, 0) + c • (0, 0, 1) := by
    simp [Prod.smul_mk, smul_eq_mul]
  rw [hsplit, map_add, map_add, map_smul, map_smul, map_smul, hDU, hDV, hDN]
  simp [smul_eq_mul]

/-! ## D. Uniqueness from entropy partials

The last lemmas show that a fundamental relation can be determined from its entropy partials
and one normalization value. The one-dimensional helper says that a function with zero
derivative everywhere on `Ioi 0` is constant there.

The main theorem applies this to the residual `Φ.S - Ψ.S`. Equality of the `U` and `V`
entropy partials makes the residual independent of those coordinates. Extensivity controls
the remaining scaling direction, and agreement at one positive reference state makes the
residual vanish everywhere. -/

/-- A one-dimensional helper: if a real function has zero derivative everywhere on
`Ioi 0`, then it is constant on `Ioi 0`. -/
private lemma eq_on_Ioi_of_hasDerivAt_zero {f : ℝ → ℝ}
    (hf : ∀ {x : ℝ}, 0 < x → HasDerivAt f 0 x)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f x = f y := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioi (0 : ℝ)) := by
    intro z hz
    exact ((hf hz).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn (deriv f) 0 (Set.Ioi (0 : ℝ)) := by
    intro z hz
    exact (hf hz).deriv
  exact (isOpen_Ioi (a := (0 : ℝ))).is_const_of_deriv_eq_zero
    (isPreconnected_Ioi (a := (0 : ℝ))) hdiff hderiv hx hy

/-- Uniqueness of a fundamental relation from its entropy partials and one reference value.

If two fundamental relations have the same `∂S/∂U` and `∂S/∂V` at every positive extensive
state, and agree at one positive reference state, then the residual `Φ.S - Ψ.S` vanishes
everywhere on the positive orthant. Equivalently, the two fundamental relations agree exactly
on positive extensive states. -/
lemma FundamentalRelation.eq_of_dS_dU_dS_dV_eq_of_eq_at
    (Φ Ψ : FundamentalRelation) {U0 V0 N0 : ℝ}
    (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0)
    (hU : ∀ e : ExtensiveState, Φ.dS_dU e = Ψ.dS_dU e)
    (hV : ∀ e : ExtensiveState, Φ.dS_dV e = Ψ.dS_dV e)
    (href : Φ.S U0 V0 N0 = Ψ.S U0 V0 N0) :
    ∀ e : ExtensiveState, Φ.S e.U e.V e.N = Ψ.S e.U e.V e.N := by
  let sResidual : ℝ → ℝ → ℝ → ℝ := fun U V N => Φ.S U V N - Ψ.S U V N
  have hResidual_hasDerivAt_U :
      ∀ {U V N : ℝ}, 0 < U → 0 < V → 0 < N →
        HasDerivAt (fun u => sResidual u V N) 0 U := by
    intro U V N hUpos hVpos hNpos
    let e : ExtensiveState := ExtensiveState.mk U V N hUpos hVpos hNpos
    have hΦ := Φ.hasDerivAt_dS_dU e
    have hΨ := Ψ.hasDerivAt_dS_dU e
    have hres : HasDerivAt ((fun u => Φ.S u V N) - fun u => Ψ.S u V N)
        (Φ.dS_dU e - Ψ.dS_dU e) U := by
      simpa [e] using hΦ.sub hΨ
    have hzero : Φ.dS_dU e - Ψ.dS_dU e = 0 := by
      rw [hU e]
      ring
    have hres0 : HasDerivAt ((fun u => Φ.S u V N) - fun u => Ψ.S u V N) 0 U := by
      simpa [hzero] using hres
    convert hres0 using 1
    ext u
    simp [sResidual]
  have hResidual_hasDerivAt_V :
      ∀ {U V N : ℝ}, 0 < U → 0 < V → 0 < N →
        HasDerivAt (fun v => sResidual U v N) 0 V := by
    intro U V N hUpos hVpos hNpos
    let e : ExtensiveState := ExtensiveState.mk U V N hUpos hVpos hNpos
    have hΦ := Φ.hasDerivAt_dS_dV e
    have hΨ := Ψ.hasDerivAt_dS_dV e
    have hres : HasDerivAt ((fun v => Φ.S U v N) - fun v => Ψ.S U v N)
        (Φ.dS_dV e - Ψ.dS_dV e) V := by
      simpa [e] using hΦ.sub hΨ
    have hzero : Φ.dS_dV e - Ψ.dS_dV e = 0 := by
      rw [hV e]
      ring
    have hres0 : HasDerivAt ((fun v => Φ.S U v N) - fun v => Ψ.S U v N) 0 V := by
      simpa [hzero] using hres
    convert hres0 using 1
    ext v
    simp [sResidual]
  have hConstU :
      ∀ {U₁ U₂ V N : ℝ}, 0 < U₁ → 0 < U₂ → 0 < V → 0 < N →
        sResidual U₁ V N = sResidual U₂ V N := by
    intro U₁ U₂ V N hU₁ hU₂ hVpos hNpos
    exact eq_on_Ioi_of_hasDerivAt_zero
      (fun hUpos => hResidual_hasDerivAt_U hUpos hVpos hNpos) hU₁ hU₂
  have hConstV :
      ∀ {U V₁ V₂ N : ℝ}, 0 < U → 0 < V₁ → 0 < V₂ → 0 < N →
        sResidual U V₁ N = sResidual U V₂ N := by
    intro U V₁ V₂ N hUpos hV₁ hV₂ hNpos
    exact eq_on_Ioi_of_hasDerivAt_zero
      (fun hVpos => hResidual_hasDerivAt_V hUpos hVpos hNpos) hV₁ hV₂
  have hConstUV :
      ∀ {U₁ U₂ V₁ V₂ N : ℝ}, 0 < U₁ → 0 < U₂ → 0 < V₁ → 0 < V₂ → 0 < N →
        sResidual U₁ V₁ N = sResidual U₂ V₂ N := by
    intro U₁ U₂ V₁ V₂ N hU₁ hU₂ hV₁ hV₂ hNpos
    calc
      sResidual U₁ V₁ N = sResidual U₂ V₁ N := hConstU hU₁ hU₂ hV₁ hNpos
      _ = sResidual U₂ V₂ N := hConstV hU₂ hV₁ hV₂ hNpos
  have hResidual_hom :
      ∀ {l : ℝ}, 0 < l →
        sResidual (l * U0) (l * V0) (l * N0) = l * sResidual U0 V0 N0 := by
    intro l hl
    have hΦ := Φ.homogeneous hl U0 V0 N0 hU0 hV0 hN0
    have hΨ := Ψ.homogeneous hl U0 V0 N0 hU0 hV0 hN0
    dsimp [sResidual]
    rw [hΦ, hΨ]
    ring
  intro e
  let l : ℝ := e.N / N0
  have hl : 0 < l := div_pos e.hN hN0
  have hNl : l * N0 = e.N := by
    dsimp [l]
    field_simp [hN0.ne']
  have hzero : sResidual e.U e.V e.N = 0 := by
    calc
      sResidual e.U e.V e.N = sResidual (l * U0) (l * V0) e.N :=
        hConstUV e.hU (mul_pos hl hU0) e.hV (mul_pos hl hV0) e.hN
      _ = sResidual (l * U0) (l * V0) (l * N0) := by rw [hNl]
      _ = l * sResidual U0 V0 N0 := hResidual_hom hl
      _ = 0 := by simp [sResidual, href]
  dsimp [sResidual] at hzero
  exact sub_eq_zero.mp hzero

end

end Thermodynamics
