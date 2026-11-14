/-
Copyright (c) 2025 Fabio Anza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitch Scheffer, Fabio Anza, Nathaneal Sajan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Physlib.Thermodynamics.FundamentalRelation.Intensive

/-!
# Ideal gas: entropy, equations of state, and characterization

## i. Overview

This module formalizes the single-component simple ideal gas in the entropy representation.
The entropy is

`S(U,V,N) = N * s0 + N * R *
  (c * log (U/U0) + log (V/V0) - (c+1) * log (N/N0))`.

The first part records this entropy formula and two equivalent forms of the fixed-`N`
adiabatic relation. The rest of the file connects the entropy formula to the general
`FundamentalRelation` interface: it proves the needed coordinate derivatives and extensivity,
packages the entropy as a `FundamentalRelation`, and derives the mechanical and caloric
equations of state.

The final theorem is a converse statement. If a `FundamentalRelation` satisfies the ideal-gas
mechanical equation `PV = NRT`, the caloric equation `U = cNRT`, and agrees with the ideal-gas
entropy at one positive reference state, then it agrees with the ideal-gas entropy at every
positive extensive state. This is determination of the fundamental equation from equations of
state and one normalization value.

## ii. Key results

- `entropy` - the simple ideal-gas entropy in the entropy representation.
- `adiabatic_relation_log`, `adiabatic_relation_UaUbVaVb` - fixed-`N` adiabatic relations.
- `idealGasFR` - the ideal-gas entropy packaged as a `FundamentalRelation`.
- `idealGas_law`, `idealGas_caloric` - the equations of state `PV = NRT` and `U = cNRT`.
- `idealGas_characterization` - determination of the entropy from those equations of state
  and one reference value.

## iii. Table of contents

- A. Entropy and adiabatic relations
- B. Coordinate derivatives and extensivity
- C. The ideal-gas fundamental relation
- D. Equations of state
- E. Determination from equations of state

## iv. References

- H.B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed., Wiley
  (1985).
-/

@[expose] public section

open Real
open scoped ContDiff

noncomputable section

namespace Thermodynamics.IdealGas

/-! ## A. Entropy and adiabatic relations

The file starts with the entropy formula for a single-component simple ideal gas and the
fixed-particle-number adiabatic relation obtained by equating that entropy at two states. -/

/-- Entropy of a monophase ideal gas:
    S(U,V,N) = N s0 + N R (c log(U/U0) + log(V/V0) - (c+1) log(N/N0)). -/
def entropy
    (c R s0 U0 V0 N0 : ℝ) (U V N : ℝ) : ℝ :=
  N * s0 +
    N * R *
      (c * log (U / U0) +
        log (V / V0) -
        (c + 1) * log (N / N0))

/-- Adiabatic relation in logarithmic form:
    If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed,
    then c * log (Ua/Ub) + log (Va/Vb) = 0.
-/
lemma adiabatic_relation_log
    {s0 U0 V0 N0 c R : ℝ}
    {Ua Ub Va Vb N : ℝ}
    (hUa : 0 < Ua) (hUb : 0 < Ub)
    (hVa : 0 < Va) (hVb : 0 < Vb)
    (hN : 0 < N)
    (hU0 : 0 < U0) (hV0 : 0 < V0)
    (hR : 0 < R)
    (hS :
      entropy c R s0 U0 V0 N0 Ua Va N =
      entropy c R s0 U0 V0 N0 Ub Vb N) :
    c * log (Ua / Ub) + log (Va / Vb) = 0 := by
  -- Unfold the entropy and expand every `log (x / y)` into `log x - log y`,
  -- so both `hS` and the goal become linear in the individual logarithms.
  unfold entropy at hS
  rw [Real.log_div hUa.ne' hU0.ne', Real.log_div hUb.ne' hU0.ne',
      Real.log_div hVa.ne' hV0.ne', Real.log_div hVb.ne' hV0.ne'] at hS
  rw [Real.log_div hUa.ne' hUb.ne', Real.log_div hVa.ne' hVb.ne']
  -- The difference of the two entropies is `N * R` times the goal, so the
  -- goal is exactly the second factor of a vanishing product.
  have key : N * R * (c * (log Ua - log Ub) + (log Va - log Vb)) = 0 := by
    linear_combination hS
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hN.ne' hR.ne')

/-- Adiabatic relation in product form:
    If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed,
    then (Ua/Ub)^c * (Va/Vb) = 1.
-/
lemma adiabatic_relation_UaUbVaVb
    {s0 U0 V0 N0 c R : ℝ}
    {Ua Ub Va Vb N : ℝ}
    (hUa : 0 < Ua) (hUb : 0 < Ub)
    (hVa : 0 < Va) (hVb : 0 < Vb)
    (hN : 0 < N)
    (hU0 : 0 < U0) (hV0 : 0 < V0)
    (hR : 0 < R)
    (hS :
      entropy c R s0 U0 V0 N0 Ua Va N =
      entropy c R s0 U0 V0 N0 Ub Vb N) :
    (Real.rpow (Ua / Ub) c) * (Va / Vb) = 1 := by
    have hlog := adiabatic_relation_log hUa hUb hVa hVb hN hU0 hV0 hR hS
    -- The product is `exp` of the left-hand side of `hlog`, i.e. `exp 0 = 1`.
    show (Ua / Ub) ^ c * (Va / Vb) = 1
    rw [Real.rpow_def_of_pos (div_pos hUa hUb), ← Real.exp_log (div_pos hVa hVb),
        ← Real.exp_add, mul_comm (log (Ua / Ub)) c, hlog, Real.exp_zero]

/-! ## B. Coordinate derivatives and extensivity

The next lemmas compute the `U` and `V` coordinate derivatives of the ideal-gas entropy and
prove degree-one homogeneity on the positive orthant. These are the ingredients needed to
construct the `FundamentalRelation` below. -/

/-- Energy-coordinate derivative of the ideal-gas entropy:
`∂S/∂U = N * R * c / U`. -/
lemma hasDerivAt_entropy_U (c R s0 U0 V0 N0 U V N : ℝ)
    (hU : 0 < U) (hU0 : 0 < U0) :
    HasDerivAt (fun u => entropy c R s0 U0 V0 N0 u V N) (N * R * c / U) U := by
  have hlogU : HasDerivAt (fun u => log (u / U0)) (1 / U) U := by
    change HasDerivAt (log ∘ fun u : ℝ => u / U0) (1 / U) U
    have hquot : HasDerivAt (fun u : ℝ => u / U0) (1 / U0) U := by
      simpa using (hasDerivAt_id U).div_const U0
    have hlog := (Real.hasDerivAt_log (div_ne_zero hU.ne' hU0.ne')).comp U hquot
    have hval : U0 / U * U0⁻¹ = U⁻¹ := by
      field_simp [hU.ne', hU0.ne']
    simpa [one_div, hval] using hlog
  have hbracket : HasDerivAt
      (fun u => c * log (u / U0) + log (V / V0) - (c + 1) * log (N / N0))
      (c * (1 / U)) U := by
    exact ((hlogU.const_mul c).add_const _).sub_const _
  have htotal : HasDerivAt
      (fun u => N * s0 + N * R *
        (c * log (u / U0) + log (V / V0) - (c + 1) * log (N / N0)))
      (N * R * (c * (1 / U))) U := by
    exact (hbracket.const_mul (N * R)).const_add (N * s0)
  have hval : N * R * (c * U⁻¹) = N * R * c / U := by
    ring
  simpa [entropy, one_div, hval] using htotal

/-- Volume-coordinate derivative of the ideal-gas entropy: `∂S/∂V = N * R / V`. -/
lemma hasDerivAt_entropy_V (c R s0 U0 V0 N0 U V N : ℝ)
    (hV : 0 < V) (hV0 : 0 < V0) :
    HasDerivAt (fun v => entropy c R s0 U0 V0 N0 U v N) (N * R / V) V := by
  have hlogV : HasDerivAt (fun v => log (v / V0)) (1 / V) V := by
    change HasDerivAt (log ∘ fun v : ℝ => v / V0) (1 / V) V
    have hquot : HasDerivAt (fun v : ℝ => v / V0) (1 / V0) V := by
      simpa using (hasDerivAt_id V).div_const V0
    have hlog := (Real.hasDerivAt_log (div_ne_zero hV.ne' hV0.ne')).comp V hquot
    have hval : V0 / V * V0⁻¹ = V⁻¹ := by
      field_simp [hV.ne', hV0.ne']
    simpa [one_div, hval] using hlog
  have hbracket : HasDerivAt
      (fun v => c * log (U / U0) + log (v / V0) - (c + 1) * log (N / N0))
      (1 / V) V := by
    exact (hlogV.const_add _).sub_const _
  have htotal : HasDerivAt
      (fun v => N * s0 + N * R *
        (c * log (U / U0) + log (v / V0) - (c + 1) * log (N / N0)))
      (N * R * (1 / V)) V := by
    exact (hbracket.const_mul (N * R)).const_add (N * s0)
  have hval : N * R * V⁻¹ = N * R / V := by
    ring
  simpa [entropy, one_div, hval] using htotal

/-- Degree-one homogeneity of the ideal-gas entropy on the positive orthant:
`S(lU, lV, lN) = l * S(U,V,N)` for `l > 0`. -/
lemma entropy_homogeneous (c R s0 U0 V0 N0 : ℝ)
    (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0)
    {l : ℝ} (hl : 0 < l) (U V N : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hN : 0 < N) :
    entropy c R s0 U0 V0 N0 (l * U) (l * V) (l * N) =
      l * entropy c R s0 U0 V0 N0 U V N := by
  unfold entropy
  rw [mul_div_assoc, mul_div_assoc, mul_div_assoc]
  rw [Real.log_mul hl.ne' (div_ne_zero hU.ne' hU0.ne')]
  rw [Real.log_mul hl.ne' (div_ne_zero hV.ne' hV0.ne')]
  rw [Real.log_mul hl.ne' (div_ne_zero hN.ne' hN0.ne')]
  ring

/-! ## C. The ideal-gas fundamental relation

The entropy formula is now packaged as a `FundamentalRelation`. The positivity assumptions on
`c`, `R`, and the reference coordinates ensure that the entropy is smooth on the positive
orthant, has positive `∂S/∂U`, and is extensive. -/

/-- The ideal-gas entropy packaged as a `FundamentalRelation`.

The assumptions `0 < c` and `0 < R` give `∂S/∂U = N * R * c / U > 0`, while the positive
reference values keep the logarithmic entropy formula on its intended domain. -/
def idealGasFR (c R s0 U0 V0 N0 : ℝ)
    (hc : 0 < c) (hR : 0 < R) (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0) :
    FundamentalRelation where
  S := entropy c R s0 U0 V0 N0
  smooth := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    obtain ⟨hU, hV, hN⟩ := hx
    unfold entropy
    fun_prop (disch := positivity)
  dS_dU_pos := by
    intro U V N hU _hV hN
    have hderiv := hasDerivAt_entropy_U c R s0 U0 V0 N0 U V N hU hU0
    rw [hderiv.deriv]
    positivity
  homogeneous := by
    intro l hl U V N hU hV hN
    exact entropy_homogeneous c R s0 U0 V0 N0 hU0 hV0 hN0 hl U V N hU hV hN

/-- The energy derivative of the ideal-gas fundamental relation:
`∂S/∂U = N * R * c / U`. -/
lemma dS_dU_idealGasFR (c R s0 U0 V0 N0 : ℝ)
    (hc : 0 < c) (hR : 0 < R) (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0)
    (e : ExtensiveState) :
    (idealGasFR c R s0 U0 V0 N0 hc hR hU0 hV0 hN0).dS_dU e =
      e.N * R * c / e.U := by
  unfold FundamentalRelation.dS_dU
  exact (hasDerivAt_entropy_U c R s0 U0 V0 N0 e.U e.V e.N e.hU hU0).deriv

/-- The volume derivative of the ideal-gas fundamental relation:
`∂S/∂V = N * R / V`. -/
lemma dS_dV_idealGasFR (c R s0 U0 V0 N0 : ℝ)
    (hc : 0 < c) (hR : 0 < R) (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0)
    (e : ExtensiveState) :
    (idealGasFR c R s0 U0 V0 N0 hc hR hU0 hV0 hN0).dS_dV e =
      e.N * R / e.V := by
  unfold FundamentalRelation.dS_dV
  exact (hasDerivAt_entropy_V c R s0 U0 V0 N0 e.U e.V e.N e.hV hV0).deriv

/-! ## D. Equations of state

The derivative formulas give the usual simple-ideal-gas equations of state in the intensive
parameters associated to `idealGasFR`: the mechanical equation `PV = NRT` and the caloric
equation `U = cNRT`. -/

/-- The mechanical equation of state for the simple ideal gas: `PV = NRT`. -/
lemma idealGas_law (c R s0 U0 V0 N0 : ℝ)
    (hc : 0 < c) (hR : 0 < R) (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0)
    (e : ExtensiveState) :
    (idealGasFR c R s0 U0 V0 N0 hc hR hU0 hV0 hN0).pressure e * e.V =
      e.N * R * (idealGasFR c R s0 U0 V0 N0 hc hR hU0 hV0 hN0).temperature e := by
  simp only [FundamentalRelation.pressure, FundamentalRelation.temperature,
    dS_dU_idealGasFR, dS_dV_idealGasFR]
  field_simp [e.hU.ne', e.hV.ne', e.hN.ne', hc.ne', hR.ne']

/-- The caloric equation of state for the simple ideal gas: `U = cNRT`. -/
lemma idealGas_caloric (c R s0 U0 V0 N0 : ℝ)
    (hc : 0 < c) (hR : 0 < R) (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0)
    (e : ExtensiveState) :
    e.U = c * e.N * R *
      (idealGasFR c R s0 U0 V0 N0 hc hR hU0 hV0 hN0).temperature e := by
  simp only [FundamentalRelation.temperature, dS_dU_idealGasFR]
  field_simp [e.hU.ne', e.hV.ne', e.hN.ne', hc.ne', hR.ne']

/-! ## E. Determination from equations of state

The last theorem proves the converse direction. The private lemmas turn the assumed mechanical
and caloric equations of state back into equality of the `V` and `U` entropy partials. The
general uniqueness theorem for `FundamentalRelation`s in `intensive.lean` shows that the residual
against the ideal-gas entropy vanishes everywhere once one reference value is fixed. -/

/-- The caloric equation of state `U = cNRT` determines the energy entropy partial
`∂S/∂U = N * R * c / U`. -/
private lemma dS_dU_eq_of_caloric (Φ : FundamentalRelation) (c R : ℝ)
    (caloric : ∀ e : ExtensiveState, e.U = c * e.N * R * Φ.temperature e)
    (e : ExtensiveState) :
    Φ.dS_dU e = e.N * R * c / e.U := by
  have hDpos : 0 < Φ.dS_dU e := by
    simpa [FundamentalRelation.dS_dU] using
      Φ.dS_dU_pos e.U e.V e.N e.hU e.hV e.hN
  have hDne : Φ.dS_dU e ≠ 0 := hDpos.ne'
  have hcal := caloric e
  simp only [FundamentalRelation.temperature] at hcal
  have hmul : e.U * Φ.dS_dU e = c * e.N * R := by
    calc
      e.U * Φ.dS_dU e =
          (c * e.N * R * (Φ.dS_dU e)⁻¹) * Φ.dS_dU e := by rw [hcal]
      _ = c * e.N * R := by field_simp [hDne]
  calc
    Φ.dS_dU e = (e.U * Φ.dS_dU e) / e.U := by field_simp [e.hU.ne']
    _ = (c * e.N * R) / e.U := by rw [hmul]
    _ = e.N * R * c / e.U := by ring

/-- The mechanical equation of state `PV = NRT` determines the volume entropy partial
`∂S/∂V = N * R / V`. -/
private lemma dS_dV_eq_of_mechanical (Φ : FundamentalRelation) (R : ℝ)
    (mechanical : ∀ e : ExtensiveState, Φ.pressure e * e.V = e.N * R * Φ.temperature e)
    (e : ExtensiveState) :
    Φ.dS_dV e = e.N * R / e.V := by
  have hTne : Φ.temperature e ≠ 0 := (Φ.temperature_pos e).ne'
  have hmech := mechanical e
  simp only [FundamentalRelation.pressure] at hmech
  calc
    Φ.dS_dV e =
        (Φ.temperature e * Φ.dS_dV e * e.V) / (Φ.temperature e * e.V) := by
          field_simp [hTne, e.hV.ne']
    _ = (e.N * R * Φ.temperature e) / (Φ.temperature e * e.V) := by rw [hmech]
    _ = e.N * R / e.V := by
      field_simp [hTne, e.hV.ne']

/-- Determination of the ideal-gas entropy from its equations of state.

If a `FundamentalRelation` satisfies the mechanical equation `PV = NRT`, the caloric equation
`U = cNRT`, and agrees with the ideal-gas entropy at one positive reference state, then it
equals the ideal-gas entropy on every positive extensive state. The proof converts the two
equations of state into equality of entropy partials and applies
`FundamentalRelation.eq_of_dS_dU_dS_dV_eq_of_eq_at`. -/
lemma idealGas_characterization (Φ : FundamentalRelation) (c R s0 U0 V0 N0 : ℝ)
    (hc : 0 < c) (hR : 0 < R) (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0)
    (href : Φ.S U0 V0 N0 = entropy c R s0 U0 V0 N0 U0 V0 N0)
    (mechanical : ∀ e : ExtensiveState, Φ.pressure e * e.V = e.N * R * Φ.temperature e)
    (caloric : ∀ e : ExtensiveState, e.U = c * e.N * R * Φ.temperature e) :
    ∀ e : ExtensiveState, Φ.S e.U e.V e.N =
      entropy c R s0 U0 V0 N0 e.U e.V e.N := by
  -- The positivity assumptions are needed here to construct the ideal-gas
  -- `FundamentalRelation`, whose `dS_dU_pos` field uses `∂S/∂U = N * R * c / U > 0`.
  let Ψ := idealGasFR c R s0 U0 V0 N0 hc hR hU0 hV0 hN0
  have hU_eq : ∀ e : ExtensiveState, Φ.dS_dU e = Ψ.dS_dU e := by
    intro e
    rw [dS_dU_eq_of_caloric Φ c R caloric e]
    exact (dS_dU_idealGasFR c R s0 U0 V0 N0 hc hR hU0 hV0 hN0 e).symm
  have hV_eq : ∀ e : ExtensiveState, Φ.dS_dV e = Ψ.dS_dV e := by
    intro e
    rw [dS_dV_eq_of_mechanical Φ R mechanical e]
    exact (dS_dV_idealGasFR c R s0 U0 V0 N0 hc hR hU0 hV0 hN0 e).symm
  have hrefΨ : Φ.S U0 V0 N0 = Ψ.S U0 V0 N0 := by
    simpa [Ψ, idealGasFR] using href
  exact Φ.eq_of_dS_dU_dS_dV_eq_of_eq_at Ψ hU0 hV0 hN0 hU_eq hV_eq hrefΨ

end Thermodynamics.IdealGas
