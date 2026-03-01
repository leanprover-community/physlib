/-
Copyright (c) 2025 Fabio Anza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitch Scheffer, Fabio Anza
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- for Real.rpow_def_of_pos

/-!
# Ideal gas: basic entropy and adiabatic relations

In this module we formalize a simple thermodynamic model of a monophase
ideal gas. We:

* Define the entropy
    S(U,V,N) = N s₀ + N R (c \log(U/U₀) + \log(V/V₀) - (c+1)\log(N/N₀)),
* Prove equivalent formulations of the adiabatic relation for two states
  (U_a, V_a) and (U_b, V_b) at fixed N:

  1. c \log(U_a/U_b) + \log(V_a/V_b) = 0,
  2. (U_a/U_b)^c (V_a/V_b) = 1,
  3. U_a^c V_a = U_b^c V_b (the latter follows from (2)).
-/

open Real

noncomputable section

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
theorem adiabatic_relation_log
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
  -- Step 1: cancel `N * s0` and isolate the `N * R * (...)` pieces.
  have h1 :
      N * R *
          (c * log (Ua / U0) +
            log (Va / V0) -
            (c + 1) * log (N / N0)) =
        N * R *
          (c * log (Ub / U0) +
            log (Vb / V0) -
            (c + 1) * log (N / N0)) := by
    -- unfold entropy and use `add_left_cancel` to cancel `N * s0`
    unfold entropy at hS
    -- now `hS` is: N*s0 + N*R*(...) = N*s0 + N*R*(...)`
    -- cancel `N*s0` from both sides
    exact add_left_cancel hS

  -- Step 2: cancel the common factor `N * R`.
  have hNR : N * R ≠ 0 :=
    mul_ne_zero (ne_of_gt hN) (ne_of_gt hR)
  have h2 :
      c * log (Ua / U0) +
        log (Va / V0) -
        (c + 1) * log (N / N0) =
      c * log (Ub / U0) +
        log (Vb / V0) -
        (c + 1) * log (N / N0) :=
    mul_left_cancel₀ hNR h1

  -- Step 3: cancel the common `-(c+1) * log (N/N0)` term.
  have h3 :
      c * log (Ua / U0) + log (Va / V0) =
      c * log (Ub / U0) + log (Vb / V0) := by

    -- rewrite with `sub_eq_add_neg` so we can use `add_right_cancel`

    have h2' :
        c * log (Ua / U0) + log (Va / V0)
          - (c + 1) * log (N / N0) =
        c * log (Ub / U0) + log (Vb / V0)
          - (c + 1) * log (N / N0) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h2
    -- now cancel the same term on the right
    exact add_right_cancel h2'

  -- Step 4: turn this equality into a “difference = 0” form
  -- and rearrange algebraically.
  have h4 :
      c * (log (Ua / U0) - log (Ub / U0)) +
        (log (Va / V0) - log (Vb / V0)) = 0 := by
    -- from `a = b`, we get `a - b = 0`
    have h4' :
        (c * log (Ua / U0) + log (Va / V0)) -
          (c * log (Ub / U0) + log (Vb / V0)) = 0 :=
      sub_eq_zero.mpr h3
    -- expand `a - b` and simplify
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h4'

  -- Step 5: use `log_div` to turn differences of logs into logs of ratios.
  have hUaU0 : 0 < Ua / U0 := div_pos hUa hU0
  have hUbU0 : 0 < Ub / U0 := div_pos hUb hU0
  have hVaV0 : 0 < Va / V0 := div_pos hVa hV0
  have hVbV0 : 0 < Vb / V0 := div_pos hVb hV0

  have hU :
      log (Ua / U0) - log (Ub / U0) =
        log ((Ua / U0) / (Ub / U0)) := by
    -- log_div hx hy : log (x / y) = log x - log y
    -- log_div needs ≠ 0, not just positivity
    have hneqx : Ua / U0 ≠ 0 := ne_of_gt hUaU0
    have hneqy : Ub / U0 ≠ 0 := ne_of_gt hUbU0

    have h := Real.log_div (x := Ua / U0) (y := Ub / U0) hneqx hneqy
    -- we want "difference = log(ratio)", so flip and rewrite
    simpa [sub_eq_add_neg] using h.symm

  have hV :
      log (Va / V0) - log (Vb / V0) =
        log ((Va / V0) / (Vb / V0)) := by
    -- log_div hx hy : log (x / y) = log x - log y
    -- log_div needs ≠ 0, not just positivity
    have hneqxV : Va / V0 ≠ 0 := ne_of_gt hVaV0
    have hneqyV : Vb / V0 ≠ 0 := ne_of_gt hVbV0

    have h := Real.log_div (x := Va / V0) (y := Vb / V0) hneqxV hneqyV

    simpa [sub_eq_add_neg] using h.symm

  have h5 :
      c * log ((Ua / U0) / (Ub / U0)) +
        log ((Va / V0) / (Vb / V0)) = 0 := by
    simpa [hU, hV] using h4

  -- Step 6: simplify the ratios to Ua/Ub and Va/Vb using `field_simp`.
  have h_ratio_U :
      (Ua / U0) / (Ub / U0) = Ua / Ub := by
    -- `field_simp` uses the nonzero denominators in the context
    field_simp [div_eq_mul_inv]

  have h_ratio_V :
      (Va / V0) / (Vb / V0) = Va / Vb := by
    field_simp [div_eq_mul_inv]

  have h6 :
      c * log (Ua / Ub) + log (Va / Vb) = 0 := by
    -- rewrite the log arguments using the two equalities above
    simpa [h_ratio_U, h_ratio_V] using h5

  exact h6

/-- Adiabatic relation in product form:
    If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed,
    then (Ua/Ub)^c * (Va/Vb) = 1.
-/

theorem adiabatic_relation_UaUbVaVb
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
    have hlog := adiabatic_relation_log
      (Ua := Ua) (Ub := Ub) (Va := Va) (Vb := Vb) (N := N)
      hUa hUb hVa hVb hN hU0 hV0 hR hS

    have hUaUb_pos : 0 < Ua / Ub := div_pos hUa hUb
    have hVaVb_pos : 0 < Va / Vb := div_pos hVa hVb

      -- exponentiate both sides and rewrite with `rpow`
    have h := congrArg Real.exp hlog
    have h' :
        Real.exp (c * log (Ua / Ub) + log (Va / Vb)) = 1 := by
      simpa using h

    -- use `exp_add` and `exp_log` / `rpow_def_of_pos` to rewrite
    have hx :
        Real.exp (c * log (Ua / Ub)) = (Ua / Ub) ^ c := by
      -- rpow_def_of_pos: x^y = exp (y * log x) for x>0
      simp [Real.rpow_def_of_pos hUaUb_pos, mul_comm]

    have hy :
        Real.exp (log (Va / Vb)) = Va / Vb := by
      have : Va / Vb ≠ 0 := ne_of_gt hVaVb_pos
      simpa using Real.exp_log hVaVb_pos

    -- now simplify the LHS of h'
    have :
        (Ua / Ub) ^ c * (Va / Vb) = 1 := by
      have := h'
      -- rewrite LHS using `exp_add`, `hx`, `hy`
      simpa [Real.exp_add, hx, hy, mul_comm, mul_left_comm, mul_assoc] using this

    exact this
