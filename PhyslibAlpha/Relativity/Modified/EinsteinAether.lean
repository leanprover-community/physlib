/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Minkowski
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Einstein–Aether Lorentz-violating vector-tensor gravity

Jacobson–Mattingly unit-timelike aether field theory, coupling combinations, kinetic tensor
contraction, spin-2/spin-1/spin-0 squared wave speeds, GW170817 luminal graviton constraint, and
renormalized Newtonian gravitational constant.

## i. Overview

Einstein–Aether theory couples General Relativity to a dynamical unit-timelike vector field `u^a`
("the aether") that spontaneously breaks local Lorentz boost invariance by selecting a preferred
rest frame at every spacetime event (`g_{ab} u^a u^b = -1` in `(-, +, +, +)` signature). The most
general quadratic derivative action is parameterized by four dimensionless coupling constants
`c₁, c₂, c₃, c₄` in `AetherCouplings` via the kinetic tensor
`K^{ab}_{cd} = c₁ g^{ab} g_{cd} + c₂ δ^a_c δ^b_d + c₃ δ^a_d δ^b_c - c₄ u^a u^b g_{cd}`.

Linearizing around flat Minkowski spacetime with rest-frame aether `u = (1, 0, 0, 0)` yields three
propagating radiative modes (spin-2 tensor, spin-1 vector, and spin-0 scalar) with distinct
squared propagation speeds `s₂², s₁², s₀²`, together with a renormalized effective Newtonian
constant `G_N = G_bare / (1 - c₁₄ / 2)`. Multi-messenger observation of the binary neutron-star
merger gravitational wave `GW170817` and its electromagnetic counterpart `GRB 170817A` constrained
the tensor propagation speed to `|s₂ - 1| ≲ 10⁻¹⁵`, requiring `c₁ + c₃ ≈ 0`. Focusing on this
algebraic dispersion-relation layer keeps the theory's observational parameter bounds independent of
a full coordinate-chart Euler–Lagrange solver.

## ii. Key results

- `AetherCouplings`, `AetherCouplings.c13`, `AetherCouplings.c14`, `AetherCouplings.c123` :
  Jacobson–Mattingly coupling structure and physical linear combinations.
- `IsUnitTimelike`, `minkowskiRestAether`, `minkowskiRestAether_unitTimelike`,
  `linUnitTimelike_time_zero` : unit-timelike constraint `g_{ab} u^a u^b = -1` and vanishing
  linearized time perturbation around the Minkowski rest frame.
- `AetherCouplings.kineticTensor`, `AetherCouplings.lagrangian` : four-index aether kinetic
  tensor `K^{ab}_{cd}` and quadratic derivative Lagrangian density.
- `AetherCouplings.spin2SpeedSq`, `AetherCouplings.spin1SpeedSq`, `AetherCouplings.spin0SpeedSq` :
  squared phase velocities of tensor, vector, and scalar aether-gravity modes.
- `AetherCouplings.spin2SpeedSq_eq_one_iff`, `AetherCouplings.spin1SpeedSq_luminal_graviton` :
  GW170817 luminal tensor graviton condition `s₂² = 1 ↔ c₁ + c₃ = 0` and resulting vector mode speed
  `s₁² = c₁ / c₁₄`.
- `AetherCouplings.effectiveNewtonG`, `AetherCouplings.effectiveNewtonG_eq_bare_iff` : renormalized
  Newtonian constant `G_N = G_bare / (1 - c₁₄ / 2)`.

## iii. Table of contents

- A. Aether coupling parameters and unit-timelike vector constraint
- B. Aether kinetic tensor and quadratic Lagrangian density
- C. Radiative mode propagation speeds and GW170817 constraints

## iv. References

* Ted Jacobson and David Mattingly, *Gravity with a Dynamical Preferred Frame*, *Physical Review D*
  (2001), Sec. II (https://arxiv.org/pdf/gr-qc/0007031#page=2). [ref: JacobsonMattingly2001]
* Ted Jacobson and David Mattingly, *Einstein-Aether Waves*, *Physical Review D* (2004), Sec. II-III
  (https://arxiv.org/pdf/gr-qc/0402005#page=2). [ref: JacobsonMattingly2004]
* Christopher Eling, Ted Jacobson, and David Mattingly, *Einstein-Aether Theory*, (2004), Sec. 2
  (https://arxiv.org/pdf/gr-qc/0410001#page=3). [ref: ElingJacobsonMattingly2004]
* Jacob Oost, Shinji Mukohyama, and Anzhong Wang, *Constraints on Einstein-aether Theory after
  GW170817*, *Physical Review D* 97, 124023 (2018), Sec. II-IV
  (https://arxiv.org/pdf/1802.04303#page=1). [ref: OostMukohyamaWang2018]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace EinsteinAether

/-!

## A. Aether coupling parameters and unit-timelike vector constraint

The coupling constants `c₁, c₂, c₃, c₄` and unit-timelike vector constraint `g_{ab} u^a u^b = -1`
fix the preferred-frame kinematics around flat Minkowski spacetime.

-/

/-- The four dimensionless Jacobson–Mattingly coupling constants `(c₁, c₂, c₃, c₄)` of
Einstein–Aether gravity. -/
structure AetherCouplings where
  /-- Coefficient `c₁` of `g^{ab} g_{cd} ∇_a u^c ∇_b u^d`. -/
  c1 : ℝ
  /-- Coefficient `c₂` of `(∇_a u^a)²`. -/
  c2 : ℝ
  /-- Coefficient `c₃` of `∇_a u^b ∇_b u^a`. -/
  c3 : ℝ
  /-- Coefficient `c₄` of `-u^a u^b g_{cd} ∇_a u^c ∇_b u^d`. -/
  c4 : ℝ

/-- Symmetric gradient coupling combination `c₁₃ = c₁ + c₃`. -/
def AetherCouplings.c13 (C : AetherCouplings) : ℝ := C.c1 + C.c3

/-- Acceleration coupling combination `c₁₄ = c₁ + c₄`. -/
def AetherCouplings.c14 (C : AetherCouplings) : ℝ := C.c1 + C.c4

/-- Divergence coupling combination `c₁₂₃ = c₁ + c₂ + c₃`. -/
def AetherCouplings.c123 (C : AetherCouplings) : ℝ := C.c1 + C.c2 + C.c3

/-- Antisymmetric (vorticity/Maxwell) coupling combination `c₁ - c₃`. -/
def AetherCouplings.c1Sub3 (C : AetherCouplings) : ℝ := C.c1 - C.c3

/-- Unit-timelike aether constraint `g_{ab} u^a u^b = -1` in `(-, +, +, +)` signature. -/
def IsUnitTimelike {n : ℕ} (g : Tensor2 n) (u : Fin n → ℝ) : Prop :=
  (∑ a : Fin n, ∑ b : Fin n, g a b * u a * u b) = -1

/-- Canonical Minkowski rest-frame aether four-vector `u^a = (1, 0, 0, 0)`. -/
def minkowskiRestAether : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- The Minkowski rest-frame aether `u = (1, 0, 0, 0)` is unit-timelike with respect to
`minkowskiMetric4`. -/
lemma minkowskiRestAether_unitTimelike : IsUnitTimelike minkowskiMetric4 minkowskiRestAether := by
  simp [IsUnitTimelike, minkowskiRestAether, Fin.sum_univ_four]

/-- First-order variation of the unit-timelike constraint `g_{ab} u^a u^b = -1` around flat
Minkowski spacetime (`g = minkowskiMetric4 + h`, `u = minkowskiRestAether + δu`):
`h_{00} - 2 δu^0 = 0`, so in a gauge with `h_{00} = 0` the time perturbation vanishes
(`δu^0 = 0`). -/
lemma linUnitTimelike_time_zero (h : Tensor2 4) (δu : Fin 4 → ℝ)
    (hlin : (∑ a : Fin 4, ∑ b : Fin 4,
      (h a b * minkowskiRestAether a * minkowskiRestAether b
        + 2 * minkowskiMetric4 a b * minkowskiRestAether a * δu b)) = 0)
    (hh00 : h 0 0 = 0) : δu 0 = 0 := by
  simp only [minkowskiRestAether, Fin.sum_univ_four, minkowskiMetric4_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hh00] at hlin
  norm_num at hlin
  linarith

/-!

## B. Aether kinetic tensor and quadratic Lagrangian density

Contracting `AetherCouplings.kineticTensor` against `∇u` gives the quadratic derivative Lagrangian
whose Lagrange multiplier enforces `IsUnitTimelike M.g u` on shell.

-/

/-- Four-index aether kinetic tensor
`K^{ab}_{cd} = c₁ g^{ab} g_{cd} + c₂ δ^a_c δ^b_d + c₃ δ^a_d δ^b_c - c₄ u^a u^b g_{cd}`. -/
def AetherCouplings.kineticTensor (C : AetherCouplings) {n : ℕ} (M : MetricTensor n)
    (u : Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  C.c1 * M.ginv a b * M.g c d
    + C.c2 * (if a = c then 1 else 0) * (if b = d then 1 else 0)
    + C.c3 * (if a = d then 1 else 0) * (if b = c then 1 else 0)
    - C.c4 * u a * u b * M.g c d

/-- Quadratic aether kinetic invariant `K^{ab}_{cd} (∇_a u^c) (∇_b u^d)` for a covariant derivative
matrix `du a c = ∇_a u^c`. -/
def AetherCouplings.kineticInvariant (C : AetherCouplings) {n : ℕ} (M : MetricTensor n)
    (u : Fin n → ℝ) (du : Tensor2 n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
    C.kineticTensor M u a b c d * du a c * du b d

/-- Full Einstein–Aether Lagrangian density (excluding the `(16 π G_æ)⁻¹` overall factor):
`ℒ_æ = R - K^{ab}_{cd} ∇_a u^c ∇_b u^d + λ (g_{ab} u^a u^b + 1)`. -/
def AetherCouplings.lagrangian (C : AetherCouplings) {n : ℕ} (M : MetricTensor n) (R : ℝ)
    (u : Fin n → ℝ) (du : Tensor2 n) (lam : ℝ) : ℝ :=
  R - C.kineticInvariant M u du
    + lam * ((∑ a : Fin n, ∑ b : Fin n, M.g a b * u a * u b) + 1)

/-- On the constraint surface `IsUnitTimelike M.g u`, the Lagrange multiplier term in
`C.lagrangian` vanishes identically. -/
lemma AetherCouplings.lagrangian_on_shell (C : AetherCouplings) {n : ℕ} (M : MetricTensor n)
    (R : ℝ) (u : Fin n → ℝ) (du : Tensor2 n) (lam : ℝ) (hu : IsUnitTimelike M.g u) :
    C.lagrangian M R u du lam = R - C.kineticInvariant M u du := by
  simp only [AetherCouplings.lagrangian]
  rw [hu]
  ring

/-!

## C. Radiative mode propagation speeds and GW170817 constraints

The squared speeds of spin-2, spin-1, and spin-0 excitations and the renormalized Newtonian
gravitational constant depend rationally on `C : AetherCouplings`.

-/

/-- Squared propagation speed of the spin-2 transverse-traceless tensor graviton mode:
`s₂² = 1 / (1 - c₁₃)`. -/
noncomputable def AetherCouplings.spin2SpeedSq (C : AetherCouplings) : ℝ :=
  1 / (1 - C.c13)

/-- Squared propagation speed of the spin-1 transverse vector aether mode:
`s₁² = (2 c₁ - c₁² + c₃²) / (2 c₁₄ (1 - c₁₃))`. -/
noncomputable def AetherCouplings.spin1SpeedSq (C : AetherCouplings) : ℝ :=
  (2 * C.c1 - C.c1 ^ 2 + C.c3 ^ 2) / (2 * C.c14 * (1 - C.c13))

/-- Squared propagation speed of the spin-0 longitudinal scalar breathing mode:
`s₀² = c₁₂₃ (2 - c₁₄) / (c₁₄ (1 - c₁₃) (2 + c₁₃ + 3 c₂))`. -/
noncomputable def AetherCouplings.spin0SpeedSq (C : AetherCouplings) : ℝ :=
  C.c123 * (2 - C.c14) / (C.c14 * (1 - C.c13) * (2 + C.c13 + 3 * C.c2))

/-- GW170817 / GRB 170817A constraint: the tensor graviton propagates at the speed of light
(`s₂² = 1`) if and only if `c₁₃ = c₁ + c₃ = 0`. -/
lemma AetherCouplings.spin2SpeedSq_eq_one_iff (C : AetherCouplings) (h : 1 - C.c13 ≠ 0) :
    C.spin2SpeedSq = 1 ↔ C.c13 = 0 := by
  simp only [AetherCouplings.spin2SpeedSq, div_eq_iff h]
  constructor <;> intro h1 <;> linarith

/-- When tensor gravitons are luminal (`c₁₃ = c₁ + c₃ = 0`), the spin-1 vector mode squared speed
simplifies to `s₁² = c₁ / c₁₄`. -/
lemma AetherCouplings.spin1SpeedSq_luminal_graviton (C : AetherCouplings) (hc13 : C.c13 = 0)
    (hc14 : C.c14 ≠ 0) : C.spin1SpeedSq = C.c1 / C.c14 := by
  have hc3 : C.c3 = -C.c1 := by
    simp only [AetherCouplings.c13] at hc13
    linarith
  simp only [AetherCouplings.spin1SpeedSq, hc13, hc3]
  field_simp [hc14]
  ring

/-- When tensor gravitons are luminal (`c₁₃ = 0`), the spin-0 scalar mode squared speed simplifies
to `s₀² = c₂ (2 - c₁₄) / (c₁₄ (2 + 3 c₂))`. -/
lemma AetherCouplings.spin0SpeedSq_luminal_graviton (C : AetherCouplings) (hc13 : C.c13 = 0) :
    C.spin0SpeedSq = C.c2 * (2 - C.c14) / (C.c14 * (2 + 3 * C.c2)) := by
  have hc123 : C.c123 = C.c2 := by
    simp only [AetherCouplings.c123, AetherCouplings.c13] at *
    linarith
  simp only [AetherCouplings.spin0SpeedSq, hc13, hc123]
  ring

/-- Renormalized Newtonian gravitational constant measured in weak-field static gravity:
`G_N = G_bare / (1 - c₁₄ / 2)`. -/
noncomputable def AetherCouplings.effectiveNewtonG (C : AetherCouplings) (Gbare : ℝ) : ℝ :=
  Gbare / (1 - C.c14 / 2)

/-- The effective Newtonian gravitational constant equals the bare action constant `G_bare ≠ 0`
if and only if `c₁₄ = c₁ + c₄ = 0`. -/
lemma AetherCouplings.effectiveNewtonG_eq_bare_iff (C : AetherCouplings) (Gbare : ℝ)
    (hG : Gbare ≠ 0) (hd : 1 - C.c14 / 2 ≠ 0) :
    C.effectiveNewtonG Gbare = Gbare ↔ C.c14 = 0 := by
  simp only [AetherCouplings.effectiveNewtonG, div_eq_iff hd]
  constructor
  · intro h
    have h1 : Gbare * (1 - C.c14 / 2) = Gbare * 1 := by linarith
    have h2 := mul_left_cancel₀ hG h1
    linarith
  · intro h
    rw [h]
    ring

end EinsteinAether

end Modified

end GeneralRelativity
