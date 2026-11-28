/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Tensors.Tensor2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Lovelock algebraic curvature tensors

Algebraic `(2,2)` curvature tensors and the Gauss–Bonnet and Lanczos invariants.

## i. Overview

At quadratic order in curvature, the Gauss–Bonnet density `𝒢 = R² - 4 R^a_b R^b_a + R^{cd}_{ab}
R^{ab}_{cd}` yields the Lanczos variation tensor `H^i_j`. The five-index contraction identity and
the constant-curvature model live in `Lovelock/Contract5.lean` and
`Lovelock/ConstantCurvature.lean`.

## ii. Key results

- `AlgebraicCurvature` : algebraic `(2,2)` curvature structure.
- `AlgebraicCurvature.ricciMixed`, `AlgebraicCurvature.ricciScalar`, `AlgebraicCurvature.ricciSq`,
  `AlgebraicCurvature.riemannSq` : mixed Ricci, Ricci scalar, and squared curvature invariants.
- `AlgebraicCurvature.gaussBonnetScalar`, `AlgebraicCurvature.lanczosTensor` : quadratic
  Gauss–Bonnet invariant and Lanczos tensor `H^i_j`.

## iii. Table of contents

- A. Algebraic curvature tensors and Gauss–Bonnet invariants

## iv. References

* Cornelius Lanczos, *A Remarkable Property of the Riemann-Christoffel Tensor in Four Dimensions*,
  *Annals of Mathematics* 39, pp. 842-850 (1938). [ref: Lanczos1938]
* David Lovelock, *The Einstein Tensor and Its Generalizations*, *Journal of Mathematical Physics*
  12, pp. 498-501 (1971), Sec. 2-3. [ref: Lovelock1971]
* David Lovelock, *The Four-Dimensionality of Space and the Einstein Tensor*, *Journal of
  Mathematical Physics* 13, pp. 874-876 (1972). [ref: Lovelock1972]
* T. Padmanabhan and D. Kothawala, *Lanczos-Lovelock Models of Gravity*, *Physics Reports* (2013),
  Sec. 2-3 (https://arxiv.org/pdf/1302.2151#page=4). [ref: PadmanabhanKothawala2013]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Lovelock


/-!

## A. Algebraic curvature tensors and Gauss–Bonnet invariants

The quadratic Gauss–Bonnet scalar density `𝒢` and its variation tensor `H^i_j` (Lanczos tensor)
depend solely on the algebraic pair antisymmetries of mixed curvature components `R^{ab}_{cd}`.

-/

/-- Abstract algebraic `(2,2)` mixed Riemann curvature tensor `R^{ab}_{cd}` in `n` dimensions,
carrying antisymmetry in `(a, b)` and `(c, d)`. Kept separate from `RiemannTensor` because the
Bach–Lanczos dimension-dependent vanishing theorem depends only on algebraic pair antisymmetry and
the mixed index structure `R^{ab}_{cd}` rather than metric lowering or the Bianchi identity. -/
structure AlgebraicCurvature (n : ℕ) where
  /-- Mixed `(2,2)` curvature components `R^{ab}_{cd}`. -/
  rUp : Fin n → Fin n → Fin n → Fin n → ℝ
  /-- Antisymmetry in the first (upper) pair of indices: `R^{ab}_{cd} = -R^{ba}_{cd}`. -/
  antisymm12 : ∀ a b c d, rUp a b c d = -rUp b a c d
  /-- Antisymmetry in the second (lower) pair of indices: `R^{ab}_{cd} = -R^{ab}_{dc}`. -/
  antisymm34 : ∀ a b c d, rUp a b c d = -rUp a b d c

/-- Mixed `(1,1)` Ricci tensor `R^i_j = ∑_b R^{ib}_{jb}`. -/
def AlgebraicCurvature.ricciMixed {n : ℕ} (C : AlgebraicCurvature n) (i j : Fin n) : ℝ :=
  ∑ b : Fin n, C.rUp i b j b

/-- Scalar curvature `R = ∑_{a,b} R^{ab}_{ab}`. -/
def AlgebraicCurvature.ricciScalar {n : ℕ} (C : AlgebraicCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, C.rUp a b a b

/-- Trace of the mixed Ricci tensor equals the scalar curvature: `∑_i R^i_i = R`. -/
lemma AlgebraicCurvature.trace_ricciMixed {n : ℕ} (C : AlgebraicCurvature n) :
    (∑ i : Fin n, C.ricciMixed i i) = C.ricciScalar := by
  rfl

/-- Quadratic Ricci invariant `R^a_b R^b_a`. -/
def AlgebraicCurvature.ricciSq {n : ℕ} (C : AlgebraicCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, C.ricciMixed a b * C.ricciMixed b a

/-- Quadratic Riemann (Kretschmann) invariant `R^{cd}_{ab} R^{ab}_{cd}`. -/
def AlgebraicCurvature.riemannSq {n : ℕ} (C : AlgebraicCurvature n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d a b * C.rUp a b c d

/-- Quadratic Gauss–Bonnet scalar density `𝒢 = R² - 4 R^a_b R^b_a + R^{cd}_{ab} R^{ab}_{cd}`. -/
def AlgebraicCurvature.gaussBonnetScalar {n : ℕ} (C : AlgebraicCurvature n) : ℝ :=
  C.ricciScalar ^ 2 - 4 * C.ricciSq + C.riemannSq

/-- Mixed `(1,1)` Lanczos–Bach–Gauss–Bonnet variation tensor
`H^i_j = -½ δ^i_j 𝒢 + 2 R R^i_j - 4 R^i_c R^c_j - 4 R^{ic}_{jb} R^b_c + 2 R^{cd}_{jb} R^{ib}_{cd}`.
-/
noncomputable def AlgebraicCurvature.lanczosTensor {n : ℕ} (C : AlgebraicCurvature n)
    (i j : Fin n) : ℝ :=
  -(1 / 2) * (if i = j then C.gaussBonnetScalar else 0)
    + 2 * C.ricciScalar * C.ricciMixed i j
    - 4 * (∑ c : Fin n, C.ricciMixed i c * C.ricciMixed c j)
    - 4 * (∑ b : Fin n, ∑ c : Fin n, C.rUp i c j b * C.ricciMixed b c)
    + 2 * (∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, C.rUp c d j b * C.rUp i b c d)

end Lovelock

end Modified

end GeneralRelativity
