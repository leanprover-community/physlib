/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import PhyslibAlpha.Relativity.Metrics.MetricTrace
public import PhyslibAlpha.Relativity.Metrics.Minkowski

/-!

# Shared massive-gravity core

Graviton mass and propagator trace coupling shared by massive-gravity models.

## i. Overview

A massive spin-2 theory is characterized by its graviton mass `m ≥ 0` and by the coefficient of
the trace-squared term in the one-graviton exchange residue. The Fierz–Pauli massless limit uses
trace coefficient `1/3`, while the massless General Relativity graviton uses `1/2`; the difference
is the origin of the van Dam–Veltman–Zakharov discontinuity.

## ii. Key results

- `MassiveGravityTheory` : shared massive-gravity data `(m, c)` with `m ≥ 0`.
- `MassiveGravityTheory.propagatorCoupling` : exchange residue with trace coefficient `M.c`.
- `MassiveGravityTheory.generalRelativity`, `MassiveGravityTheory.fierzPauli` : the massless
  General Relativity and Fierz–Pauli specializations.

## iii. Table of contents

- A. Massive-gravity data and propagator coupling

## iv. References

* Kurt Hinterbichler, *Theoretical Aspects of Massive Gravity*, *Reviews of Modern Physics* 84, pp.
  671-710 (2012), Sec. II-III (https://arxiv.org/pdf/1105.3735#page=4). [ref: Hinterbichler2012]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace MassiveGravity

/-!

## A. Massive-gravity data and propagator coupling

The structure stores the graviton mass together with the trace coefficient of the exchange
residue, so the massless General Relativity and Fierz–Pauli limits differ only in one field.

-/

/-- Shared massive-gravity data: graviton mass `m ≥ 0` and the coefficient `c` of the
trace-squared term in the one-graviton exchange residue. -/
structure MassiveGravityTheory where
  /-- Graviton mass `m`. -/
  m : ℝ
  /-- The graviton mass is non-negative. -/
  mass_nonneg : 0 ≤ m
  /-- Coefficient `c` of the trace-squared term in the exchange residue. -/
  c : ℝ

namespace MassiveGravityTheory

/-- Squared graviton mass `m²`. -/
def massSq (M : MassiveGravityTheory) : ℝ := M.m ^ 2

/-- The squared graviton mass is non-negative. -/
lemma massSq_nonneg (M : MassiveGravityTheory) : 0 ≤ M.massSq := sq_nonneg M.m

/-- One-graviton exchange residue contracted between two conserved stress-energy tensors:
`T₁_{ab} T₂^{ab} - c T₁ T₂`, with trace coefficient `M.c`. -/
noncomputable def propagatorCoupling (M : MassiveGravityTheory) (T1 T2 : Tensor2 4) : ℝ :=
  (∑ a : Fin 4, ∑ b : Fin 4,
      minkowskiMetric4 a a * minkowskiMetric4 b b * T1 a b * T2 a b)
    - M.c * metricTrace minkowski T1 * metricTrace minkowski T2

/-- The massless General Relativity graviton: zero mass and trace coefficient `1/2`. -/
noncomputable def generalRelativity : MassiveGravityTheory where
  m := 0
  mass_nonneg := le_rfl
  c := 1 / 2

/-- The Fierz–Pauli massive graviton of mass `m ≥ 0`: trace coefficient `1/3` in the massless
limit. -/
noncomputable def fierzPauli (m : ℝ) (hm : 0 ≤ m) : MassiveGravityTheory where
  m := m
  mass_nonneg := hm
  c := 1 / 3

end MassiveGravityTheory

end MassiveGravity

end Modified

end GeneralRelativity
