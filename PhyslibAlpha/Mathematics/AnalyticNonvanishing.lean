/-
Copyright (c) 2026 Rithwik Ranganathan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rithwik Ranganathan
-/
module

public import Physlib.Mathematics.ForMathlib.Analytic

/-!
# Analytic non-vanishing sets in phase space

An import interface for analytic tools used by Hamiltonian integrability developments.

## i. Overview

This module re-exports the analytic tools in `Physlib.Mathematics.ForMathlib.Analytic`, preserving
the import path used by the integrability developments. The general mathematical proofs live in
`ForMathlib` so that they can be upstreamed independently of the physics library.

## ii. Key results

- `AnalyticOnNhd.dense_setOf_ne_zero`: an analytic function non-zero at one point is non-zero
  on a dense set.
- `analyticAt_euclideanSpace_apply`: coordinate functionals on Euclidean space are analytic.

## iii. Table of contents

- A. Import compatibility

## iv. References

See `Physlib.Mathematics.ForMathlib.Analytic` for the proofs and their mathematical background.

## A. Import compatibility

The public import above makes both lemmas available through the existing Alpha import path.
-/
