/-
Copyright (c) 2026
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PhysLean.Mathematics.Geometry.Metric.QuadraticForm.NegDim

/-!
# Quadratic form inertia indices (compatibility layer)

This file is the single import point for the inertia index/signature API used by the
pseudo-Riemannian metric development (`QuadraticForm.posIndex`, `QuadraticForm.posDim`,
`QuadraticForm.negDim`, `QuadraticForm.zeroDim`, `QuadraticForm.signature`, ...).

Currently these definitions live in `PhysLean.Mathematics.Geometry.Metric.QuadraticForm.NegDim`.
If Mathlib later provides overlapping canonical inertia invariants, this file is intended to be
the unique switch-point.
-/

