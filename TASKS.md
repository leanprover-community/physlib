# Gravity branch task list

## Core tasks

| Task | Status | Notes |
| --- | --- | --- |
| 1. Metric tensor and inverse API | Done | `MetricTensor`, `CoordinateMetric`, inverse contraction lemmas. |
| 2. Christoffel and coordinate derivatives | Done | `CoordinateCurvature.christoffel`, `CoordinateMetric.christoffel`, `coordDeriv`. |
| 3. Riemann curvature | Done | `riemann`, `riemannFromData`, chart operators. |
| 4. Ricci, scalar, and Einstein tensors | Done | Component and chart-level operators plus constant-metric vanishing. |
| 5. Spacetime solutions | Done | Schwarzschild, Schwarzschild–de Sitter, Reissner–Nordström, Kerr, FLRW, Nordström. |
| 6. Scope renames | Done | Committed in `64176f69`; includes `oscillatorKineticHessian`, `inertialDivergence`, and line wrapping. |
| 7. Coordinate curvature operators and `Pipeline` split | Done | `Pipeline` removed; `Christoffel`, `Riemann`, `Ricci`, `Einstein`, and the `CoordinateMetric` aggregator added; committed in `3b20c5de`, `e1b37bae`. |
| 1b. FLRW speed-of-light generalization | Done | `SpeedOfLight` and `GravitationalConstant` are used in `PerfectFluid`, `FriedmannBridge`, and `FLRWTorsion`; full build passes. |

## Follow-ups

| Follow-up | Status | Notes |
| --- | --- | --- |
| Migrate chart proofs to `CoordinateMetric` operators | Partial | Done for Schwarzschild, Schwarzschild–de Sitter, Reissner–Nordström, Kerr, FLRW, and the FLRW perfect-fluid/Friedmann/teleparallel consumers. The static-spherical component file still uses the raw `(g, ginv)` form internally. |
| Bridge algebraic and coordinate curvature | Partial | `Metrics/CurvatureBridge.lean` lowers coordinate Riemann components and proves agreement of `ricci`, `ricciScalar`, and `einstein`. General pair symmetry and Bianchi remain hypotheses; the constant-metric case is unconditional. |
| Add bridge to the API map | Done | `PhyslibAlpha/Relativity/General/API-map.md` entry `[79]`; `RiemannTensor.ext` listed under entry `[6]`. |
| Update this task list | Done | This file. |

## Blocker on the general bridge

`CoordinateMetric` assumes only pointwise symmetry and a two-sided inverse. A general proof of
pair-exchange symmetry and the first Bianchi identity for the lowered coordinate Riemann tensor
also needs differentiability, commuting coordinate derivatives, and metric compatibility. Those
data are not part of `CoordinateMetric`, so the bridge keeps them as explicit hypotheses and only
the constant-metric case is proved unconditionally.
