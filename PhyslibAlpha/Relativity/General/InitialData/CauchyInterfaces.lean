/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.InitialData.InitialDataInterface

/-!

# Interface certificates for M3–M6

## i. Overview

This file records the data and the unresolved propositions that a full
formalisation of the Cauchy problem would have to supply.  The certificates are
specifications, not existence theorems: no certificate is constructed here, and
none of the fields is asserted as true.  A consumer must provide the missing
local-existence, gauge-recovery, constraint-propagation, maximality, or
explicit-solution recovery input.

The chart-level M1 and M2 layers live in `ManifoldInterface` and
`InitialDataInterface`; this module deliberately adds no manifold, Sobolev, PDE,
or causality theory.

## ii. Key results

- `ReducedCauchyProblem`, `ReducedLocalExistenceCertificate` : the M3 reduced
  Cauchy interface and its missing local existence/uniqueness input.
- `GaugeRecoveryProblem`, `GaugeRecoveryCertificate` : the M4 gauge and
  constraint-propagation interface.
- `DevelopmentInterface`, `MaximalDevelopmentCertificate` : the M5 maximal
  development and uniqueness-up-to-isometry interface, universe-polymorphic in
  its data and spacetime types.
- `ExplicitDevelopmentObligations`, `ExplicitDevelopmentCertificate` : the M6
  explicit-solution recovery interface.

## iii. Table of contents

- M3. reduced quasilinear hyperbolic system
- M4. gauge recovery and constraint propagation
- M5. maximal development
- M6. explicit-solution cross-checks

## iv. References

* J. Sbierski, *On the existence of a maximal Cauchy development for the
  Einstein equations — a dezornification*, arXiv:1309.7591, §2, p. 2.
  [ref: sbierski_2013, p. 2]
-/

@[expose] public section

namespace GeneralRelativity

universe u v

/-! ## M3. reduced quasilinear hyperbolic system -/

/-- The data of a reduced Cauchy problem.  `Solution` is the type of reduced
solutions and the predicates are the interface; this structure does not
construct a solution or a reduced equation. -/
structure ReducedCauchyProblem (X : ChartSpacetime) where
  /-- The chart initial data. -/
  data : ChartInitialData X
  /-- The type of reduced solutions. -/
  Solution : Type
  /-- The reduced equation. -/
  IsSolution : Solution → Prop
  /-- The prescribed Cauchy data. -/
  HasCauchyData : Solution → Prop
  /-- The harmonic/wave gauge condition. -/
  IsWaveGauge : Solution → Prop

/-- The missing M3 local-existence and uniqueness input for a reduced problem.
This is a certificate of an analytic theorem, not a proof of one. -/
structure ReducedLocalExistenceCertificate {X : ChartSpacetime}
    (P : ReducedCauchyProblem X) : Prop where
  /-- A local reduced solution with the prescribed data and gauge. -/
  local_existence : ∃ u : P.Solution,
    P.IsSolution u ∧ P.HasCauchyData u ∧ P.IsWaveGauge u
  /-- Local uniqueness of reduced solutions with the same data. -/
  local_uniqueness : ∀ u v : P.Solution,
    P.IsSolution u → P.IsSolution v →
    P.HasCauchyData u → P.HasCauchyData v → u = v

/-- A local-existence certificate supplies a reduced solution. -/
lemma ReducedLocalExistenceCertificate.exists_solution
    {X : ChartSpacetime} {P : ReducedCauchyProblem X}
    (h : ReducedLocalExistenceCertificate P) :
    ∃ u : P.Solution, P.IsSolution u ∧ P.HasCauchyData u ∧ P.IsWaveGauge u :=
  h.local_existence

/-- A local-existence certificate supplies local uniqueness. -/
lemma ReducedLocalExistenceCertificate.unique_solution
    {X : ChartSpacetime} {P : ReducedCauchyProblem X}
    (h : ReducedLocalExistenceCertificate P) {u v : P.Solution}
    (hu : P.IsSolution u) (hv : P.IsSolution v)
    (hu₀ : P.HasCauchyData u) (hv₀ : P.HasCauchyData v) : u = v :=
  h.local_uniqueness u v hu hv hu₀ hv₀

/-! ## M4. gauge recovery and constraint propagation -/

/-- The full-Einstein and constraint predicates attached to reduced solutions.
The fields are specifications; no implication between them is asserted. -/
structure GaugeRecoveryProblem {X : ChartSpacetime}
    (P : ReducedCauchyProblem X) where
  /-- The reduced solution satisfies the full Einstein equations. -/
  IsFullEinsteinSolution : P.Solution → Prop
  /-- The reduced solution preserves the ADM constraints. -/
  ConstraintsPreserved : P.Solution → Prop
  /-- The reduced solution satisfies the recovered gauge. -/
  GaugeRecovered : P.Solution → Prop

/-- The missing M4 gauge-recovery and constraint-propagation input. -/
structure GaugeRecoveryCertificate {X : ChartSpacetime}
    {P : ReducedCauchyProblem X} (G : GaugeRecoveryProblem P) : Prop where
  /-- Every reduced solution satisfies the recovered gauge. -/
  gauge_recovered : ∀ u : P.Solution, P.IsSolution u → G.GaugeRecovered u
  /-- Every reduced solution satisfies the full Einstein equations. -/
  full_einstein : ∀ u : P.Solution, P.IsSolution u → G.IsFullEinsteinSolution u
  /-- Every reduced solution preserves the constraints. -/
  constraints_preserved : ∀ u : P.Solution, P.IsSolution u → G.ConstraintsPreserved u

/-- A gauge-recovery certificate gives gauge recovery. -/
lemma GaugeRecoveryCertificate.gaugeRecovered
    {X : ChartSpacetime} {P : ReducedCauchyProblem X}
    {G : GaugeRecoveryProblem P} (h : GaugeRecoveryCertificate G)
    {u : P.Solution} (hu : P.IsSolution u) : G.GaugeRecovered u :=
  h.gauge_recovered u hu

/-- A gauge-recovery certificate gives the full Einstein equations. -/
lemma GaugeRecoveryCertificate.satisfiesEinstein
    {X : ChartSpacetime} {P : ReducedCauchyProblem X}
    {G : GaugeRecoveryProblem P} (h : GaugeRecoveryCertificate G)
    {u : P.Solution} (hu : P.IsSolution u) : G.IsFullEinsteinSolution u :=
  h.full_einstein u hu

/-- A gauge-recovery certificate gives constraint preservation. -/
lemma GaugeRecoveryCertificate.preservesConstraints
    {X : ChartSpacetime} {P : ReducedCauchyProblem X}
    {G : GaugeRecoveryProblem P} (h : GaugeRecoveryCertificate G)
    {u : P.Solution} (hu : P.IsSolution u) : G.ConstraintsPreserved u :=
  h.constraints_preserved u hu

/-! ## M5. maximal development -/

/-- The development relation and the maximality and isometry predicates.  The
structure records only the interface needed to state the maximal-development
obligation; it constructs no development. -/
structure DevelopmentInterface where
  /-- The type of initial-data sets. -/
  Data : Type u
  /-- The type of candidate spacetimes.  Universe-polymorphic so that the
  chart-level interface can use `ChartSpacetime` directly. -/
  Spacetime : Type v
  /-- `IsDevelopment M data` says that `M` develops `data`. -/
  IsDevelopment : Spacetime → Data → Prop
  /-- Maximality among developments of the same data. -/
  IsMaximal : Spacetime → Prop
  /-- Isometry between developments. -/
  IsIsometric : Spacetime → Spacetime → Prop

/-- The missing M5 maximal-existence and uniqueness-up-to-isometry input. -/
structure MaximalDevelopmentCertificate (D : DevelopmentInterface.{u, v}) : Prop where
  /-- Every data set has a maximal development. -/
  maximal_existence : ∀ data : D.Data,
    ∃ M : D.Spacetime, D.IsDevelopment M data ∧ D.IsMaximal M
  /-- Maximal developments of the same data are isometric. -/
  uniqueness_up_to_isometry : ∀ (M N : D.Spacetime) (data : D.Data),
    D.IsDevelopment M data → D.IsDevelopment N data →
    D.IsMaximal M → D.IsMaximal N → D.IsIsometric M N

/-- A maximal-development certificate supplies maximal existence. -/
lemma MaximalDevelopmentCertificate.exists_maximal
    {D : DevelopmentInterface} (h : MaximalDevelopmentCertificate D)
    (data : D.Data) :
    ∃ M : D.Spacetime, D.IsDevelopment M data ∧ D.IsMaximal M :=
  h.maximal_existence data

/-- A maximal-development certificate supplies uniqueness up to isometry. -/
lemma MaximalDevelopmentCertificate.unique_up_to_isometry
    {D : DevelopmentInterface} (h : MaximalDevelopmentCertificate D)
    {M N : D.Spacetime} {data : D.Data}
    (hM : D.IsDevelopment M data) (hN : D.IsDevelopment N data)
    (hmaxM : D.IsMaximal M) (hmaxN : D.IsMaximal N) : D.IsIsometric M N :=
  h.uniqueness_up_to_isometry M N data hM hN hmaxM hmaxN

/-! ## M6. explicit-solution cross-checks -/

/-- A chart-level development relation: the chart-induced spatial metric is
the ADM metric.  This is the only development condition exported at chart
scope; it does not assert that the chart solves the evolution equations. -/
def ChartSpacetime.IsChartDevelopment (X : ChartSpacetime)
    (D : ChartInitialData X) : Prop :=
  X.spatialMetric = D.data.h.g

/-- Minkowski is a chart-level explicit development of its flat initial data. -/
lemma minkowskiChart_isChartDevelopment :
    minkowskiChart.IsChartDevelopment minkowskiChartInitialData :=
  minkowskiChartInitialData_metric

/-- Scoped M6 cross-check: the Minkowski initial data have a chart development. -/
lemma minkowskiChart_explicit_development :
    ∃ D : ChartInitialData minkowskiChart,
      minkowskiChart.IsChartDevelopment D :=
  ⟨minkowskiChartInitialData, minkowskiChart_isChartDevelopment⟩

/-- The four explicit-solution recovery obligations.  Each field is a
proposition to be instantiated with an actual development theorem; none is
asserted here. -/
structure ExplicitDevelopmentObligations where
  /-- Schwarzschild is recovered as a development of its initial data. -/
  schwarzschild : Prop
  /-- Schwarzschild–de Sitter is recovered as a development of its initial data. -/
  deSitter : Prop
  /-- Kerr is recovered as a development of its initial data. -/
  kerr : Prop
  /-- FLRW is recovered as a development of its initial data. -/
  flrw : Prop

/-- The missing M6 explicit-solution recovery input. -/
structure ExplicitDevelopmentCertificate (O : ExplicitDevelopmentObligations) : Prop where
  /-- The Schwarzschild recovery obligation. -/
  schwarzschild : O.schwarzschild
  /-- The Schwarzschild–de Sitter recovery obligation. -/
  deSitter : O.deSitter
  /-- The Kerr recovery obligation. -/
  kerr : O.kerr
  /-- The FLRW recovery obligation. -/
  flrw : O.flrw

/-- An explicit-development certificate gives the Schwarzschild cross-check. -/
lemma ExplicitDevelopmentCertificate.schwarzschild_recovered
    {O : ExplicitDevelopmentObligations} (h : ExplicitDevelopmentCertificate O) :
    O.schwarzschild :=
  h.schwarzschild

/-- An explicit-development certificate gives the de Sitter cross-check. -/
lemma ExplicitDevelopmentCertificate.deSitter_recovered
    {O : ExplicitDevelopmentObligations} (h : ExplicitDevelopmentCertificate O) :
    O.deSitter :=
  h.deSitter

/-- An explicit-development certificate gives the Kerr cross-check. -/
lemma ExplicitDevelopmentCertificate.kerr_recovered
    {O : ExplicitDevelopmentObligations} (h : ExplicitDevelopmentCertificate O) :
    O.kerr :=
  h.kerr

/-- An explicit-development certificate gives the FLRW cross-check. -/
lemma ExplicitDevelopmentCertificate.flrw_recovered
    {O : ExplicitDevelopmentObligations} (h : ExplicitDevelopmentCertificate O) :
    O.flrw :=
  h.flrw

end GeneralRelativity