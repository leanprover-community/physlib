/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Flow.Stone

/-!
# Public generator API for an unbounded spectral theorem

`Unbounded.Flow.Stone` proves the analytic limit statements for the unitary group attached to a
domain-aware spectral theorem.  This file packages the most useful interface theorem: a vector is
in the generator domain exactly when its orbit is differentiable at time zero.  The result is
stated with an existential derivative so that it is independent of the sign convention chosen for
the group; a companion theorem identifies the derivative as `Complex.I • T x`.

This is only packaging.  The actual work is the square-moment argument and the maximal-integral
operator equality proved in `Unbounded.Flow.Stone` and `UnboundedSpectralIntegral`.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology InnerProductSpace Function

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

namespace DomainAwareSelfAdjointSpectralTheorem

variable (D : DomainAwareSelfAdjointSpectralTheorem T μS)

include D

/-- If the orbit is differentiable at zero, its derivative is forced by the operator. -/
theorem expUnitaryGroup_hasDerivAt_zero_iff (x : H) (y : H) :
    HasDerivAt (fun t : ℝ => D.expUnitaryGroup t x) y 0 ↔
      ∃ hx : x ∈ T.domain, y = Complex.I • T ⟨x, hx⟩ := by
  constructor
  · intro hy
    have hsl : Tendsto
        (fun t : ℝ => t⁻¹ • (D.expUnitaryGroup t x - x))
        (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
      rw [hasDerivAt_iff_tendsto_slope] at hy
      convert hy using 1
      funext t
      simp [slope, D.expUnitaryGroup_zero]
    have hx := (D.mem_domain_iff_expUnitaryGroup_strong_slope x).2 ⟨y, hsl⟩
    let x' : T.domain := ⟨x, hx⟩
    have hcanonical := D.expUnitaryGroup_strong_slope_tendsto x'
    have heq : y = Complex.I • T x' := tendsto_nhds_unique hsl hcanonical
    exact ⟨hx, heq⟩
  · rintro ⟨hx, rfl⟩
    exact D.expUnitaryGroup_hasDerivAt_zero ⟨x, hx⟩

/-- The generator domain is independent of the time at which differentiability is tested.  This
is the orbit-level form of Stone's theorem used by evolution arguments. -/
theorem mem_domain_iff_expUnitaryGroup_hasDerivAt (x : H) (s : ℝ) :
    x ∈ T.domain ↔
      ∃ y : H, HasDerivAt (fun t : ℝ => D.expUnitaryGroup t x) y s := by
  constructor
  · intro hx
    let x' : T.domain := ⟨x, hx⟩
    exact ⟨D.expUnitaryGroup s (Complex.I • T x'),
      D.expUnitaryGroup_hasDerivAt x' s⟩
  · rintro ⟨y, hy⟩
    let U : H →L[ℂ] H :=
      ContinuousLinearMapWOT.toCLM (D.expUnitaryGroup (-s))
    let U' : H →L[ℝ] H := U.restrictScalars ℝ
    have hshift : HasDerivAt
        (fun t : ℝ => D.expUnitaryGroup (t + s) x) y 0 := by
      have hadd : HasDerivAt (fun t : ℝ => t + s) 1 0 := by
        simpa using (hasDerivAt_id' (𝕜 := ℝ) 0).add_const s
      simpa [Function.comp_def] using hy.scomp_of_eq 0 hadd (by ring)
    have hconst : HasDerivAt (fun _ : ℝ => U') 0 0 := hasDerivAt_const 0 U'
    have happly := hconst.clm_apply hshift
    have happly' : HasDerivAt
        (fun t : ℝ => U' (D.expUnitaryGroup (t + s) x)) (U' y) 0 := by
      simpa using happly
    have hzero : HasDerivAt
        (fun t : ℝ => D.expUnitaryGroup t x) (U' y) 0 := by
      apply happly'.congr_of_eventuallyEq
      filter_upwards [] with t
      have hgroup := D.expUnitaryGroup_add (-s) (t + s)
      calc
        D.expUnitaryGroup t x =
            D.expUnitaryGroup (-s + (t + s)) x := by
              exact congrArg (fun r : ℝ => D.expUnitaryGroup r x) (by ring)
        _ = (D.expUnitaryGroup (-s) * D.expUnitaryGroup (t + s)) x := by
              rw [hgroup]
        _ = U' (D.expUnitaryGroup (t + s) x) := by
              rfl
    exact (D.mem_domain_iff_expUnitaryGroup_hasDerivAt_zero x).2
      ⟨U' y, hzero⟩

/-- The derivative at an arbitrary time is uniquely the evolved generator vector. -/
theorem expUnitaryGroup_hasDerivAt_iff (x : H) (y : H) (s : ℝ) :
    HasDerivAt (fun t : ℝ => D.expUnitaryGroup t x) y s ↔
      ∃ hx : x ∈ T.domain,
        y = D.expUnitaryGroup s (Complex.I • T ⟨x, hx⟩) := by
  constructor
  · intro hy
    have hx := (D.mem_domain_iff_expUnitaryGroup_hasDerivAt x s).2 ⟨y, hy⟩
    let x' : T.domain := ⟨x, hx⟩
    have hcanonical := D.expUnitaryGroup_hasDerivAt x' s
    have heq : y = D.expUnitaryGroup s (Complex.I • T x') :=
      hy.unique hcanonical
    exact ⟨hx, heq⟩
  · rintro ⟨hx, rfl⟩
    exact D.expUnitaryGroup_hasDerivAt ⟨x, hx⟩ s

end DomainAwareSelfAdjointSpectralTheorem

end QuantumMechanics
