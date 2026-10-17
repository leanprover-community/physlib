/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Flow.StoneAPI

/-!

# The unitary group preserves the domain of its generator

The unitary group exp(i t T) preserves the domain of T and commutes with T.

## i. Overview

For a self-adjoint operator `T` with spectral measure `μ`, the unitary group `exp(i t T)` preserves
the domain of `T` and commutes with `T` there.

## ii. Key results

- `expUnitaryGroup_translate_mem` : `exp(i s T)` preserves the domain of `T`.
- `expUnitaryGroup_translate` : `T` commutes with `exp(i s T)` on its domain.

## iii. Table of contents

- A. Invariance of the domain
- B. Commutation with the generator

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped Topology InnerProductSpace Function
open QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

namespace DomainAwareSelfAdjointSpectralTheorem

variable (D : DomainAwareSelfAdjointSpectralTheorem T μS)

include D

/-!

## A. Invariance of the domain

-/

/-- The group law: `D.expUnitaryGroup t (D.expUnitaryGroup s x) = D.expUnitaryGroup (t + s) x`,
via `expUnitaryGroup_add` and the (definitional) fact that `WOT`-multiplication is composition. -/
lemma expUnitaryGroup_translate_comm (x : H) (s t : ℝ) :
    D.expUnitaryGroup t (D.expUnitaryGroup s x) = D.expUnitaryGroup (t + s) x := by
  rw [D.expUnitaryGroup_add t s]
  rfl

/-- `exp(i s T)` preserves the domain of `T`: the orbit of `exp(i s T) x` is the orbit of `x`
shifted by `s`, so it is differentiable at `0`. -/
lemma expUnitaryGroup_translate_mem (x : T.domain) (s : ℝ) :
    D.expUnitaryGroup s (x : H) ∈ T.domain := by
  have hf : HasDerivAt (fun r : ℝ => D.expUnitaryGroup r (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) s :=
    D.expUnitaryGroup_hasDerivAt x s
  have hadd : HasDerivAt (fun t : ℝ => t + s) 1 0 := by
    simpa using (hasDerivAt_id' (𝕜 := ℝ) 0).add_const s
  have hshift : HasDerivAt (fun t : ℝ => D.expUnitaryGroup (t + s) (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) 0 := by
    simpa [Function.comp_def] using hf.scomp_of_eq 0 hadd (by ring)
  have hfun_eq : (fun t : ℝ => D.expUnitaryGroup (t + s) (x : H)) =
      (fun t : ℝ => D.expUnitaryGroup t (D.expUnitaryGroup s (x : H))) := by
    funext t
    exact (D.expUnitaryGroup_translate_comm (x : H) s t).symm
  rw [hfun_eq] at hshift
  exact (D.mem_domain_iff_expUnitaryGroup_hasDerivAt_zero _).2 ⟨_, hshift⟩

/-!

## B. Commutation with the generator

-/

/-- `T` commutes with `D.expUnitaryGroup s` on `T.domain`: for `x ∈ T.domain`,
`D.expUnitaryGroup s x ∈ T.domain` and `T (D.expUnitaryGroup s x) = D.expUnitaryGroup s (T x)`. -/
lemma expUnitaryGroup_translate (x : T.domain) (s : ℝ) :
    T ⟨D.expUnitaryGroup s (x : H), D.expUnitaryGroup_translate_mem x s⟩ =
      D.expUnitaryGroup s (T x) := by
  set y : T.domain := ⟨D.expUnitaryGroup s (x : H), D.expUnitaryGroup_translate_mem x s⟩ with hy_def
  have hcanonical : HasDerivAt (fun t : ℝ => D.expUnitaryGroup t (y : H))
      (Complex.I • T y) 0 :=
    D.expUnitaryGroup_hasDerivAt_zero y
  have hf : HasDerivAt (fun r : ℝ => D.expUnitaryGroup r (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) s :=
    D.expUnitaryGroup_hasDerivAt x s
  have hadd : HasDerivAt (fun t : ℝ => t + s) 1 0 := by
    simpa using (hasDerivAt_id' (𝕜 := ℝ) 0).add_const s
  have hshift : HasDerivAt (fun t : ℝ => D.expUnitaryGroup (t + s) (x : H))
      (D.expUnitaryGroup s (Complex.I • T x)) 0 := by
    simpa [Function.comp_def] using hf.scomp_of_eq 0 hadd (by ring)
  have hfun_eq : (fun t : ℝ => D.expUnitaryGroup (t + s) (x : H)) =
      (fun t : ℝ => D.expUnitaryGroup t (y : H)) := by
    funext t
    rw [hy_def]
    exact (D.expUnitaryGroup_translate_comm (x : H) s t).symm
  rw [hfun_eq] at hshift
  have heq : Complex.I • T y = D.expUnitaryGroup s (Complex.I • T x) :=
    hcanonical.unique hshift
  have hscalar : D.expUnitaryGroup s (Complex.I • T x) = Complex.I • D.expUnitaryGroup s (T x) :=
    map_smul _ _ _
  rw [hscalar] at heq
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact smul_right_injective H hI heq

end DomainAwareSelfAdjointSpectralTheorem

end QuantumMechanics

end ProbabilisticTheory
