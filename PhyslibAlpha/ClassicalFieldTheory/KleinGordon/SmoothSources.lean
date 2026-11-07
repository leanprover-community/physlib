/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Solution
public import PhyslibAlpha.Mathematics.Distribution.OfFun
public import PhyslibAlpha.ClassicalFieldTheory.WaveEquation.Basic

/-!

# Smooth sources as distributions

The retarded solution of a smooth source and the distributional retarded solution agree.

## i. Overview

A smooth function is a distribution by integration against test functions. The weak derivative of
the induced distribution is the induced distribution of the derivative. The Klein–Gordon operator
on the induced distribution is the induced distribution of the smooth operator. So the retarded
solution of the distribution induced by a test field is the distribution induced by the smooth
retarded solution.

## ii. Key results

- `lineDerivCLM_lineDerivCLM_ofFun` : the second weak derivative.
- `distributionOperator_ofFun` : the Klein–Gordon operator on the distribution of a smooth field.
- `ofFun_mem_compactDistributions` : the distribution of a test field has compact support.
- `retardedDistribution_ofFun` : the retarded solution of the distribution of a test field is the
  distribution of the smooth retarded solution.

## iii. Table of contents

- A. Weak derivatives
- B. The Klein–Gordon operator
- C. Compact support
- D. The retarded solution

## iv. References

None.

## A. Weak derivatives

- `lineDerivCLM_lineDerivCLM_ofFun` : the second weak derivative of a smooth function.

## B. The Klein–Gordon operator

- `distributionOperator_ofFun` : the Klein–Gordon operator on the distribution of a smooth field.

## C. Compact support

- `ofFun_mem_compactDistributions` : the distribution of a test field has compact support.

## D. The retarded solution

- `retardedDistribution_ofFun` : the retarded solution of the distribution of a test field is the
  distribution of the smooth retarded solution.
-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff
open MeasureTheory TopologicalSpace Distribution Minkowski WaveEquation minkowskiMatrix

namespace KleinGordon.Spacetime

variable {d : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The weak derivative of the second order of a smooth function. -/
lemma lineDerivCLM_lineDerivCLM_ofFun {u : SpaceTime d → V} (hu : ContDiff ℝ ∞ u)
    (μ : Fin 1 ⊕ Fin d) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Lorentz.Vector.basis μ)
        (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Lorentz.Vector.basis μ)
          (Distribution.ofFun (⊤ : Opens (SpaceTime d)) u volume ⊤)) =
      Distribution.ofFun (⊤ : Opens (SpaceTime d))
        (SpaceTime.deriv μ (SpaceTime.deriv μ u)) volume ⊤ := by
  rw [Distribution.lineDerivCLM_ofFun hu]
  have hu1 : ContDiff ℝ ∞ (fun x => fderiv ℝ u x (Lorentz.Vector.basis μ)) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  rw [Distribution.lineDerivCLM_ofFun hu1]
  rfl

/-- **The Klein–Gordon operator on a smooth field.** The operator on the distribution induced by a
smooth field is the distribution induced by the smooth operator. -/
lemma distributionOperator_ofFun (m : ℝ) (u : smoothFields d V) :
    distributionOperator m (Distribution.ofFun (⊤ : Opens (SpaceTime d)) u.val volume ⊤) =
      Distribution.ofFun (⊤ : Opens (SpaceTime d)) (operator m u).val volume ⊤ := by
  have hU : ContDiff ℝ ∞ u.val := smoothFields_contDiff u
  have hD : ∀ μ, ContDiff ℝ ∞ (SpaceTime.deriv μ u.val) := fun μ =>
    SpaceTime.contDiff_deriv μ u.val (by simpa using hU)
  have hDD : ∀ μ, ContDiff ℝ ∞ (SpaceTime.deriv μ (SpaceTime.deriv μ u.val)) := fun μ =>
    SpaceTime.contDiff_deriv μ _ (by simpa using hD μ)
  have hval : ((operator m u).val : SpaceTime d → V) =
      (∑ μ : Fin 1 ⊕ Fin d, (η μ μ : ℝ) • SpaceTime.deriv μ (SpaceTime.deriv μ u.val)) +
        (m ^ 2) • u.val := by
    simp [operator, smoothWaveOperator_coe]
  have hc1 : Continuous (∑ μ : Fin 1 ⊕ Fin d, (η μ μ : ℝ) •
      SpaceTime.deriv μ (SpaceTime.deriv μ u.val)) := by
    have : (∑ μ : Fin 1 ⊕ Fin d, (η μ μ : ℝ) • SpaceTime.deriv μ (SpaceTime.deriv μ u.val)) =
        fun x => ∑ μ : Fin 1 ⊕ Fin d, (η μ μ : ℝ) •
          SpaceTime.deriv μ (SpaceTime.deriv μ u.val) x := funext fun x => by
      simp [Finset.sum_apply]
    rw [this]
    exact continuous_finsetSum _ fun μ _ => (hDD μ).continuous.const_smul (η μ μ : ℝ)
  have hc2 : Continuous ((m ^ 2) • u.val) := hU.continuous.const_smul (m ^ 2)
  have hc3 : ∀ μ : Fin 1 ⊕ Fin d, Continuous ((η μ μ : ℝ) •
      SpaceTime.deriv μ (SpaceTime.deriv μ u.val)) := fun μ =>
    (hDD μ).continuous.const_smul (η μ μ : ℝ)
  rw [hval, Distribution.ofFun_continuous_add hc1 hc2, Distribution.ofFun_finset_sum _ hc3]
  simp only [distributionOperator, distributionWaveOperator, add_apply,
    sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, lineDerivCLM_lineDerivCLM_ofFun hU]
  congr 1
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Distribution.ofFun_smul]
  · rw [Distribution.ofFun_smul]

/-- The distribution induced by a test field has compact support. -/
lemma ofFun_mem_compactDistributions (f : TestField d V) :
    Distribution.ofFun (⊤ : Opens (SpaceTime d)) (f.val : SpaceTime d → V) volume ⊤ ∈
      compactDistributions (SpaceTime d) V :=
  ⟨tsupport (f.val : SpaceTime d → V), f.property, Distribution.isVanishingOn_ofFun fun _ hx =>
    image_eq_zero_of_notMem_tsupport hx⟩

omit [NormedSpace ℝ V] in
/-- **Smooth sources.** The retarded solution of the distribution induced by a test field is the
distribution induced by the smooth retarded solution. This is the one Green operator realised on
test fields, on compactly supported distributions and on smooth fields. -/
lemma retardedDistribution_ofFun {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (m : ℝ) (f : TestField d F) :
    Solution.retardedDistribution m ⟨Distribution.ofFun (⊤ : Opens (SpaceTime d))
        (f.val : SpaceTime d → F) volume ⊤, ofFun_mem_compactDistributions f⟩ =
      Distribution.ofFun (⊤ : Opens (SpaceTime d))
        ((Solution.retarded F m f).val : SpaceTime d → F) volume ⊤ := by
  refine (Solution.retardedDistribution_unique (m := m) _ _ f.property ?_ ?_).symm
  · exact Distribution.isVanishingOn_ofFun fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
      hx (Solution.retarded_support (m := m) f h)
  · rw [distributionOperator_ofFun]
    have := Solution.retarded_solves (m := m) f
    simp only [this]

end KleinGordon.Spacetime
