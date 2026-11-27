/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.Einstein
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor

/-!

# Bridge from coordinate to algebraic curvature

Lowering the coordinate Riemann tensor and contracting it as an algebraic `RiemannTensor`.

## i. Overview

The coordinate operator `CoordinateMetric.riemann` computes the mixed components
`R^ρ_{σμν}`. Lowering the first index with the metric gives the covariant components
`R_{ρσμν} = ∑ λ, g_{ρλ} R^λ_{σμν}`, which satisfy last-pair antisymmetry. When the covariant
components also satisfy pair-exchange symmetry and the first Bianchi identity, they form an
algebraic `RiemannTensor`, and the algebraic contractions `ricci`, `ricciScalar`, and `einstein`
of that tensor agree with the chart-level `CoordinateMetric` operators. Pair symmetry and Bianchi
are hypotheses here: `CoordinateMetric` carries pointwise symmetry and an inverse but not the
differentiability and metric-compatibility data needed to derive them. For a constant metric all
curvature vanishes, so that case is unconditional.

## ii. Key results

- `CoordinateMetric.loweredRiemann` : covariant coordinate Riemann components.
- `CoordinateMetric.loweredRiemann_skew_last` : antisymmetry in the last index pair.
- `CoordinateMetric.toRiemannTensor` : algebraic `RiemannTensor` from the covariant components,
  given pair symmetry and the first Bianchi identity.
- `CoordinateMetric.ricci_toRiemannTensor`, `CoordinateMetric.ricciScalar_toRiemannTensor`,
  `CoordinateMetric.einstein_toRiemannTensor` : agreement of the algebraic contractions with the
  coordinate Ricci tensor, scalar curvature, and Einstein tensor.
- `CoordinateMetric.toRiemannTensorConst` : unconditional bridge for a constant metric, where all
  curvature vanishes and the algebraic tensor is `RiemannTensor.flat`.

## iii. Table of contents

- A. Covariant coordinate Riemann components
- B. Algebraic contractions of the coordinate curvature

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 13.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3 (Sec. 3.6)
  (https://arxiv.org/pdf/gr-qc/9712019#page=77). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Covariant coordinate Riemann components

Lowering the first index of `CoordinateMetric.riemann` with the chart metric produces covariant
components, which are antisymmetric in the last pair by the definition of the mixed curvature.

-/

/-- Covariant coordinate Riemann components
`R_{ρσμν} = ∑ λ, g_{ρλ} R^λ_{σμν}`. -/
noncomputable def CoordinateMetric.loweredRiemann {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  ∑ a, C.g x ρ a * C.riemann x a σ μ ν

/-- The mixed coordinate Riemann tensor is antisymmetric in the last pair. -/
lemma CoordinateMetric.riemann_skew_last {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (a σ μ ν : Fin n) :
    C.riemann x a σ μ ν = -C.riemann x a σ ν μ := by
  simp only [CoordinateMetric.riemann_apply, CoordinateCurvature.riemann]
  simp_rw [Finset.sum_sub_distrib]
  ring

/-- The covariant coordinate Riemann components are antisymmetric in the last pair. -/
lemma CoordinateMetric.loweredRiemann_skew_last {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    C.loweredRiemann x ρ σ μ ν = -C.loweredRiemann x ρ σ ν μ := by
  simp only [CoordinateMetric.loweredRiemann]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [CoordinateMetric.riemann_skew_last]
  ring

/-- The algebraic Riemann tensor whose components are the covariant coordinate components, given
pair-exchange symmetry and the first Bianchi identity. -/
noncomputable def CoordinateMetric.toRiemannTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ)
    (hpair : ∀ i j k l, C.loweredRiemann x i j k l = C.loweredRiemann x k l i j)
    (hbianchi : ∀ i j k l, C.loweredRiemann x i j k l + C.loweredRiemann x i k l j +
      C.loweredRiemann x i l j k = 0) : RiemannTensor n where
  comp := C.loweredRiemann x
  skew_last := fun i j k l => C.loweredRiemann_skew_last x i j k l
  pair_symm := hpair
  bianchi := hbianchi

/-!

## B. Algebraic contractions of the coordinate curvature

Contracting the covariant components against the inverse metric reproduces the coordinate Ricci
tensor, scalar curvature, and Einstein tensor.

-/

/-- Contracting a lowered mixed tensor against the inverse metric recovers its first-index trace:
`∑ k l, g^{kl} (∑ λ, g_{kλ} R^λ_{i l j}) = ∑ ρ, R^ρ_{iρj}`. -/
lemma ricci_lowered {n : ℕ} (M : MetricTensor n)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ k : Fin n, ∑ l : Fin n,
        M.ginv k l * (∑ a : Fin n, M.g k a * R a i l j)) =
      ∑ ρ : Fin n, R ρ i ρ j := by
  have hstep :
      (∑ k : Fin n, ∑ l : Fin n,
          M.ginv k l * (∑ a : Fin n, M.g k a * R a i l j)) =
        ∑ l : Fin n, ∑ a : Fin n,
          (∑ k : Fin n, M.ginv k l * M.g k a) * R a i l j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hstep]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · have h1 : (∑ k : Fin n, M.ginv k l * M.g k l) = 1 := by
      calc (∑ k : Fin n, M.ginv k l * M.g k l)
          = ∑ k : Fin n, M.ginv l k * M.g k l := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [M.ginv_symm.apply k l]
        _ = 1 := by simp [M.sum_ginv_mul_g_left l l]
    simp [h1]
  · intro a _ ha
    have h0 : (∑ k : Fin n, M.ginv k l * M.g k a) = 0 := by
      calc (∑ k : Fin n, M.ginv k l * M.g k a)
          = ∑ k : Fin n, M.ginv l k * M.g k a := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [M.ginv_symm.apply k l]
        _ = 0 := by
            rw [M.sum_ginv_mul_g_left l a]
            simp [Ne.symm ha]
    simp [h0]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

/-- The algebraic Ricci tensor of `C.toRiemannTensor` equals the coordinate Ricci tensor. -/
lemma CoordinateMetric.ricci_toRiemannTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (hx : x ∈ C.domain)
    (hpair : ∀ i j k l, C.loweredRiemann x i j k l = C.loweredRiemann x k l i j)
    (hbianchi : ∀ i j k l, C.loweredRiemann x i j k l + C.loweredRiemann x i k l j +
      C.loweredRiemann x i l j k = 0) (i j : Fin n) :
    ricci (C.metricTensor x hx) (C.toRiemannTensor x hpair hbianchi) i j =
      C.ricciTensor x i j := by
  simp only [ricci, CoordinateMetric.toRiemannTensor, CoordinateMetric.loweredRiemann,
    CoordinateMetric.ricciTensor_apply, CoordinateCurvature.ricciTensor]
  simpa only [CoordinateMetric.metricTensor_g, CoordinateMetric.metricTensor_ginv,
    CoordinateMetric.riemann_apply]
    using ricci_lowered (C.metricTensor x hx) (fun ρ σ μ ν => C.riemann x ρ σ μ ν) i j

/-- The algebraic scalar curvature of `C.toRiemannTensor` equals the coordinate scalar
curvature. -/
lemma CoordinateMetric.ricciScalar_toRiemannTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (hx : x ∈ C.domain)
    (hpair : ∀ i j k l, C.loweredRiemann x i j k l = C.loweredRiemann x k l i j)
    (hbianchi : ∀ i j k l, C.loweredRiemann x i j k l + C.loweredRiemann x i k l j +
      C.loweredRiemann x i l j k = 0) :
    GeneralRelativity.ricciScalar (C.metricTensor x hx)
        (C.toRiemannTensor x hpair hbianchi) =
      C.ricciScalar x := by
  simp only [GeneralRelativity.ricciScalar, CoordinateMetric.ricciScalar_apply,
    CoordinateMetric.ricciTensor_apply, CoordinateCurvature.ricciScalar,
    CoordinateMetric.metricTensor_ginv,
    CoordinateMetric.ricci_toRiemannTensor C x hx hpair hbianchi]

/-- The algebraic Einstein tensor of `C.toRiemannTensor` equals the coordinate Einstein
tensor. -/
lemma CoordinateMetric.einstein_toRiemannTensor {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (hx : x ∈ C.domain)
    (hpair : ∀ i j k l, C.loweredRiemann x i j k l = C.loweredRiemann x k l i j)
    (hbianchi : ∀ i j k l, C.loweredRiemann x i j k l + C.loweredRiemann x i k l j +
      C.loweredRiemann x i l j k = 0) (i j : Fin n) :
    einstein (C.metricTensor x hx) (C.toRiemannTensor x hpair hbianchi) i j =
      C.einsteinTensor x i j := by
  simp only [einstein, CoordinateMetric.einsteinTensor_apply, CoordinateCurvature.einsteinTensor,
    CoordinateMetric.ricciTensor_apply, CoordinateMetric.ricciScalar_apply,
    CoordinateMetric.metricTensor_g,
    CoordinateMetric.ricci_toRiemannTensor C x hx hpair hbianchi,
    CoordinateMetric.ricciScalar_toRiemannTensor C x hx hpair hbianchi]

/-- The covariant Riemann components of a constant metric vanish. -/
lemma CoordinateMetric.loweredRiemann_const {n : ℕ} (C : CoordinateMetric n) (G : Tensor2 n)
    (hg : ∀ x, C.g x = G) (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    C.loweredRiemann x ρ σ μ ν = 0 := by
  simp only [CoordinateMetric.loweredRiemann, CoordinateMetric.riemann_apply,
    CoordinateCurvature.riemann_const C.g C.ginv G hg, mul_zero, Finset.sum_const_zero]

/-- For a constant coordinate metric, the covariant components satisfy the algebraic symmetries
unconditionally, so the bridge produces an algebraic `RiemannTensor`. -/
noncomputable def CoordinateMetric.toRiemannTensorConst {n : ℕ} (C : CoordinateMetric n)
    (G : Tensor2 n) (hg : ∀ x, C.g x = G) (x : Fin n → ℝ) : RiemannTensor n :=
  C.toRiemannTensor x
    (fun i j k l => by simp [CoordinateMetric.loweredRiemann_const C G hg])
    (fun i j k l => by simp [CoordinateMetric.loweredRiemann_const C G hg])

/-- The algebraic Riemann tensor of a constant coordinate metric is the flat tensor. -/
lemma CoordinateMetric.toRiemannTensorConst_eq_flat {n : ℕ} (C : CoordinateMetric n)
    (G : Tensor2 n) (hg : ∀ x, C.g x = G) (x : Fin n → ℝ) :
    C.toRiemannTensorConst G hg x = RiemannTensor.flat n := by
  ext i j k l
  simp [CoordinateMetric.toRiemannTensorConst, CoordinateMetric.toRiemannTensor,
    CoordinateMetric.loweredRiemann_const C G hg]

/-- The algebraic Ricci tensor of a constant coordinate metric vanishes. -/
lemma CoordinateMetric.ricci_toRiemannTensorConst {n : ℕ} (C : CoordinateMetric n)
    (G : Tensor2 n) (hg : ∀ x, C.g x = G) (x : Fin n → ℝ) (hx : x ∈ C.domain) :
    ricci (C.metricTensor x hx) (C.toRiemannTensorConst G hg x) = 0 := by
  rw [CoordinateMetric.toRiemannTensorConst_eq_flat, ricci_flat]

/-- The algebraic scalar curvature of a constant coordinate metric vanishes. -/
lemma CoordinateMetric.ricciScalar_toRiemannTensorConst {n : ℕ} (C : CoordinateMetric n)
    (G : Tensor2 n) (hg : ∀ x, C.g x = G) (x : Fin n → ℝ) (hx : x ∈ C.domain) :
    GeneralRelativity.ricciScalar (C.metricTensor x hx) (C.toRiemannTensorConst G hg x) = 0 := by
  rw [CoordinateMetric.toRiemannTensorConst_eq_flat, ricciScalar_flat]

/-- The algebraic Einstein tensor of a constant coordinate metric vanishes. -/
lemma CoordinateMetric.einstein_toRiemannTensorConst {n : ℕ} (C : CoordinateMetric n)
    (G : Tensor2 n) (hg : ∀ x, C.g x = G) (x : Fin n → ℝ) (hx : x ∈ C.domain) :
    einstein (C.metricTensor x hx) (C.toRiemannTensorConst G hg x) = 0 := by
  rw [CoordinateMetric.toRiemannTensorConst_eq_flat, einstein_flat]

end GeneralRelativity
