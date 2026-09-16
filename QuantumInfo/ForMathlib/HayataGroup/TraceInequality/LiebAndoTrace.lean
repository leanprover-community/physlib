/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.OperatorGeometricMean
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.HilbertSchmidtOperatorSpace
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

namespace LiebAndoTrace

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open OperatorGeometricMean
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

set_option synthInstance.maxHeartbeats 80000 in
noncomputable local instance : NonnegSpectrumClass ℝ ((L ℋ)ᵐᵒᵖ) := inferInstance

set_option synthInstance.maxHeartbeats 80000 in
noncomputable local instance :
    IsometricContinuousFunctionalCalculus ℂ ((L ℋ)ᵐᵒᵖ) IsStarNormal := inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance instCFCRealSelfAdjointMop :
    ContinuousFunctionalCalculus ℝ ((L ℋ)ᵐᵒᵖ) IsSelfAdjoint := inferInstance

/-- The real part of the finite-dimensional trace on bounded operators. -/
noncomputable def traceRe (T : L ℋ) : ℝ :=
  Complex.re (LinearMap.trace ℂ ℋ T.toLinearMap)

/-- Trace functional appearing in Lieb's concavity theorem. -/
noncomputable def liebTraceMap (s : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K)

/-- Trace functional appearing in Lieb's extension theorem. -/
noncomputable def liebExtensionTraceMap (q p : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ p * K)

/-- Trace functional appearing in Corollary 1.3. -/
noncomputable def liebCorollaryTraceMap (q r : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ (1 - r) * K)

/-- Trace functional appearing in Ando's convexity theorem. -/
noncomputable def andoTraceMap (q r : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ (-r) * K)

omit [Nontrivial ℋ] [CompleteSpace ℋ] in
private lemma rightMulHS_real_smul_one (r : ℝ) :
    rightMulHS (ℋ := ℋ) (r • (1 : L ℋ)) = r • (1 : L (HSOp ℋ)) := by
  ext T
  change ofOp (toOp T * ((algebraMap ℝ (L ℋ)) r)) =
    r • ofOp (toOp T * (1 : L ℋ))
  calc
    ofOp (toOp T * ((algebraMap ℝ (L ℋ)) r))
        = ofOp (((algebraMap ℝ (L ℋ)) r * toOp T) * (1 : L ℋ)) := by
            have hcomm := Algebra.commutes (R := ℝ) (A := L ℋ) r (toOp T)
            exact congrArg (fun X => X * (1 : L ℋ)) hcomm.symm
    _ = r • ofOp (toOp T) := by
          delta HSOp
          rfl
    _ = r • ofOp (toOp T * (1 : L ℋ)) := by simp

omit [Nontrivial ℋ] in
private lemma rightMulHS_nonneg {A : L ℋ} (hA0 : 0 ≤ A) :
    0 ≤ rightMulHS (ℋ := ℋ) A := by
  let sqrtA : L ℋ := A ^ ((1 : ℝ) / 2)
  have hsqrt_sq_pow : sqrtA ^ (2 : ℕ) = A := by
    calc
      sqrtA ^ (2 : ℕ) = sqrtA ^ (2 : ℝ) := by
            simpa using (CFC.rpow_natCast sqrtA 2).symm
      _ = A ^ (((1 : ℝ) / 2) * 2) := by
            simpa [sqrtA] using
              (CFC.rpow_rpow_of_exponent_nonneg A ((1 : ℝ) / 2) 2
                (by positivity) (by positivity) (ha := hA0))
      _ = A ^ (1 : ℝ) := by ring_nf
      _ = A := by simpa using CFC.rpow_one A
  have hsqrt_sq : sqrtA * sqrtA = A := by
    simpa [pow_two] using hsqrt_sq_pow
  have hsqrt_sa : IsSelfAdjoint sqrtA := IsSelfAdjoint.of_nonneg (by
    simp [sqrtA])
  let S : L (HSOp ℋ) := rightMulHS (ℋ := ℋ) sqrtA
  have hSstar : star S = S := by
    change star (rightMulHS (ℋ := ℋ) sqrtA) = rightMulHS (ℋ := ℋ) sqrtA
    simp [hsqrt_sa.star_eq]
  have hSq : rightMulHS (ℋ := ℋ) A = star S * S := by
    calc
      rightMulHS (ℋ := ℋ) A = rightMulHS (ℋ := ℋ) (sqrtA * sqrtA) := by simp [hsqrt_sq]
      _ = S * S := by simp [S]
      _ = star S * S := by simp [hSstar]
  simp [hSq]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
private lemma rightMulHS_le_rightMulHS {A B : L ℋ} (hAB : A ≤ B) :
    rightMulHS (ℋ := ℋ) A ≤ rightMulHS (ℋ := ℋ) B := by
  have hnonneg : 0 ≤ rightMulHS (ℋ := ℋ) (B - A) :=
    rightMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hAB)
  have hsub :
      rightMulHS (ℋ := ℋ) B - rightMulHS (ℋ := ℋ) A =
        rightMulHS (ℋ := ℋ) (B - A) := by
    ext T
    have h1 := (mul_add (toOp T) B (-A)).symm
    simp_all only [sub_eq_add_neg, mul_neg, add_apply, rightMulHS_apply, neg_apply]
    exact h1
  exact sub_nonneg.mp (by simpa [hsub] using hnonneg)

private lemma rightMulHS_pdSet {A : L ℋ} (hA : A ∈ pdSet (ℋ := ℋ)) :
    rightMulHS (ℋ := ℋ) A ∈ pdSet (ℋ := HSOp ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hright_sa : IsSelfAdjoint (rightMulHS (ℋ := ℋ) A) := by
    change star (rightMulHS (ℋ := ℋ) A) = rightMulHS (ℋ := ℋ) A
    simp [hA_sa.star_eq]
  let : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  let : Nontrivial (L (HSOp ℋ)) := inferInstance
  refine ⟨hright_sa, ?_⟩
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 hA_spec
    with ⟨r, hr, hrA⟩
  refine (CFC.exists_pos_algebraMap_le_iff
    (A := L (HSOp ℋ)) (a := rightMulHS (ℋ := ℋ) A) (ha := hright_sa)).1 ?_
  refine ⟨r, hr, ?_⟩
  simpa [Algebra.algebraMap_eq_smul_one, rightMulHS_real_smul_one (ℋ := ℋ) (r := r)] using
    rightMulHS_le_rightMulHS (ℋ := ℋ) hrA

private noncomputable def phiK (K : L ℋ) (T : L (HSOp ℋ)) : ℝ :=
  Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K))))

omit [Nontrivial ℋ] in
private lemma phiK_nonneg (K : L ℋ) {T : L (HSOp ℋ)} (hT : 0 ≤ T) :
    0 ≤ phiK (ℋ := ℋ) K T := by
  dsimp [phiK]
  have hpos : T.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive T).1 hT
  have hnonneg : 0 ≤ Complex.re (inner ℂ (T (ofOp (star K))) (ofOp (star K))) := by
    exact ((ContinuousLinearMap.isPositive_iff_complex T).1 hpos (ofOp (star K))).2
  have hre :
      Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K)))) =
        Complex.re (inner ℂ (T (ofOp (star K))) (ofOp (star K))) := by
    simpa using
      (inner_re_symm (𝕜 := ℂ) (x := ofOp (star K)) (y := T (ofOp (star K))))
  rw [hre]
  exact hnonneg

omit [Nontrivial ℋ] in
private lemma phiK_add (K : L ℋ) (T S : L (HSOp ℋ)) :
    phiK (ℋ := ℋ) K (T + S) = phiK (ℋ := ℋ) K T + phiK (ℋ := ℋ) K S := by
  simp [phiK, inner_add_right, Complex.add_re]

omit [Nontrivial ℋ] in
private lemma phiK_smul (K : L ℋ) (r : ℝ) (T : L (HSOp ℋ)) :
    phiK (ℋ := ℋ) K (r • T) = r * phiK (ℋ := ℋ) K T := by
  rw [phiK]
  change Complex.re (inner ℂ (ofOp (star K)) (r • T (ofOp (star K)))) =
    r * Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K))))
  rw [show inner ℂ (ofOp (star K)) (r • T (ofOp (star K))) =
      (r : ℂ) * inner ℂ (ofOp (star K)) (T (ofOp (star K))) by
        simpa using inner_smul_right (ofOp (star K)) (T (ofOp (star K))) (r : ℂ)]
  simp

omit [Nontrivial ℋ] in
private lemma phiK_mono (K : L ℋ) {T S : L (HSOp ℋ)} (hTS : T ≤ S) :
    phiK (ℋ := ℋ) K T ≤ phiK (ℋ := ℋ) K S := by
  have hnonneg :
      0 ≤ S + (-1 : ℝ) • T := by
    simpa [sub_eq_add_neg] using (sub_nonneg.mpr hTS)
  have hphi_nonneg := phiK_nonneg (ℋ := ℋ) K hnonneg
  have hrewrite :
      phiK (ℋ := ℋ) K (S + (-1 : ℝ) • T) =
        phiK (ℋ := ℋ) K S - phiK (ℋ := ℋ) K T := by
    rw [phiK_add, phiK_smul]
    ring
  linarith [hrewrite ▸ hphi_nonneg]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
private lemma leftMulHS_rankOne (A : L ℋ) (x y : ℋ) :
    leftMulHS (ℋ := ℋ) A (ofOp (InnerProductSpace.rankOne ℂ x y)) =
      ofOp (InnerProductSpace.rankOne ℂ (A x) y) := by
  change (A * InnerProductSpace.rankOne ℂ x y) = InnerProductSpace.rankOne ℂ (A x) y
  exact
    (InnerProductSpace.comp_rankOne (𝕜 := ℂ) (x := x) (y := y) (f := A))

omit [Nontrivial ℋ] in
private lemma rightMulHS_rankOne (B : L ℋ) (x y : ℋ) :
    rightMulHS (ℋ := ℋ) B (ofOp (InnerProductSpace.rankOne ℂ x y)) =
      ofOp (InnerProductSpace.rankOne ℂ x ((star B) y)) := by
  change (InnerProductSpace.rankOne ℂ x y * B) = InnerProductSpace.rankOne ℂ x ((star B) y)
  exact
    (InnerProductSpace.rankOne_comp (𝕜 := ℂ) (x := x) (y := y) (f := B))

private lemma re_inner_nonneg_of_nonneg
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : 𝓚 →L[ℂ] 𝓚} (hT : 0 ≤ T) :
    ∀ x : 𝓚, 0 ≤ Complex.re (inner ℂ x (T x)) := by
  intro x
  have hpos : T.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive T).1 hT
  have hnonneg : 0 ≤ Complex.re (inner ℂ (T x) x) :=
    ((ContinuousLinearMap.isPositive_iff_complex T).1 hpos x).2
  have hre :
      Complex.re (inner ℂ x (T x)) = Complex.re (inner ℂ (T x) x) := by
    simpa using (inner_re_symm (𝕜 := ℂ) (x := x) (y := T x))
  rw [hre]
  exact hnonneg

private lemma aeval_apply_of_mem_eigenspace_realpoly
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : 𝓚 →L[ℂ] 𝓚} {r : ℝ} {x : 𝓚}
    (hx : x ∈ eigenspace T.toLinearMap (r : ℂ)) (p : ℝ[X]) :
    Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
      ((p.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hmap :
      Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
        Polynomial.aeval T.toLinearMap (p.map (algebraMap ℝ ℂ)) x := by
    simpa using
      congrArg (fun F : 𝓚 →ₗ[ℂ] 𝓚 => F x)
        (Polynomial.map_aeval_eq_aeval_map
          (R := ℂ) (S := 𝓚 →L[ℂ] 𝓚) (T := ℂ) (U := 𝓚 →ₗ[ℂ] 𝓚)
          (φ := RingHom.id ℂ) (ψ := ContinuousLinearMap.toLinearMapRingHom)
          (h := by ext z; rfl) (p := p.map (algebraMap ℝ ℂ)) (a := T))
  rw [hmap]
  simpa using
    (Module.End.aeval_apply_of_hasEigenvector
      (f := T.toLinearMap) (p := p.map (algebraMap ℝ ℂ)) (μ := (r : ℂ)) (x := x) ⟨hx, hx0⟩)

-- The interpolation-based `cfcR`-on-eigenspace lemma is elaboration-heavy.
private lemma cfcR_apply_of_mem_eigenspace_real
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚] [CompleteSpace 𝓚]
    [FiniteDimensional ℂ 𝓚]
    [ContinuousFunctionalCalculus ℝ (L 𝓚) IsSelfAdjoint]
    (f : ℝ → ℝ) {T : L 𝓚} (hT : IsSelfAdjoint T) {r : ℝ} {x : 𝓚}
    (hx : x ∈ eigenspace T.toLinearMap (r : ℂ)) :
    cfcR (ℋ := 𝓚) f T x = (f r : ℂ) • x := by
  have : IsScalarTower ℝ ℂ (L 𝓚) := RestrictScalars.isScalarTower ℝ ℂ (L 𝓚)
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    change Set.Finite (spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) T.toLinearMap))
    simpa using Module.End.finite_spectrum (K := ℂ) (V := 𝓚) T.toLinearMap
  have hspecRfin : Set.Finite (spectrum ℝ T) := by
    rw [← spectrum.preimage_algebraMap ℂ]
    exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  let s : Finset ℝ := hspecRfin.toFinset
  let q : ℝ[X] := Lagrange.interpolate s id fun y ↦ f y
  have hq_spec : (spectrum ℝ T).EqOn f q.eval := by
    intro y hy
    have hy' : y ∈ s := by
      simpa [s] using hy
    symm
    simpa [q] using
      (Lagrange.eval_interpolate_at_node
        (s := s) (v := id) (r := fun z ↦ f z) (i := y)
        (hvs := fun _ _ _ _ h => h) hy')
  have hcfc : cfcR (ℋ := 𝓚) f T = cfcR (ℋ := 𝓚) q.eval T := by
    simpa [cfcR] using (cfc_congr (a := T) (f := f) (g := q.eval) hq_spec)
  have hpoly : cfcR (ℋ := 𝓚) q.eval T = Polynomial.aeval T q := by
    simpa [cfcR] using (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T) hT)
  have hxv : Module.End.HasEigenvector T.toLinearMap (r : ℂ) x := ⟨hx, hx0⟩
  have hr_specC : (r : ℂ) ∈ spectrum ℂ T :=
    by
      change (r : ℂ) ∈ spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) T.toLinearMap)
      simpa using (Module.End.hasEigenvalue_of_hasEigenvector hxv).mem_spectrum
  have hr_spec : r ∈ spectrum ℝ T := spectrum.of_algebraMap_mem ℂ hr_specC
  calc
    cfcR (ℋ := 𝓚) f T x = cfcR (ℋ := 𝓚) q.eval T x := by rw [hcfc]
    _ = Polynomial.aeval T q x := by rw [hpoly]
    _ = Polynomial.aeval T (q.map (algebraMap ℝ ℂ)) x := by
      symm
      simp
    _ = ((q.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
      simpa using aeval_apply_of_mem_eigenspace_realpoly hx q
    _ = (f r : ℂ) • x := by
      congr 1
      rw [Polynomial.eval_map_algebraMap]
      calc
        Polynomial.aeval (algebraMap ℝ ℂ r) q = ((Polynomial.eval r q : ℝ) : ℂ) := by
          simpa using
            (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (x := r) (p := q))
        _ = (f r : ℂ) := by
          simpa using congrArg (fun t : ℝ => (t : ℂ)) (hq_spec hr_spec).symm

-- This proof is isolated because the joint eigenspace decomposition is heartbeat-heavy.
private lemma hmiddle_leftMul_rightMul
    {s : ℝ} {A B : L ℋ}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
        (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B)) =
      leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hA0 : 0 ≤ A := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      (by intro x hx; exact (hA_spec hx).le)
  have hB0 : 0 ≤ B := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
      (by intro x hx; exact (hB_spec hx).le)
  have hright_negHalf :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (-1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((-1 : ℝ) / 2)
          (Or.inl (ne_of_gt (hB_spec hx)))).continuousWithinAt)).symm
  have hBunit : IsUnit B := by
    refine spectrum.isUnit_of_zero_notMem (R := ℝ) ?_
    intro h0
    exact (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB_spec h0)
  have hBnegOne :
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2) = B ^ (-1 : ℝ) := by
    calc
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2)
          = B ^ (((-1 : ℝ) / 2) + ((-1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (-1 : ℝ) := by ring_nf
  have hmid_prod :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    rw [hright_negHalf]
    calc
      rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
          leftMulHS (ℋ := ℋ) A *
          rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) =
        leftMulHS (ℋ := ℋ) A *
          (rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2))) := by
            rw [← mul_assoc,
              (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ ((-1 : ℝ) / 2))).eq.symm,
              mul_assoc]
      _ = leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
            rw [← rightMulHS_mul (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) (B ^ ((-1 : ℝ) / 2)), hBnegOne]
  rw [hmid_prod]
  let T0 : HSOp ℋ →ₗ[ℂ] HSOp ℋ := (leftMulHS (ℋ := ℋ) A).toLinearMap
  let T1 : HSOp ℋ →ₗ[ℂ] HSOp ℋ := (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))).toLinearMap
  let lhs : L (HSOp ℋ) :=
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
      (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)))
  let rhs : L (HSOp ℋ) :=
    leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))
  let D : L (HSOp ℋ) := lhs - rhs
  have hleft_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A) :=
    IsSelfAdjoint.of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0)
  have hT0_symm : T0.IsSymmetric := by
    simpa [T0] using
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hleft_sa)
  have hBinv0 : 0 ≤ B ^ (-1 : ℝ) := by
    simp
  have hBinv_sa : IsSelfAdjoint (B ^ (-1 : ℝ)) := IsSelfAdjoint.of_nonneg hBinv0
  have hBinv_unit : IsUnit (B ^ (-1 : ℝ)) := by
    rcases hBunit with ⟨u, rfl⟩
    simp [CFC.rpow_neg_one_eq_inv u (by simpa using hB0)]
  have hright_sa : IsSelfAdjoint (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) :=
    IsSelfAdjoint.of_nonneg (rightMulHS_nonneg (ℋ := ℋ) hBinv0)
  have hT1_symm : T1.IsSymmetric := by
    simpa [T1] using
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hright_sa)
  have hcomm : Commute T0 T1 := by
    show T0 * T1 = T1 * T0
    ext x
    simpa [T0, T1] using congrArg (fun F : L (HSOp ℋ) => F x)
      (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ (-1 : ℝ))).eq
  have hleft_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s) (leftMulHS (ℋ := ℋ) A) =
        leftMulHS (ℋ := ℋ) (A ^ s) := by
    rw [show leftMulHS (ℋ := ℋ) (A ^ s) =
        leftMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) A) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := A) (y := s) (ha := hA0))]
    exact (leftMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) A hA_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (Or.inl (ne_of_gt (hA_spec hx)))).continuousWithinAt)).symm
  have hright_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) =
        rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ (-s)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ))) by
      congr
      calc
        B ^ (-s) = (B ^ (-1 : ℝ)) ^ s := by
          symm
          simpa using (CFC.rpow_rpow B (-1 : ℝ) s (by norm_num) (hBunit.isStrictlyPositive hB0))
        _ = cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ)) := by
          simpa [cfcR] using
            (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B ^ (-1 : ℝ)) (y := s) (ha := hBinv0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ)) hBinv_sa
      (by
        intro x hx
        have hx0 : x ≠ 0 := by
          intro hx0
          exact spectrum.zero_notMem (R := ℝ) hBinv_unit (by simpa [hx0] using hx)
        exact (Real.continuousAt_rpow_const x s (Or.inl hx0)).continuousWithinAt)).symm
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    exact (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ (-1 : ℝ))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) hA0)
      (rightMulHS_nonneg (ℋ := ℋ) hBinv0)
  have hprod_sa :
      IsSelfAdjoint
        (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) :=
    IsSelfAdjoint.of_nonneg hprod0
  have htop :
      (⨆ α, ⨆ β, eigenspace T0 α ⊓ eigenspace T1 β) = ⊤ := by
    exact LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
      hT0_symm hT1_symm hcomm
  have hjoint_ker :
      ∀ α β,
        eigenspace T0 α ⊓ eigenspace T1 β ≤ LinearMap.ker D.toLinearMap := by
    intro α β x hx
    rcases hx with ⟨hx0, hx1⟩
    rw [LinearMap.mem_ker]
    by_cases hxzero : x = 0
    · simp [D, hxzero]
    have hxv0 : Module.End.HasEigenvector T0 α x := ⟨hx0, hxzero⟩
    have hxv1 : Module.End.HasEigenvector T1 β x := ⟨hx1, hxzero⟩
    have hαeq : α = (α.re : ℂ) := by
      exact (RCLike.conj_eq_iff_re.mp
        (hT0_symm.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hxv0))
        ).symm
    have hβeq : β = (β.re : ℂ) := by
      exact (RCLike.conj_eq_iff_re.mp
        (hT1_symm.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hxv1))
        ).symm
    have hx0r : x ∈ eigenspace T0 (α.re : ℂ) := by
      rwa [hαeq] at hx0
    have hx1r : x ∈ eigenspace T1 (β.re : ℂ) := by
      rwa [hβeq] at hx1
    have hT0_nonneg_re :
        ∀ y : HSOp ℋ, 0 ≤ Complex.re (inner ℂ y (T0 y)) := by
      intro y
      simpa [T0] using
        re_inner_nonneg_of_nonneg
          (T := leftMulHS (ℋ := ℋ) A)
          (leftMulHS_nonneg (ℋ := ℋ) hA0) y
    have hT1_nonneg_re :
        ∀ y : HSOp ℋ, 0 ≤ Complex.re (inner ℂ y (T1 y)) := by
      intro y
      simpa [T1] using
        re_inner_nonneg_of_nonneg
          (T := rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)))
          (rightMulHS_nonneg (ℋ := ℋ) hBinv0) y
    have hαnonneg : 0 ≤ α.re := by
      exact eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx0r, hxzero⟩)
        hT0_nonneg_re
    have hβnonneg : 0 ≤ β.re := by
      exact eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx1r, hxzero⟩)
        hT1_nonneg_re
    have hxprod :
        x ∈ eigenspace
          ((leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))).toLinearMap)
          (((α.re * β.re : ℝ) : ℂ)) := by
      rw [Module.End.mem_eigenspace_iff]
      have hx0apply : T0 x = (α.re : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx0r
      have hx1apply : T1 x = (β.re : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx1r
      have hx0apply' :
          leftMulHS (ℋ := ℋ) A x = (α.re : ℂ) • x := by
        simpa [T0] using hx0apply
      have hx1apply' :
          rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) x = (β.re : ℂ) • x := by
        simpa [T1] using hx1apply
      show leftMulHS (ℋ := ℋ) A (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) x) =
        (((α.re * β.re : ℝ) : ℂ)) • x
      rw [hx1apply', ContinuousLinearMap.map_smul, hx0apply']
      rw [smul_smul]
      congr 1
      simp [mul_comm]
    have hlhsx :
        lhs x = ((((α.re * β.re : ℝ) ^ s : ℝ) : ℂ) • x) := by
      simpa [lhs] using
        cfcR_apply_of_mem_eigenspace_real
          (𝓚 := HSOp ℋ) (f := fun t : ℝ ↦ t ^ s) hprod_sa hxprod
    have hrhsx :
        rhs x = ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x) := by
      change (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) x =
        ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x)
      have hleftx :
          cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A) x =
            (((α.re ^ s : ℝ) : ℂ) • x) := by
        simpa using
          cfcR_apply_of_mem_eigenspace_real
            (𝓚 := HSOp ℋ) (f := fun t : ℝ ↦ t ^ s) hleft_sa hx0r
      have hrightx :
          cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s)
              (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) x =
            (((β.re ^ s : ℝ) : ℂ) • x) := by
        simpa using
          cfcR_apply_of_mem_eigenspace_real
            (𝓚 := HSOp ℋ) (f := fun t : ℝ ↦ t ^ s) hright_sa hx1r
      rw [← hleft_pow, ← hright_pow, ContinuousLinearMap.mul_def]
      show cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A)
          (cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s)
            (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) x) =
        ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x)
      rw [hrightx, ContinuousLinearMap.map_smul, hleftx]
      rw [smul_smul]
      congr 1
      simp [mul_comm]
    have hscal :
        (((α.re * β.re : ℝ) ^ s : ℝ) : ℂ) =
          ((((α.re ^ s) * (β.re ^ s) : ℝ)) : ℂ) := by
      exact congrArg (fun t : ℝ => (t : ℂ)) (Real.mul_rpow hαnonneg hβnonneg)
    simpa [D] using
      sub_eq_zero.mpr (hlhsx.trans (hscal ▸ hrhsx.symm))
  have hker_top : LinearMap.ker D.toLinearMap = ⊤ := by
    apply top_unique
    rw [← htop]
    refine iSup_le ?_
    intro α
    refine iSup_le ?_
    intro β
    exact hjoint_ker α β
  have hDzero : D = 0 := by
    ext x
    have hx : x ∈ LinearMap.ker D.toLinearMap := by simp [hker_top]
    exact LinearMap.mem_ker.mp hx
  have hlhs_eq_rhs : lhs = rhs := sub_eq_zero.mp hDzero
  simpa [lhs, rhs] using hlhs_eq_rhs

-- The bridge lemma expands a large `HSOp`-valued generalized perspective term.
set_option backward.isDefEq.respectTransparency false in
private lemma phiK_operatorPowerMean_eq_liebTraceMap
    {s : ℝ} (K A B : L ℋ) (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B)) =
      liebTraceMap (ℋ := ℋ) s K A B := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hA0 : 0 ≤ A := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      (by intro x hx; exact (hA_spec hx).le)
  have hB0 : 0 ≤ B := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
      (by intro x hx; exact (hB_spec hx).le)
  have hright_half :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((1 : ℝ) / 2)
          (Or.inr (by positivity))).continuousWithinAt)).symm
  have hright_negHalf :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (-1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((-1 : ℝ) / 2)
          (Or.inl (ne_of_gt (hB_spec hx)))).continuousWithinAt)).symm
  have hBunit : IsUnit B := by
    refine spectrum.isUnit_of_zero_notMem (R := ℝ) ?_
    intro h0
    exact (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB_spec h0)
  have hBpow :
      B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2) = B ^ (1 - s) := by
    calc
      B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2)
          = B ^ (((1 : ℝ) / 2) + (-s)) * B ^ ((1 : ℝ) / 2) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ ((((1 : ℝ) / 2) + (-s)) + ((1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (1 - s) := by ring_nf
  have hBnegOne :
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2) = B ^ (-1 : ℝ) := by
    calc
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2)
          = B ^ (((-1 : ℝ) / 2) + ((-1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (-1 : ℝ) := by ring_nf
  have hBinvHalf0 : 0 ≤ B ^ ((-1 : ℝ) / 2) := by
    simp
  have hBinv0 : 0 ≤ B ^ (-1 : ℝ) := by
    simp
  have hBinv_sa : IsSelfAdjoint (B ^ (-1 : ℝ)) := IsSelfAdjoint.of_nonneg hBinv0
  have hright_invHalf0 :
      0 ≤ rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    exact rightMulHS_nonneg (ℋ := ℋ) hBinvHalf0
  have hmid_nonneg :
      0 ≤ cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) := by
    rw [hright_negHalf]
    simpa [mul_assoc] using
      conjugate_nonneg_of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0) hright_invHalf0
  have hmid_prod :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    rw [hright_negHalf]
    calc
      rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
          leftMulHS (ℋ := ℋ) A *
          rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2))
          =
        leftMulHS (ℋ := ℋ) A *
          (rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2))) := by
            rw [← mul_assoc,
              (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ ((-1 : ℝ) / 2))).eq.symm,
              mul_assoc]
      _ = leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
            rw [← rightMulHS_mul (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) (B ^ ((-1 : ℝ) / 2)), hBnegOne]
  have hmiddle :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
            leftMulHS (ℋ := ℋ) A *
            cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    exact hmiddle_leftMul_rightMul (ℋ := ℋ) (s := s) ⟨hA_sa, hA_spec⟩ ⟨hB_sa, hB_spec⟩
  have happly :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K)) =
        ofOp (A ^ s * star K * B ^ (1 - s)) := by
    have hcomm_half :
        Commute (leftMulHS (ℋ := ℋ) (A ^ s)) (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) :=
      leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s) (B ^ ((1 : ℝ) / 2))
    have hright_pow :
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s)) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
          rightMulHS (ℋ := ℋ) (B ^ (1 - s)) := by
      calc
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s)) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))
            =
          rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2)) := by
            simp [mul_assoc]
        _ = rightMulHS (ℋ := ℋ) (B ^ (1 - s)) := by rw [hBpow]
    have hreorder :
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
          leftMulHS (ℋ := ℋ) (A ^ s) *
            (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              rightMulHS (ℋ := ℋ) (B ^ (-s)) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) := by
      calc
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))
            =
          ((rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              leftMulHS (ℋ := ℋ) (A ^ s)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
                simp [mul_assoc]
        _ =
          ((leftMulHS (ℋ := ℋ) (A ^ s) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) *
            rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
                rw [hcomm_half.eq]
        _ =
          leftMulHS (ℋ := ℋ) (A ^ s) *
            (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              rightMulHS (ℋ := ℋ) (B ^ (-s)) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) := by
                simp [mul_assoc]
    calc
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K))
        =
          (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) (ofOp (star K)) := by
            rw [OperatorGeometricMean.operatorPowerMean, GeneralizedPerspective,
              GeneralizedPerspectiveFunction.hSqrt, GeneralizedPerspectiveFunction.hInvSqrt]
            simp only [Real.rpow_one]
            rw [hmiddle]
            rw [hright_half]
      _ =
          (leftMulHS (ℋ := ℋ) (A ^ s) *
              (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
                rightMulHS (ℋ := ℋ) (B ^ (-s)) *
                rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)))) (ofOp (star K)) := by
            rw [hreorder]
      _ =
          (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (1 - s))) (ofOp (star K)) := by
            rw [hright_pow]
      _ = ofOp (A ^ s * star K * B ^ (1 - s)) := by
            simp [leftMulHS_apply, rightMulHS_apply, mul_assoc]
  calc
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B))
      = Complex.re
          (inner ℂ (ofOp (star K))
            (ofOp (A ^ s * star K * B ^ (1 - s)))) := by
            simp [phiK, happly]
    _ = traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K) := by
          rw [traceRe]
          set X : L ℋ := A ^ s * star K * B ^ (1 - s)
          have htrace :=
            re_hsInner_eq_traceRe (ℋ := ℋ) (X := star K) (Y := X)
          have htrace' :
              Complex.re (inner ℂ (ofOp (star K)) (ofOp X)) =
                Complex.re (LinearMap.trace ℂ ℋ
                  ((K * X).toLinearMap)) := by
            simpa [X, mul_assoc] using htrace
          have hcycle :
              Complex.re (LinearMap.trace ℂ ℋ ((K * X).toLinearMap)) =
                Complex.re (LinearMap.trace ℂ ℋ ((X * K).toLinearMap)) := by
            simpa using
              congrArg Complex.re
                (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) K.toLinearMap X.toLinearMap)
          simpa [X, mul_assoc] using htrace'.trans hcycle
    _ = liebTraceMap (ℋ := ℋ) s K A B := by
          rfl

omit [FiniteDimensional ℂ ℋ] in
/-- Convex combinations preserve `pdSet` (strict positivity). -/
lemma pdSet_convexCombo {A B : L ℋ} {t : ℝ}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • A + t • B) ∈ pdSet (ℋ := ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  set C : L ℋ := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA_sa |>.add ((IsSelfAdjoint.all t).smul hB_sa)
  have hApos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 ?_
    intro x hx
    exact hA_spec hx
  have hBpos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := B) (ha := hB_sa)).2 ?_
    intro x hx
    exact hB_spec hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by linarith
      subst ht'
      simpa [rC] using hrB
    · have h1t_pos : 0 < 1 - t := lt_of_le_of_ne (sub_nonneg.mpr ht1) (Ne.symm h1t)
      simpa [rC] using
        add_pos_of_pos_of_nonneg (mul_pos h1t_pos hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (L ℋ) rC ≤ C := by
    have hsum :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB ≤ C := by
      simpa [C] using
        add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
          (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB =
          algebraMap ℝ (L ℋ) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  refine ⟨hC, ?_⟩
  intro x hx
  simpa [C] using
    (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx

set_option backward.isDefEq.respectTransparency false in
omit [Nontrivial ℋ] in
private lemma phiK_leftMul_rightMul_eq_traceRe (K C D : L ℋ) :
    phiK (ℋ := ℋ) K
        (leftMulHS (ℋ := ℋ) C * rightMulHS (ℋ := ℋ) D) =
      traceRe (ℋ := ℋ) (C * star K * D * K) := by
  calc
    phiK (ℋ := ℋ) K
        (leftMulHS (ℋ := ℋ) C * rightMulHS (ℋ := ℋ) D)
      = Complex.re
          (inner ℂ (ofOp (star K))
            ((leftMulHS (ℋ := ℋ) C * rightMulHS (ℋ := ℋ) D) (ofOp (star K)))) := by
            simp [phiK]
    _ = Complex.re
          (inner ℂ (ofOp (star K))
            (ofOp (C * star K * D))) := by
            simp [leftMulHS_apply, rightMulHS_apply, mul_assoc]
    _ = traceRe (ℋ := ℋ) (C * star K * D * K) := by
          rw [traceRe]
          set X : L ℋ := C * star K * D
          have htrace :=
            re_hsInner_eq_traceRe (ℋ := ℋ) (X := star K) (Y := X)
          have htrace' :
              Complex.re (inner ℂ (ofOp (star K)) (ofOp X)) =
                Complex.re (LinearMap.trace ℂ ℋ ((K * X).toLinearMap)) := by
            simpa [X, mul_assoc] using htrace
          have hcycle :
              Complex.re (LinearMap.trace ℂ ℋ ((K * X).toLinearMap)) =
                Complex.re (LinearMap.trace ℂ ℋ ((X * K).toLinearMap)) := by
            simpa using
              congrArg Complex.re
                (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) K.toLinearMap X.toLinearMap)
          simpa [X, mul_assoc] using htrace'.trans hcycle

omit [FiniteDimensional ℂ ℋ] in
private lemma pdSet_rpow_of_mem_Icc_zero_one
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {A : L ℋ} (hA : A ∈ pdSet (ℋ := ℋ)) :
    A ^ p ∈ pdSet (ℋ := ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hA0 : 0 ≤ A := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      (by intro x hx; exact (hA_spec hx).le)
  have hApow0 : 0 ≤ A ^ p := by
    simp
  have hApow_sa : IsSelfAdjoint (A ^ p) := IsSelfAdjoint.of_nonneg hApow0
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 hA_spec with
    ⟨r, hr, hrA⟩
  refine ⟨hApow_sa, ?_⟩
  have hr0 : 0 ≤ algebraMap ℝ (L ℋ) r := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      smul_nonneg hr.le (show (0 : L ℋ) ≤ 1 by simp)
  have hmono :=
    power_Icc_zero_one_operatorMonotoneOn_Ici (ℋ := ℋ) p hp
      (A := A) (B := algebraMap ℝ (L ℋ) r)
      hA0 hr0 hrA
      (by
        intro x hx
        have hx0 : 0 < x := by simpa [Set.Ioi] using hA_spec hx
        exact hx0.le)
      (by
        intro x hx
        exact spectrum_nonneg_of_nonneg hr0 hx)
  have hApow :
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ p) A = A ^ p := by
    simpa [cfcR, LownerHeinzCore.cfcR] using
      (CFC.rpow_eq_cfc_real (A := L ℋ) (a := A) (y := p) (ha := hA0)).symm
  have hscalar :
      (algebraMap ℝ (L ℋ) r) ^ p = algebraMap ℝ (L ℋ) (r ^ p) := by
    rw [CFC.rpow_eq_cfc_real (A := L ℋ) (a := algebraMap ℝ (L ℋ) r) (y := p) (ha := hr0)]
    simp
  have hbound : algebraMap ℝ (L ℋ) (r ^ p) ≤ A ^ p := by
    simpa [hscalar, hApow] using hmono
  exact (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A ^ p) (ha := hApow_sa)).1
    ⟨r ^ p, Real.rpow_pos_of_pos hr p, hbound⟩

omit [Nontrivial ℋ] in
private lemma liebTraceMap_mono_right
    {s : ℝ} (hs : 1 - s ∈ Set.Icc (0 : ℝ) 1)
    (K A B₁ B₂ : L ℋ)
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ))
    (hB : B₁ ≤ B₂) :
    liebTraceMap (ℋ := ℋ) s K A B₁ ≤ liebTraceMap (ℋ := ℋ) s K A B₂ := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  have hA0 : 0 ≤ A := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      (by intro x hx; exact (hA_spec hx).le)
  have hB₁0 : 0 ≤ B₁ := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ (ha := hB₁_sa)).2
      (by intro x hx; exact (hB₁_spec hx).le)
  have hB₂0 : 0 ≤ B₂ := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ (ha := hB₂_sa)).2
      (by intro x hx; exact (hB₂_spec hx).le)
  have hcfc :=
    power_Icc_zero_one_operatorMonotoneOn_Ici (ℋ := ℋ) (1 - s) hs
      (A := B₂) (B := B₁) hB₂0 hB₁0 hB
      (by
        intro x hx
        have hx0 : 0 < x := by simpa [Set.Ioi] using hB₂_spec hx
        exact hx0.le)
      (by
        intro x hx
        have hx0 : 0 < x := by simpa [Set.Ioi] using hB₁_spec hx
        exact hx0.le)
  have hpow :
      B₁ ^ (1 - s) ≤ B₂ ^ (1 - s) := by
    simpa [cfcR, LownerHeinzCore.cfcR,
      CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₁) (y := 1 - s) (ha := hB₁0),
      CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₂) (y := 1 - s) (ha := hB₂0)] using hcfc
  have hApow0 : 0 ≤ A ^ s := by
    simp
  have hdiff0 : 0 ≤ B₂ ^ (1 - s) - B₁ ^ (1 - s) := sub_nonneg.mpr hpow
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s)) := by
    exact (leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s) (B₂ ^ (1 - s) - B₁ ^ (1 - s))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) hApow0)
      (rightMulHS_nonneg (ℋ := ℋ) hdiff0)
  have hphi : 0 ≤
      phiK (ℋ := ℋ) K
        (leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s))) :=
    phiK_nonneg (ℋ := ℋ) K hprod0
  have hsplit :
      leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s)) -
          leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s)) := by
    ext T
    show (A ^ s * (toOp T * (B₂ ^ (1 - s) - B₁ ^ (1 - s))) : L ℋ) =
      A ^ s * (toOp T * B₂ ^ (1 - s)) - A ^ s * (toOp T * B₁ ^ (1 - s))
    simp [mul_sub]
  have hrewrite :
      phiK (ℋ := ℋ) K
          (leftMulHS (ℋ := ℋ) (A ^ s) *
            rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s))) =
        liebTraceMap (ℋ := ℋ) s K A B₂ - liebTraceMap (ℋ := ℋ) s K A B₁ := by
    rw [hsplit, sub_eq_add_neg, phiK_add]
    rw [show -(leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s))) =
        (-1 : ℝ) • (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s))) by simp,
      phiK_smul]
    simp [phiK_leftMul_rightMul_eq_traceRe, liebTraceMap, mul_assoc, sub_eq_add_neg]
  linarith [hrewrite ▸ hphi]

omit [Nontrivial ℋ] in
private lemma liebTraceMap_antitone_right
    {s : ℝ} (hs : 1 - s ∈ Set.Icc (-1 : ℝ) 0)
    (K A B₁ B₂ : L ℋ)
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ))
    (hB : B₁ ≤ B₂) :
    liebTraceMap (ℋ := ℋ) s K A B₂ ≤ liebTraceMap (ℋ := ℋ) s K A B₁ := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  have hA0 : 0 ≤ A := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      (by intro x hx; exact (hA_spec hx).le)
  have hcfc :=
    power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi (ℋ := ℋ) (1 - s) hs
      (A := B₂) (B := B₁)
      (show (0 : L ℋ) ≤ B₂ by
        exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ (ha := hB₂_sa)).2
          (by intro x hx; exact (hB₂_spec hx).le))
      (show (0 : L ℋ) ≤ B₁ by
        exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ (ha := hB₁_sa)).2
          (by intro x hx; exact (hB₁_spec hx).le))
      hB
      (by
        intro x hx
        exact hB₂_spec hx)
      (by
        intro x hx
        exact hB₁_spec hx)
  have hpow :
      B₂ ^ (1 - s) ≤ B₁ ^ (1 - s) := by
    have hnegpow : -(B₁ ^ (1 - s)) ≤ -(B₂ ^ (1 - s)) := by
      simpa [cfcR, LownerHeinzCore.cfcR, cfc_neg,
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₁) (y := 1 - s)
          (ha := (show 0 ≤ B₁ by
            exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ (ha := hB₁_sa)).2
              (by intro x hx; exact (hB₁_spec hx).le))),
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₂) (y := 1 - s)
          (ha := (show 0 ≤ B₂ by
            exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ (ha := hB₂_sa)).2
              (by intro x hx; exact (hB₂_spec hx).le)))] using hcfc
    simpa using (neg_le_neg_iff.mp hnegpow)
  have hApow0 : 0 ≤ A ^ s := by
    simp
  have hdiff0 : 0 ≤ B₁ ^ (1 - s) - B₂ ^ (1 - s) := sub_nonneg.mpr hpow
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s)) := by
    exact (leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s) (B₁ ^ (1 - s) - B₂ ^ (1 - s))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) hApow0)
      (rightMulHS_nonneg (ℋ := ℋ) hdiff0)
  have hphi : 0 ≤
      phiK (ℋ := ℋ) K
        (leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s))) :=
    phiK_nonneg (ℋ := ℋ) K hprod0
  have hsplit :
      leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s)) -
          leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s)) := by
    ext T
    show (A ^ s * (toOp T * (B₁ ^ (1 - s) - B₂ ^ (1 - s))) : L ℋ) =
      A ^ s * (toOp T * B₁ ^ (1 - s)) - A ^ s * (toOp T * B₂ ^ (1 - s))
    simp [mul_sub]
  have hrewrite :
      phiK (ℋ := ℋ) K
          (leftMulHS (ℋ := ℋ) (A ^ s) *
            rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s))) =
        liebTraceMap (ℋ := ℋ) s K A B₁ - liebTraceMap (ℋ := ℋ) s K A B₂ := by
    rw [hsplit, sub_eq_add_neg, phiK_add]
    rw [show -(leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s))) =
        (-1 : ℝ) • (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s))) by simp,
      phiK_smul]
    simp [phiK_leftMul_rightMul_eq_traceRe, liebTraceMap, mul_assoc, sub_eq_add_neg]
  linarith [hrewrite ▸ hphi]

private lemma phiK_weightedSum_operatorPowerMean_eq
    {s θ : ℝ} (K A₁ A₂ B₁ B₂ : L ℋ)
    (hA₁ : A₁ ∈ pdSet (ℋ := ℋ)) (hA₂ : A₂ ∈ pdSet (ℋ := ℋ))
    (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ)) :
    phiK (ℋ := ℋ) K
        ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) • liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ • liebTraceMap (ℋ := ℋ) s K A₂ B₂ := by
  rw [phiK_add, phiK_smul, phiK_smul]
  simpa [smul_eq_mul] using
    show (1 - θ) * phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁)) +
      θ * phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) * liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ * liebTraceMap (ℋ := ℋ) s K A₂ B₂ by
      simp only [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K A₁ B₁ hA₁ hB₁,
    phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K A₂ B₂ hA₂ hB₂]

-- The `HSOp`-valued `operatorPowerMean` terms are large enough that the skeleton itself is expensive.
theorem liebTrace_jointlyConcaveOn_pdSet
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : L ℋ) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    show ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    show ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo :
      ((1 - θ) • A₁ + θ • A₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo :
      ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  let : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  let : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hconc_hs :=
    operatorPowerMean_jointlyConcaveOn_pdSet
      (ℋ := HSOp ℋ) (α := s) (β := 1)
      ⟨le_of_lt hs0, hs1.le⟩ ⟨by norm_num, by norm_num⟩
      (A₁ := leftMulHS (ℋ := ℋ) A₁) (A₂ := leftMulHS (ℋ := ℋ) A₂)
      (B₁ := rightMulHS (ℋ := ℋ) B₁) (B₂ := rightMulHS (ℋ := ℋ) B₂)
      (θ := θ)
      (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
      (rightMulHS_pdSet (ℋ := ℋ) hB₁) (rightMulHS_pdSet (ℋ := ℋ) hB₂)
      hθ0 hθ1
  have hconc :
      (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
        θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂) ≤
        operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
          (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂)) := by
    simpa [hleft_combo, hright_combo] using hconc_hs
  have hphi_mono :
      phiK (ℋ := ℋ) K
          ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
            θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) ≤
        phiK (ℋ := ℋ) K
          (operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
            (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂))) := by
    exact phiK_mono (ℋ := ℋ) K hconc
  rw [phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  rw [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono

theorem liebTrace_jointlyConvexOn_pdSet
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    show ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    show ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo :
      ((1 - θ) • A₁ + θ • A₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo :
      ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  let : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  let : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hconv_hs :=
    operatorPowerMean_jointlyConvexOn_pdSet
      (ℋ := HSOp ℋ) (α := s) (β := 1)
      ⟨hs1, hs2⟩ ⟨by norm_num, by norm_num⟩
      (A₁ := leftMulHS (ℋ := ℋ) A₁) (A₂ := leftMulHS (ℋ := ℋ) A₂)
      (B₁ := rightMulHS (ℋ := ℋ) B₁) (B₂ := rightMulHS (ℋ := ℋ) B₂)
      (θ := θ)
      (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
      (rightMulHS_pdSet (ℋ := ℋ) hB₁) (rightMulHS_pdSet (ℋ := ℋ) hB₂)
      hθ0 hθ1
  have hconv :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
          (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂)) ≤
        (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂) := by
    simpa [hleft_combo, hright_combo] using hconv_hs
  have hphi_mono :
      phiK (ℋ := ℋ) K
          (operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
            (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂))) ≤
        phiK (ℋ := ℋ) K
          ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
            θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) := by
    exact phiK_mono (ℋ := ℋ) K hconv
  rw [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  rw [phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono

theorem liebExtensionTrace_jointlyConcaveOn_pdSet
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1) (K : L ℋ) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebExtensionTraceMap (ℋ := ℋ) q p K) := by
  have hq1 : q < 1 := by linarith
  let β : ℝ := p / (1 - q)
  have h1q : 0 < 1 - q := by linarith
  have hβ0 : 0 ≤ β := by
    dsimp [β]
    positivity
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    field_simp [h1q.ne']
    linarith
  have hβ : β ∈ Set.Icc (0 : ℝ) 1 := ⟨hβ0, hβ1⟩
  have hβmul : β * (1 - q) = p := by
    dsimp [β]
    field_simp [h1q.ne']
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hA_combo :
      ((1 - θ) • A₁ + θ • A₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo :
      ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  have hB₁β : B₁ ^ β ∈ pdSet (ℋ := ℋ) :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₁
  have hB₂β : B₂ ^ β ∈ pdSet (ℋ := ℋ) :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₂
  have hB_comboβ :
      (((1 - θ) • B₁ + θ • B₂) ^ β) ∈ pdSet (ℋ := ℋ) :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB_combo
  have hBpow_combo :
      ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hB₁β hB₂β hθ0 hθ1
  have hB₁_mem := hB₁
  have hB₂_mem := hB₂
  have hB_combo_mem := hB_combo
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  rcases hB_combo with ⟨hB_combo_sa, hB_combo_spec⟩
  have hB₁0 : 0 ≤ B₁ := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ (ha := hB₁_sa)).2
      (by intro x hx; exact (hB₁_spec hx).le)
  have hB₂0 : 0 ≤ B₂ := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ (ha := hB₂_sa)).2
      (by intro x hx; exact (hB₂_spec hx).le)
  have hBcombo0 : 0 ≤ ((1 - θ) • B₁ + θ • B₂) := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) ((1 - θ) • B₁ + θ • B₂)
      (ha := hB_combo_sa)).2
      (by intro x hx; exact (hB_combo_spec hx).le)
  have hpow_conc :=
    power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) β hβ
      (A := B₁) (B := B₂) (t := θ) hB₁_sa hB₂_sa hθ0 hθ1
      (by
        intro x hx
        have hx0 : 0 < x := by simpa [Set.Ioi] using hB₁_spec hx
        exact hx0.le)
      (by
        intro x hx
        have hx0 : 0 < x := by simpa [Set.Ioi] using hB₂_spec hx
        exact hx0.le)
  have hBpow_le :
      (1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β) ≤
        ((1 - θ) • B₁ + θ • B₂) ^ β := by
    have hBcombo0' : 0 ≤ θ • B₂ + (1 - θ) • B₁ := by
      simpa [add_comm, add_left_comm, add_assoc] using hBcombo0
    have hneg :
        -(((1 - θ) • B₁ + θ • B₂) ^ β) ≤
          -((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) := by
      simpa [cfcR, LownerHeinzCore.cfcR, cfc_neg, smul_neg, neg_add,
        add_comm, add_left_comm, add_assoc,
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₁) (y := β) (ha := hB₁0),
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₂) (y := β) (ha := hB₂0),
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := θ • B₂ + (1 - θ) • B₁) (y := β) (ha := hBcombo0'),
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := ((1 - θ) • B₁ + θ • B₂)) (y := β) (ha := hBcombo0)]
        using hpow_conc
    exact neg_le_neg_iff.mp hneg
  have hsmono : 1 - q ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hmono :
      liebTraceMap (ℋ := ℋ) q K
          ((1 - θ) • A₁ + θ • A₂)
          ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) ≤
        liebTraceMap (ℋ := ℋ) q K
          ((1 - θ) • A₁ + θ • A₂)
          (((1 - θ) • B₁ + θ • B₂) ^ β) := by
    exact liebTraceMap_mono_right (ℋ := ℋ) (s := q) hsmono K
      ((1 - θ) • A₁ + θ • A₂)
      ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β))
      (((1 - θ) • B₁ + θ • B₂) ^ β)
      hA_combo hBpow_combo hB_comboβ hBpow_le
  have hconc :=
    liebTrace_jointlyConcaveOn_pdSet (ℋ := ℋ) (s := q) hq hq1 K
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁ ^ β) (B₂ := B₂ ^ β)
      (θ := θ) hA₁ hA₂ hB₁β hB₂β hθ0 hθ1
  have hpow_rewrite :
      ∀ {A B : L ℋ}, B ∈ pdSet (ℋ := ℋ) →
        liebTraceMap (ℋ := ℋ) q K A (B ^ β) =
          liebExtensionTraceMap (ℋ := ℋ) q p K A B := by
    intro A B hB
    rcases hB with ⟨hB_sa, hB_spec⟩
    have hB0 : 0 ≤ B := by
      exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
        (by intro x hx; exact (hB_spec hx).le)
    have hpow :
        (B ^ β) ^ (1 - q) = B ^ p := by
      calc
        (B ^ β) ^ (1 - q) = B ^ (β * (1 - q)) := by
            simpa using
              (CFC.rpow_rpow_of_exponent_nonneg (A := L ℋ) B β (1 - q) hβ0 (by linarith) hB0)
        _ = B ^ p := by rw [hβmul]
    simp [liebTraceMap, liebExtensionTraceMap, hpow, mul_assoc]
  simpa [hpow_rewrite hB₁_mem, hpow_rewrite hB₂_mem, hpow_rewrite hB_combo_mem] using
    (le_trans hconc hmono)

theorem andoTrace_jointlyConvexOn_pdSet
    {q r : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hqr : 1 ≤ q - r) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (andoTraceMap (ℋ := ℋ) q r K) := by
  by_cases hqeq : q = 1
  · have hrz : r = 0 := by linarith
    subst hqeq
    subst hrz
    convert (liebTrace_jointlyConvexOn_pdSet (s := 1) (by norm_num) (by norm_num) K) using 1
    ext A B
    simp [andoTraceMap, liebTraceMap]
  · have hqgt : 1 < q := lt_of_le_of_ne hq1 (Ne.symm hqeq)
    let β : ℝ := r / (q - 1)
    have hq1pos : 0 < q - 1 := by linarith
    have hβ0 : 0 ≤ β := by
      dsimp [β]
      positivity
    have hβ1 : β ≤ 1 := by
      dsimp [β]
      field_simp [hq1pos.ne']
      linarith
    have hβ : β ∈ Set.Icc (0 : ℝ) 1 := ⟨hβ0, hβ1⟩
    have hβmul : β * (1 - q) = -r := by
      dsimp [β]
      field_simp [hq1pos.ne']
      ring
    intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
    have hA_combo :
        ((1 - θ) • A₁ + θ • A₂) ∈ pdSet (ℋ := ℋ) := by
      exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
    have hB_combo :
        ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) := by
      exact pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
    have hB₁β : B₁ ^ β ∈ pdSet (ℋ := ℋ) :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₁
    have hB₂β : B₂ ^ β ∈ pdSet (ℋ := ℋ) :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₂
    have hB_comboβ :
        (((1 - θ) • B₁ + θ • B₂) ^ β) ∈ pdSet (ℋ := ℋ) :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB_combo
    have hBpow_combo :
        ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) ∈ pdSet (ℋ := ℋ) := by
      exact pdSet_convexCombo (ℋ := ℋ) hB₁β hB₂β hθ0 hθ1
    have hB₁_mem := hB₁
    have hB₂_mem := hB₂
    have hB_combo_mem := hB_combo
    rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
    rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
    rcases hB_combo with ⟨hB_combo_sa, hB_combo_spec⟩
    have hB₁0 : 0 ≤ B₁ := by
      exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ (ha := hB₁_sa)).2
        (by intro x hx; exact (hB₁_spec hx).le)
    have hB₂0 : 0 ≤ B₂ := by
      exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ (ha := hB₂_sa)).2
        (by intro x hx; exact (hB₂_spec hx).le)
    have hBcombo0 : 0 ≤ ((1 - θ) • B₁ + θ • B₂) := by
      exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) ((1 - θ) • B₁ + θ • B₂)
        (ha := hB_combo_sa)).2
        (by intro x hx; exact (hB_combo_spec hx).le)
    have hpow_conc :=
      power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) β hβ
        (A := B₁) (B := B₂) (t := θ) hB₁_sa hB₂_sa hθ0 hθ1
        (by
          intro x hx
          have hx0 : 0 < x := by simpa [Set.Ioi] using hB₁_spec hx
          exact hx0.le)
        (by
          intro x hx
          have hx0 : 0 < x := by simpa [Set.Ioi] using hB₂_spec hx
          exact hx0.le)
    have hBcombo0' : 0 ≤ θ • B₂ + (1 - θ) • B₁ := by
      simpa [add_comm, add_left_comm, add_assoc] using hBcombo0
    have hBpow_le :
        (1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β) ≤
          ((1 - θ) • B₁ + θ • B₂) ^ β := by
      have hneg :
          -(((1 - θ) • B₁ + θ • B₂) ^ β) ≤
            -((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) := by
        simpa [cfcR, LownerHeinzCore.cfcR, cfc_neg, smul_neg, neg_add,
          add_comm, add_left_comm, add_assoc,
          CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₁) (y := β) (ha := hB₁0),
          CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₂) (y := β) (ha := hB₂0),
          CFC.rpow_eq_cfc_real (A := L ℋ) (a := θ • B₂ + (1 - θ) • B₁) (y := β) (ha := hBcombo0'),
          CFC.rpow_eq_cfc_real (A := L ℋ) (a := ((1 - θ) • B₁ + θ • B₂)) (y := β) (ha := hBcombo0)]
          using hpow_conc
      exact neg_le_neg_iff.mp hneg
    have hsanti : 1 - q ∈ Set.Icc (-1 : ℝ) 0 := by
      constructor <;> linarith
    have hmono :
        liebTraceMap (ℋ := ℋ) q K
            ((1 - θ) • A₁ + θ • A₂)
            (((1 - θ) • B₁ + θ • B₂) ^ β) ≤
          liebTraceMap (ℋ := ℋ) q K
            ((1 - θ) • A₁ + θ • A₂)
            ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) := by
      exact liebTraceMap_antitone_right (ℋ := ℋ) (s := q) hsanti K
        ((1 - θ) • A₁ + θ • A₂)
        ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β))
        (((1 - θ) • B₁ + θ • B₂) ^ β)
        hA_combo hBpow_combo hB_comboβ hBpow_le
    have hconv :=
      liebTrace_jointlyConvexOn_pdSet (ℋ := ℋ) (s := q) hq1 hq2 K
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁ ^ β) (B₂ := B₂ ^ β)
        (θ := θ) hA₁ hA₂ hB₁β hB₂β hθ0 hθ1
    have hpow_rewrite :
        ∀ {A B : L ℋ}, B ∈ pdSet (ℋ := ℋ) →
          liebTraceMap (ℋ := ℋ) q K A (B ^ β) =
            andoTraceMap (ℋ := ℋ) q r K A B := by
      intro A B hB
      rcases hB with ⟨hB_sa, hB_spec⟩
      have hB0 : 0 ≤ B := by
        exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
          (by intro x hx; exact (hB_spec hx).le)
      have hBunit : IsUnit B := by
        refine spectrum.isUnit_of_zero_notMem (R := ℝ) ?_
        intro h0
        exact (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB_spec h0)
      have hpow :
          (B ^ β) ^ (1 - q) = B ^ (-r) := by
        by_cases hβzero : β = 0
        · have hrz : r = 0 := by
            rw [hβzero] at hβmul
            linarith
          have hBzero : B ^ (0 : ℝ) = (1 : L ℋ) := by
            simpa using (CFC.rpow_zero (a := B))
          calc
            (B ^ β) ^ (1 - q) = (B ^ (0 : ℝ)) ^ (1 - q) := by simp [hβzero]
            _ = (1 : L ℋ) ^ (1 - q) := by rw [hBzero]
            _ = (1 : L ℋ) := by simp
            _ = B ^ (0 : ℝ) := by rw [hBzero]
            _ = B ^ (-r) := by simp [hrz]
        · calc
            (B ^ β) ^ (1 - q) = B ^ (β * (1 - q)) := by
                simpa [mul_comm] using
                  (CFC.rpow_rpow B β (1 - q) hβzero (hBunit.isStrictlyPositive hB0))
            _ = B ^ (-r) := by rw [hβmul]
      simp [liebTraceMap, andoTraceMap, hpow, mul_assoc]
    simpa [hpow_rewrite hB₁_mem, hpow_rewrite hB₂_mem, hpow_rewrite hB_combo_mem] using
      (le_trans hmono hconv)

theorem liebCorollaryTrace_jointlyConvexOn_pdSet
    {q r : ℝ} (hr1 : 1 < r) (hrq : r ≤ q) (hq2 : q ≤ 2) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebCorollaryTraceMap (ℋ := ℋ) q r K) := by
  have hq1 : 1 ≤ q := by linarith
  have hr0 : 0 ≤ r - 1 := by linarith
  have hr1' : r - 1 ≤ 1 := by linarith
  have hqr' : 1 ≤ q - (r - 1) := by linarith
  convert
    (andoTrace_jointlyConvexOn_pdSet (ℋ := ℋ) (q := q) (r := r - 1)
      hq1 hq2 hr0 hr1' hqr' K) using 1
  ext A B
  simp [liebCorollaryTraceMap, andoTraceMap]

end LiebAndoTrace
