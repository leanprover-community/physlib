/-
Copyright (c) 2025 Rein Zustand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rein Zustand
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange

/-!

# Equivalent Lagrangians under Total Derivatives

## i. Overview

Two Lagrangians are physically equivalent if they differ by a total time derivative
d/dt F(q, t). This is because the Euler-Lagrange equations depend only on extremizing
the action integral, and total derivatives don't affect which paths are extremal.

This module defines the key concept of a function being a total time derivative,
which is essential for analyzing symmetries like Galilean invariance.

Note: Some authors call this "gauge equivalence" by analogy with gauge transformations
in field theory, but we avoid that terminology here since no gauge fields are involved.

## ii. Key insight

A general function δL(t, q, dₜ q) is a total time derivative if there exists a function
F(t, q) (independent of velocity) such that:
  δL(t, q, dₜ q) = d/dt F(t, q) = fderiv ℝ F (t q) (v, 1)

By the chain rule, this expands to:
  δL(t, q, dₜ q) = ∂F/∂t + ⟨∇ᵣF, dₜ q⟩

For the special case where δL depends only on velocity dₜ q (not position or time),
this implies a strong constraint:
  δL(dₜ q) = ⟨g, dₜ q⟩ for some constant vector g

This is because:
1. d/dt F(t, q) = ∂F/∂t + ⟨∇F, dₜ q⟩
2. For δL to be q-independent, ∇F must be q-independent
3. For δL to be t-independent, the time-dependent part must vanish
4. The result is δL = ⟨g, dₜ q⟩ for constant g

## iii. Key definitions

- `IsTotalTimeDerivative`: General case for δL(t, q, dₜ q)
- `IsTotalTimeDerivativeVelocity`: Velocity-only case, equivalent to δL(dₜ q) = ⟨g, dₜ q⟩

## iv. References

* Landau & Lifshitz, "Mechanics", §2 (The principle of least action). [ref: landau_mechanics]
* Landau & Lifshitz, "Mechanics", §4 (The Lagrangian for a free particle). [ref: landau_mechanics]
-/

@[expose] public section

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

namespace ClassicalMechanics

open InnerProductSpace ContDiff Time ContinuousMultilinearMap

namespace Lagrangian
/-!

## A. General Total Time Derivative

-/

/-- A function δL(t, q, dₜ q) is a total time derivative if it can be written as d/dt F(r, t)
    for some function F that depends on position and time but not velocity,

δL(t, q, dₜ q) = (d/dt) F(t, q)

    This is the most general form of Lagrangian equivalence under total derivatives.
    The key point is that F must be independent of velocity. -/
def IsTotalTimeDerivative
    (δL : Time → X → X → ℝ) : Prop :=
    ∃ (F : Time → X → ℝ) (_ : ContDiff ℝ ∞ ↿F),
    ∀ t (q : Time → X), (ContDiff ℝ ∞ q) → δL t (q t) (∂ₜ q t) = ∂ₜ (fun t' => F t' (q t')) t

/--
    Explicit reformulation (by the chain rule):
    δL(t, q, dₜ q) = ∂F/∂t(t, q) + ⟨∇ᵣF(t, q), dₜ q⟩

    or

    δL(t, q, dₜ q) = fderiv ℝ F (t, q) (1, dₜ q)
-/
lemma isTotalTimeDerivative_explicit {δL : Time → X → X → ℝ} :
    IsTotalTimeDerivative δL ↔  (∃ (F : Time → X → ℝ) (_ : ContDiff ℝ ∞ ↿F),
    ∀ t q v, δL t q v = fderiv ℝ ↿F (t, q) ((1 : Time), v)) := by
  -- Preliminary construction: properties of the function t => (t, q t)
  let tq := fun (q : Time → X) t => (t, q t)
  have h_tq_contDiff : ∀ (q : Time → X), ContDiff ℝ ∞ q -> ContDiff ℝ ∞ (tq q) := by
    fun_prop
  have h_tq_der :  ∀ (q : Time → X) t, ContDiff ℝ ∞ q -> ∂ₜ (tq q) t = (1, ∂ₜ q t) := by
    intro q t h_ContDiff_q
    ext
    change (∂ₜ (tq q) t).1.val = (1 : Time).val
    congr
    apply Eq.symm
    calc
      (1 : Time) = fderiv ℝ (fun (t' : Time) => t') t 1 := by simp only [fderiv_fun_id,
        ContinuousLinearMap.coe_id', id_eq]
      _ = fderiv ℝ (fun (t' : Time) => (tq q t').1) t 1 := by rfl
      _ = (∂ₜ (tq q) t).1 := by
        rw [fderiv.fst]
        · simp
          rfl
        · apply ContDiffAt.differentiableAt
          · apply ContDiff.contDiffAt
            exact h_tq_contDiff q h_ContDiff_q
          · by_contra
            rcases this
    apply Eq.symm
    calc
       (1, ∂ₜ q t).2 = fderiv ℝ (fun t' => (tq q t').2) t 1 := by rfl
       _ = (∂ₜ (tq q) t).2 := by
        rw [fderiv.snd]
        · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']
          rfl
        · apply ContDiffAt.differentiableAt
          · apply ContDiff.contDiffAt
            exact h_tq_contDiff q h_ContDiff_q
          · by_contra
            rcases this
  have h_F_tq_der : ∀ (q : Time → X) (F : Time → X → ℝ) t, (ContDiff ℝ ∞ ↿F) → (ContDiff ℝ ∞ q)  →
      ∂ₜ (fun t' => ↿F (t', q t')) t = fderiv ℝ ↿F (t, q t) ((1 : Time), ∂ₜ q t) := by
    intro q F t hF hq
    change  fderiv ℝ ((↿F) ∘ (tq q)) t 1 = fderiv ℝ ↿F (t, q t) ((1 : Time), ∂ₜ q t)
    rw [fderiv_comp]
    · simp only [ContinuousLinearMap.comp_apply]
      rw [← Time.deriv_eq,h_tq_der]
      exact hq
    · apply ContDiffAt.differentiableAt
      · apply ContDiff.contDiffAt
        exact hF
      · by_contra
        rcases this
    · apply ContDiffAt.differentiableAt
      · apply ContDiff.contDiffAt
        exact h_tq_contDiff q hq
      · by_contra
        rcases this
  -- beginning of the proof
  constructor
  -- From total the total derivative to the explicit form
  · intro h
    rcases h with ⟨F, hF⟩
    rcases hF with ⟨hFdif, hFder⟩
    use F
    use hFdif
    intro t q₀ v
    let qv := fun (t' : Time) => (q₀ - t.val • v) + t'.val • v
    have h_qv_contDiff : ContDiff ℝ ∞ qv := by
      change ContDiff ℝ ∞ (((fun (tR : ℝ) => (q₀ - t.val • v) + tR • v)) ∘ Time.toRealCLE)
      fun_prop
    have h_qv_t : qv t = q₀ := by
      calc
        qv t = (q₀ - t.val • v) + t.val • v := by rfl
        _ = q₀ := by module
    have h_qv_der : ∂ₜ qv t = v := by
      calc
        ∂ₜ qv t = fderiv ℝ (fun t' => (q₀ - t.val • v) + t'.val • v) t 1 := by rfl
        _ = v := by
          rw [fderiv_const_add,fderiv_smul_const]
          · simp only [ContinuousLinearMap.smulRight_apply, fderiv_val, one_smul]
          · fun_prop
    rw [← h_qv_t, ← h_qv_der, hFder, ← h_F_tq_der]
    · rfl
    · exact hFdif
    · exact h_qv_contDiff
    · exact h_qv_contDiff
  -- From the explicit form to the total derivative
  · intro h
    rcases h with ⟨F, hF⟩
    rcases hF with ⟨hFdif, hFder⟩
    use F
    use hFdif
    intro t q hq_ContDiff
    rw [hFder, ← h_F_tq_der]
    · rfl
    · exact hFdif
    · exact hq_ContDiff

/--
Elementary fact: if δL is a time derivative, then so is -δL.
-/
lemma isTotalTimeDerivative_neg {δL : Time → X → X → ℝ} (h :  IsTotalTimeDerivative δL) :
    IsTotalTimeDerivative (- δL) := by
    rcases h with ⟨F, h_ContDiff, hF⟩
    set F_neg := (fun t q => - F t q)
    use F_neg
    have h_neg_F_ContDiff : ContDiff ℝ ∞ ↿F_neg := by
      fun_prop
    use  h_neg_F_ContDiff
    intro t q hq
    simp only [Pi.neg_apply]
    rw [hF t q hq]
    unfold F_neg
    unfold Time.deriv
    simp only [fderiv_fun_neg, _root_.neg_apply]

/--
If δL is a total time derivative (of a smooth function), then it is smooth
-/
lemma totalTimeDerivative_contDiff {δL : Time → X → X → ℝ} (h : IsTotalTimeDerivative δL):
    ContDiff ℝ ∞ ↿δL := by
 rcases isTotalTimeDerivative_explicit.mp h with ⟨F, hContDiff, heq⟩
 let Fder_v := Prod.map (fderiv ℝ ↿(fun t q => F t q)) (fun (v : X) => v )
 let regroup := ↿(fun (t : Time) (q : X) (v : X) => ((t, q), v))
 let appv := fun (FV : ((Time × X →L[ℝ] ℝ) × X )) => FV.fst (1, FV.snd)
 have hδL : ↿δL = appv ∘ Fder_v ∘ regroup := by
   funext tqv
   rcases tqv with ⟨t, q, v⟩
   simp only [Function.comp_apply]
   change δL t q v = appv (Fder_v (regroup (t, q, v)))
   rw [heq t q v]
   rfl
 rw [hδL]
 unfold appv
 unfold Fder_v
 unfold regroup
 fun_prop

/-!
## B. Total time derivative do not affect the physical content
  The total time derivative does not affect the Euler-Lagrange equations, because its variational
  derivative is zero:
  ∫d/dt F(t, q)= F(t₁,q₁) - F(t₀,q₀)
  is fixed by the boundary conditions.
-/


 /--
Total time derivative has a variational derivative, which is zero
 -/
lemma totalTimeDerivative_hasZeroVarGradient [CompleteSpace X] {δL : Time → X → X → ℝ}
    (h : IsTotalTimeDerivative δL) (q : Time → X) (hq : ContDiff ℝ ∞ q):
     HasVarGradientAt (fun q' t => δL t (q' t) (∂ₜ q' t)) (fun _ => 0) q := by
  rcases h with ⟨F,hF_contDiff, hF⟩
  let traj_deriv := fun (G : Time → ℝ) t => fderiv ℝ G t 1
  let F_traj := fun (q : Time → X) t => F t (q t)
  apply HasVarGradientAt.intro _
  · apply HasVarAdjDerivAt.congr (F := fun q' => traj_deriv (F_traj q'))
    · apply HasVarAdjDerivAt.comp (F := traj_deriv) (G := F_traj)
      · apply HasVarAdjDerivAt.fderiv
        fun_prop
      · apply HasVarAdjDerivAt.fmap (f := fun t => F t)
        · exact hq
        · fun_prop
        · intro t x
          apply DifferentiableAt.hasAdjFDerivAt
          apply Differentiable.differentiableAt
          apply ContDiff.differentiable
          fun_prop
          decide
    · intro q' hq'
      funext t'
      rw [hF t' q' hq']
      rfl
  funext t
  unfold adjFDeriv
  simp [adjoint_eq_clm_adjoint]

/--
If two lagrangians, L and L', differ by a total time derivative, and L has a variational derivative
grad, then so does L'.
 -/
lemma totalTimeDerivative_hasVarGradientAt_equivalence [CompleteSpace X] (L δL : Time → X → X → ℝ)
    (hδL : IsTotalTimeDerivative δL)
    (q : Time → X)    (hq : ContDiff ℝ ∞ q) (grad : Time → X)
    (hgrad :  HasVarGradientAt (fun q' t => L t (q' t) (fderiv ℝ  q' t 1)) grad q) :
    HasVarGradientAt (fun q' t => (L + δL) t (q' t) (fderiv ℝ q' t 1)) grad q := by
  have h_add_zero : grad = grad + (fun _ => 0) := by
    funext t
    simp
  rw [h_add_zero]
  apply HasVarGradientAt.add
  · exact hgrad
  · exact totalTimeDerivative_hasZeroVarGradient hδL q hq


/-
Reformulation of the previous result:
If two lagrangians, L and L', differ by a total time derivative, their variational time derivatives
coincide (or neither of them has a variational derivative).
-/
lemma totalTimeDerivative_varGradient_equivalenvce [CompleteSpace X] (L L' : Time → X → X → ℝ)
    (htot : IsTotalTimeDerivative (L' - L))
    (q : Time → X) (hq : ContDiff ℝ ∞ q):
    (δ (q':=q), ∫ t, L' t (q' t) (fderiv ℝ q' t 1)) =
       (δ (q':=q), ∫ t, L t (q' t) (fderiv ℝ q' t 1)) := by
  let δL := (fun t q v => L' t q v - L t q v)
  by_cases hL : ∃ grad, HasVarGradientAt (fun q' t => L t (q' t) (fderiv ℝ q' t 1)) grad q
  · apply HasVarGradientAt.varGradient
    have h_triv : L' = L + (L' - L) := by module
    rw [h_triv]
    apply totalTimeDerivative_hasVarGradientAt_equivalence
    · exact htot
    · exact hq
    · rcases hL with ⟨grad, hgrad⟩
      rw [ HasVarGradientAt.varGradient (fun q' t => L t (q' t) (fderiv ℝ  q' t 1)) grad q hgrad]
      exact hgrad
  · by_cases hL' : ∃ grad, HasVarGradientAt (fun q' t => L' t (q' t) (fderiv ℝ q' t 1)) grad q
    · apply Eq.symm
      apply HasVarGradientAt.varGradient
      have h_triv : L = L' +(-(L' - L)) := by module
      rw [h_triv]
      apply totalTimeDerivative_hasVarGradientAt_equivalence
      · apply isTotalTimeDerivative_neg
        exact htot
      · exact hq
      · rcases hL' with ⟨grad, hgrad⟩
        rw [HasVarGradientAt.varGradient (fun q' t => L' t (q' t) (fderiv ℝ  q' t 1)) grad q hgrad]
        exact hgrad
    · unfold varGradient
      simp only [hL, hL', ↓reduceDIte]

/--
Corollary: If L and L' differ by a total time derivative, then the corresponding Euler-Lagrange
operators coincide
-/
lemma totalTimeDerivative_eulerLagrange_equivalenvce [CompleteSpace X] (L L' : Time → X → X → ℝ)
    (htot : IsTotalTimeDerivative (L' - L)) (hContDiff : (ContDiff ℝ ∞ ↿L) ∨ (ContDiff ℝ ∞ ↿L'))
    (q : Time → X) (hq : ContDiff ℝ ∞ q) : eulerLagrangeOp L q = eulerLagrangeOp L' q := by
  rcases (isTotalTimeDerivative_explicit.mp htot) with ⟨F, hFContDiff, hEq⟩
  have hContDiff_both :  (ContDiff ℝ ∞ ↿L) ∧ (ContDiff ℝ ∞ ↿L') := by
    cases hContDiff with
      | inl hL =>
        constructor
        · exact hL
        · have h_triv : ↿L' =  ↿L + ↿(L' - L) := by
            funext tqv
            rcases tqv with ⟨t, q', v⟩
            rw [Pi.add_apply]
            change L' t q' v = L t q' v + (L' - L) t q' v
            simp
          have h_δL_contDiff := totalTimeDerivative_contDiff htot
          rw [h_triv]
          exact hL.add h_δL_contDiff
      | inr hL' =>
        constructor
        · have h_triv : ↿L =  ↿L' + ↿(-(L' - L)) := by
            funext tqv
            rcases tqv with ⟨t, q', v⟩
            rw [Pi.add_apply]
            change L t q' v = L' t q' v + (- (L' - L)) t q' v
            simp
          have h_δL_contDiff := totalTimeDerivative_contDiff (isTotalTimeDerivative_neg htot)
          rw [h_triv]
          exact hL'.add h_δL_contDiff
        · exact hL'
  rw [← euler_lagrange_varGradient L q hq hContDiff_both.left]
  rw [← euler_lagrange_varGradient L' q hq hContDiff_both.right]
  apply Eq.symm
  apply totalTimeDerivative_varGradient_equivalenvce
  · exact htot
  · exact hq

/-!

## C. Velocity-Only Total Time Derivative

When δL depends only on velocity (the free particle case), the condition simplifies.

-/

/-- A velocity-only function that is a total time derivative must be linear in velocity.

    If δL depends only on velocity and equals d/dt F(t, q) for some F,
    then δL(dₜ q) = ⟨g, dₜ q⟩ for some constant vector g.

    This characterization comes from the requirement that:
    - d/dt F(t, q) = ∂F/∂t + ⟨∇F, dₜ q⟩ = ∂F/∂t + ⟨∇F, dₜ q⟩
    - For the result to be independent of q and t, we need ∇F = g (constant) and ∂F/∂t = 0
    - Thus δL(dₜ q) = ⟨g, dₜ q⟩

    WLOG, we assume `δL 0 = 0` since constants are total derivatives (c = d/dt(c·t))
    and can be absorbed without affecting the equations of motion. -/
lemma isTotalTimeDerivativeVelocity  [CompleteSpace X]
    (δL : X → ℝ)
    (hδL0 : δL 0 = 0)
    (h : IsTotalTimeDerivative (fun _ _ v => δL v)) :
    ∃ g : X, ∀ v, δL v = ⟪g, v⟫_ℝ := by
  classical
  rcases (isTotalTimeDerivative_explicit.mp h) with ⟨F, hFdiff, hEq⟩

  -- Derivative of F at (0,0)
  let dF : (Time  × X) →L[ℝ] ℝ :=
    fderiv ℝ ↿F ((0 : Time), (0 : X))

  -- The "time-direction" derivative must vanish because δL 0 = 0.
  have h_time : dF ((1 : Time), (0 : X)) = 0 := by
    have h0 :
        δL (0 : X) =
          fderiv ℝ ↿F ((0 : Time), (0 : X))
            ((1 : Time), (0 : X)) := by
      simpa using (hEq (0 : Time) (0 : X)
        (0 : X))
    have : dF ((1 : Time), (0 : X)) =
        δL (0 : X) := by
      simpa [dF] using h0.symm
    simpa [hδL0] using this

  -- Induced continuous linear functional on velocity: v ↦ dF (0,v).
  let φ : X →L[ℝ] ℝ :=
    dF.comp (ContinuousLinearMap.inr ℝ Time X)

  -- Show δL v = φ v for all v.
  have hφ : ∀ v : X, δL v = φ v := by
    intro v
    have hv :
        δL v =
          fderiv ℝ ↿F ((0 : Time), (0 : X))
            ((1 : Time), v) := by
      simpa using (hEq (0 : Time) (0 : X) v)
    have hv' : δL v = dF ((1 : Time), v) := by
      simpa [dF] using hv
    calc
      δL v = dF ((1 : Time), v) := hv'
     _ = dF (((0  : Time), v) + ((1 : Time), (0 : X))) := by simp only [Prod.mk_add_mk, zero_add,
        add_zero]
      _ = dF ((0 : Time), v) + dF ((1 : Time), (0 : X)) := by
        simpa using
          (dF.map_add ((0 : Time), v) ((1 : Time), (0 : X)))
      _ = dF ((0 : Time), v) := by
        simp [h_time]
      _ = φ v := by
        simp [φ]

  -- Frechet–Riesz: represent φ as inner product with some g.
  refine ⟨(InnerProductSpace.toDual ℝ (X)).symm φ, ?_⟩
  intro v
  have hinner :
      ⟪(InnerProductSpace.toDual ℝ (X)).symm φ, v⟫_ℝ = φ v := by
    rw [InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
        (E := X) (x := v) (y := φ)]
  calc
    δL v = φ v := hφ v
    _ = ⟪(InnerProductSpace.toDual ℝ (X)).symm φ, v⟫_ℝ := by
      rw [hinner.symm]

end Lagrangian

end ClassicalMechanics
