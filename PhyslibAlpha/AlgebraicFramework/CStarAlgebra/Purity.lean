/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.Uncertainty
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.State.Pure
public import PhyslibAlpha.QuantumMechanics.QuadraticSystem.Weyl.StoneVonNeumann.Regularity
public import PhyslibAlpha.QuantumMechanics.QuadraticSystem.Weyl.StoneVonNeumann.Irreducible
public import Mathlib.Algebra.Module.Submodule.Invariant

/-!

# Pure states have irreducible GNS representations

The general C⋆-algebra fact behind `Quasifree.lean`'s remaining purity gap, proved here
independently of anything Gaussian: **a pure state's GNS representation has no nontrivial reducing
subspace.** Combined with a Gaussian-specific fact — a quasifree state with positive-definite
covariance is pure — not attempted here, this would close `Quasifree.lean`'s gap; this file closes
the general half.

## The argument

Given a nontrivial reducing subspace `K` (`K` and `Kᗮ` both invariant under every `π_ω(a)`,
`K ≠ ⊥, ⊤`), let `P` be the orthogonal projection onto `K`. `P` commutes with every `π_ω(a)`
(standard idempotent/invariant-subspace fact). Cyclicity of `Ω := Ω_ω` forces `PΩ ≠ 0` and
`(1-P)Ω ≠ 0` (otherwise `P`, resp. `1-P`, would vanish on the dense orbit `π_ω(A)Ω`, forcing it to
be `0` everywhere by continuity — contradicting `K ≠ ⊥`, resp. `K ≠ ⊤`). Set `t := ‖PΩ‖² ∈ (0,1)`.
The two vector functionals `ω₁(a) := ⟪PΩ, π_ω(a)PΩ⟫/t`, `ω₂(a) := ⟪(1-P)Ω, π_ω(a)(1-P)Ω⟫/(1-t)`
are genuine states (`UnitalPositiveLinearMap.ofLinearMap`, positivity via `CFC.sqrt`), and satisfy
`ω = t•ω₁ + (1-t)•ω₂` (a direct computation using that `P` commutes with every `π_ω(a)`).

Purity of `ω` then forces `ω₁ = ω₂`, hence `ω = ω₁` (substituting back). The key remaining step —
**`ω = ω₁` forces `P` itself to be an isometry up to the scalar `√t`** — follows from comparing the
GNS-exact inner product identity `⟪π_ω(a)Ω, π_ω(a)Ω⟫ = ω(star a * a)` against
`⟪π_ω(a)PΩ, π_ω(a)PΩ⟫ = t·ω₁(star a * a)` (using that `P` commutes with `π_ω(a)`) and `ω = ω₁`:
this gives `‖P(π_ω(a)Ω)‖ = √t · ‖π_ω(a)Ω‖` on the dense orbit `π_ω(A)Ω`, hence (both sides
continuous) `‖Pξ‖ = √t‖ξ‖` for *every* `ξ : ω.GNS`. But `K ≠ ⊤` gives a nonzero `ξ ∈ Kᗮ`, for which
`Pξ = 0`, forcing `√t = 0` — contradicting `t > 0`.

## Main definitions

- `UnitalPositiveLinearMap.IsPure` : a state that is not a nontrivial convex combination of two
  (necessarily equal, hence equal to it) states.
- `UnitalPositiveLinearMap.IsPure.reducing_eq_bot_or_top` : the general fact — proved above.
- `WeylFamily.IsPure.gnsRep_irreducible` : the Weyl-specific corollary, replacing
  `Quasifree.lean`'s old (false) unconditional claim: a *generating* Weyl family's GNS
  representation at a pure state is irreducible.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace UnitalPositiveLinearMap

/- `UnitalPositiveLinearMap.IsPure` (extreme point of the convex state space,
`OrderUnit/State/Pure.lean`) already gives exactly the property this file needs:
`IsPure.eq_of_mix` says a genuine binary mixture equal to a pure state repeats it at both
endpoints. -/

variable (ω : 𝓢[A])

/-- The vector-state functional `a ↦ ⟪ξ, π_ω(a) ξ⟫` is `ℂ`-linear in `a`, for any fixed `ξ`. -/
noncomputable def vectorFunctionalLM (ξ : ω.GNS) : A →ₗ[ℂ] ℂ where
  toFun a := ⟪ξ, ω.gnsRep a ξ⟫_ℂ
  map_add' a b := by simp [map_add, inner_add_right]
  map_smul' c a := by simp [map_smul, inner_smul_right]

/-- The vector-state functional is positive: `a ≥ 0` forces `⟪ξ, π_ω(a)ξ⟫ ≥ 0`, via writing
`a = star b * b` (`CFC.sqrt`) and reducing to `‖π_ω(b)ξ‖² ≥ 0`. -/
theorem vectorFunctionalLM_nonneg (ξ : ω.GNS) {a : A} (ha : 0 ≤ a) :
    0 ≤ vectorFunctionalLM ω ξ a := by
  set b : A := CFC.sqrt a with hb_def
  have hb_sa : IsSelfAdjoint b := .of_nonneg (CFC.sqrt_nonneg a)
  have hab : a = star b * b := by rw [hb_sa.star_eq]; exact (CFC.sqrt_mul_sqrt_self a ha).symm
  show 0 ≤ ⟪ξ, ω.gnsRep a ξ⟫_ℂ
  rw [hab, map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  positivity

/-- The vector-state functional built from a unit vector is unital. -/
theorem vectorFunctionalLM_one {ξ : ω.GNS} (hξ : ‖ξ‖ = 1) :
    vectorFunctionalLM ω ξ 1 = 1 := by
  show ⟪ξ, ω.gnsRep 1 ξ⟫_ℂ = 1
  rw [map_one, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hξ]
  norm_num

/-- The vector-state functional built from a *nonzero* vector `ξ`, normalized by `‖ξ‖²`: a genuine
state. -/
noncomputable def vectorState {ξ : ω.GNS} (hξ : ξ ≠ 0) : 𝓢[A] :=
  UnitalPositiveLinearMap.ofLinearMap
    (((‖ξ‖ ^ 2 : ℝ) : ℂ)⁻¹ • vectorFunctionalLM ω ξ)
    (fun a ha => by
      have hpos : 0 ≤ vectorFunctionalLM ω ξ a := vectorFunctionalLM_nonneg ω ξ ha
      have hinv : (0:ℝ) ≤ (‖ξ‖ ^ 2 : ℝ)⁻¹ := by positivity
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by exact_mod_cast hinv : (0:ℂ) ≤ ((‖ξ‖ ^ 2 : ℝ)⁻¹ : ℂ)) hpos)
    (by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      show ((‖ξ‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪ξ, ω.gnsRep 1 ξ⟫_ℂ = 1
      have hne : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hξ
      rw [map_one, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K]
      field_simp
      norm_cast)

@[simp]
theorem vectorState_apply {ξ : ω.GNS} (hξ : ξ ≠ 0) (a : A) :
    ω.vectorState hξ a = ((‖ξ‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪ξ, ω.gnsRep a ξ⟫_ℂ := by
  show (((‖ξ‖ ^ 2 : ℝ) : ℂ)⁻¹ • vectorFunctionalLM ω ξ) a = _
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rfl

/-- The general `*`-representation identity `⟪π(b)ξ, π(b)ξ⟫ = ⟪ξ, π(star b * b)ξ⟫`, for *any*
vector `ξ` (not just the cyclic vector) — the adjoint identity underlying both positivity of
vector functionals and the main theorem below. -/
theorem inner_gnsRep_self_eq (ξ : ω.GNS) (b : A) :
    ⟪ξ, ω.gnsRep (star b * b) ξ⟫_ℂ = ⟪ω.gnsRep b ξ, ω.gnsRep b ξ⟫_ℂ := by
  rw [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- **A pure state's GNS representation has no nontrivial reducing subspace.** See the file
docstring for the full argument. `K` reducing means both `K` and `Kᗮ` are invariant under every
`π_ω(a)`, `a : A` (not merely the generators of some sub-family — this is the genuinely stronger,
whole-algebra notion a general C⋆-algebra argument needs). -/
theorem IsPure.reducing_eq_bot_or_top (hpure : ω.IsPure) (K : Submodule ℂ ω.GNS)
    (hK_inv : ∀ a : A, ∀ ξ ∈ K, ω.gnsRep a ξ ∈ K)
    (hKperp_inv : ∀ a : A, ∀ ξ ∈ Kᗮ, ω.gnsRep a ξ ∈ Kᗮ)
    [K.HasOrthogonalProjection] :
    K = ⊥ ∨ K = ⊤ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hbot, htop⟩ := hcon
  set P : ω.GNS →L[ℂ] ω.GNS := K.starProjection with hP_def
  have hP_idem : IsIdempotentElem P := K.isIdempotentElem_starProjection
  have hP_range : P.range = K := Submodule.range_starProjection K
  have hP_ker : P.ker = Kᗮ := Submodule.ker_starProjection K
  have h_commute : ∀ a : A, Commute P (ω.gnsRep a) := by
    intro a
    rw [ContinuousLinearMap.IsIdempotentElem.commute_iff hP_idem, hP_range, hP_ker]
    exact ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ω.gnsRep a).toLinearMap).mpr
        (hK_inv a),
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ω.gnsRep a).toLinearMap).mpr
        (hKperp_inv a)⟩
  have h_commute' : ∀ a : A, Commute (1 - P) (ω.gnsRep a) :=
    fun a => (Commute.one_left (ω.gnsRep a)).sub_left (h_commute a)
  set Ω : ω.GNS := ω.gnsCyclicVector with hΩ_def
  have hcyc : DenseRange (fun a : A => ω.gnsRep a Ω) := ω.denseRange_gnsRep_gnsCyclicVector
  -- `PΩ ≠ 0` and `(1-P)Ω ≠ 0`: otherwise `P`, resp. `1-P`, vanishes on the dense orbit `π_ω(A)Ω`,
  -- forcing it to be `0` everywhere, contradicting `K ≠ ⊥`, resp. `K ≠ ⊤`.
  have hPΩ_ne : P Ω ≠ 0 := by
    intro hz
    apply hbot
    rw [← hP_range]
    have heq : ((P : ω.GNS → ω.GNS)) ∘ (fun a : A => ω.gnsRep a Ω) =
        ((0 : ω.GNS →L[ℂ] ω.GNS) : ω.GNS → ω.GNS) ∘ (fun a : A => ω.gnsRep a Ω) := by
      funext a
      show P (ω.gnsRep a Ω) = 0
      rw [← ContinuousLinearMap.mul_apply, (h_commute a).eq, ContinuousLinearMap.mul_apply, hz,
        map_zero]
    have hPzero : P = 0 :=
      ContinuousLinearMap.ext (congrFun (hcyc.equalizer P.continuous continuous_const heq))
    rw [hPzero]
    exact LinearMap.range_eq_bot.mpr rfl
  have hQΩ_ne : (1 - P) Ω ≠ 0 := by
    intro hz
    apply htop
    have heq : (((1 : ω.GNS →L[ℂ] ω.GNS) - P : ω.GNS →L[ℂ] ω.GNS) : ω.GNS → ω.GNS) ∘
        (fun a : A => ω.gnsRep a Ω) =
        ((0 : ω.GNS →L[ℂ] ω.GNS) : ω.GNS → ω.GNS) ∘ (fun a : A => ω.gnsRep a Ω) := by
      funext a
      show (1 - P) (ω.gnsRep a Ω) = 0
      rw [← ContinuousLinearMap.mul_apply, (h_commute' a).eq, ContinuousLinearMap.mul_apply, hz,
        map_zero]
    have hQzero : (1 : ω.GNS →L[ℂ] ω.GNS) - P = 0 :=
      ContinuousLinearMap.ext
        (congrFun (hcyc.equalizer (1 - P).continuous continuous_const heq))
    have hPone : P = 1 := (sub_eq_zero.mp hQzero).symm
    rw [← hP_range, hPone]
    exact LinearMap.range_eq_top.mpr Function.surjective_id
  -- `t := ‖PΩ‖² ∈ (0,1)`, via the Pythagorean identity `‖PΩ‖² + ‖(1-P)Ω‖² = ‖Ω‖² = 1`
  -- (`P`, `1-P` complementary orthogonal projections, cross term vanishes by self-adjointness).
  have hP_sa : IsSelfAdjoint P := isSelfAdjoint_starProjection K
  have hPP : P (P Ω) = P Ω := by
    have := congrArg (fun T : ω.GNS →L[ℂ] ω.GNS => T Ω) hP_idem
    simpa [ContinuousLinearMap.mul_apply] using this
  have hcross : ⟪P Ω, (1 - P) Ω⟫_ℂ = 0 := by
    have hadjP : ⟪P Ω, (1 - P) Ω⟫_ℂ = ⟪(ContinuousLinearMap.adjoint P) Ω, (1 - P) Ω⟫_ℂ := by
      rw [← ContinuousLinearMap.star_eq_adjoint, hP_sa.star_eq]
    rw [hadjP, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, map_sub, hPP, sub_self, inner_zero_right]
  have hpyth : (‖P Ω‖ : ℝ) ^ 2 + ‖(1 - P) Ω‖ ^ 2 = 1 := by
    have hΩsplit : Ω = P Ω + (1 - P) Ω := by simp
    have hns := norm_add_sq (𝕜 := ℂ) (P Ω) ((1 - P) Ω)
    rw [hcross] at hns
    simp only [RCLike.zero_re, mul_zero] at hns
    rw [← hΩsplit] at hns
    have hΩnorm : ‖Ω‖ = 1 := ω.norm_gnsCyclicVector
    rw [hΩnorm] at hns
    linarith [hns]
  set t : ℝ := ‖P Ω‖ ^ 2 with ht_def
  have ht_pos : 0 < t := by rw [ht_def]; positivity
  have ht_lt_one : t < 1 := by
    have hQpos : 0 < ‖(1 - P) Ω‖ ^ 2 := by positivity
    linarith [hpyth]
  -- The two vector states, and the decomposition identity.
  set ω₁ : 𝓢[A] := ω.vectorState hPΩ_ne with hω₁_def
  set ω₂ : 𝓢[A] := ω.vectorState hQΩ_ne with hω₂_def
  have hPa : ∀ a : A, P (ω.gnsRep a Ω) = ω.gnsRep a (P Ω) := by
    intro a
    rw [← ContinuousLinearMap.mul_apply, (h_commute a).eq, ContinuousLinearMap.mul_apply]
  have hQa : ∀ a : A, (1 - P) (ω.gnsRep a Ω) = ω.gnsRep a ((1 - P) Ω) := by
    intro a
    rw [← ContinuousLinearMap.mul_apply, (h_commute' a).eq, ContinuousLinearMap.mul_apply]
  have hdecomp : ∀ a : A, ω a = (t : ℂ) * ω₁ a + ((1 : ℝ) - t : ℝ) * ω₂ a := by
    intro a
    rw [hω₁_def, hω₂_def, vectorState_apply, vectorState_apply]
    have h1 : (t : ℂ) * (((‖P Ω‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪P Ω, ω.gnsRep a (P Ω)⟫_ℂ) =
        ⟪P Ω, ω.gnsRep a (P Ω)⟫_ℂ := by
      rw [ht_def]
      have hne : ((‖P Ω‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (‖P Ω‖ ^ 2 : ℝ) ≠ 0)
      field_simp
    have h2 : (((1 : ℝ) - t : ℝ) : ℂ) *
        (((‖(1 - P) Ω‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪(1 - P) Ω, ω.gnsRep a ((1 - P) Ω)⟫_ℂ) =
        ⟪(1 - P) Ω, ω.gnsRep a ((1 - P) Ω)⟫_ℂ := by
      have hval : ((1:ℝ) - t) = ‖(1 - P) Ω‖ ^ 2 := by linarith [hpyth]
      rw [hval]
      have hne : ((‖(1 - P) Ω‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (‖(1 - P) Ω‖ ^ 2 : ℝ) ≠ 0)
      field_simp
    rw [h1, h2]
    have e1 : ⟪P Ω, ω.gnsRep a (P Ω)⟫_ℂ = ⟪Ω, ω.gnsRep a (P Ω)⟫_ℂ := by
      have step1 : ⟪P Ω, ω.gnsRep a (P Ω)⟫_ℂ =
          ⟪(ContinuousLinearMap.adjoint P) Ω, ω.gnsRep a (P Ω)⟫_ℂ := by
        rw [← ContinuousLinearMap.star_eq_adjoint, hP_sa.star_eq]
      rw [step1, ContinuousLinearMap.adjoint_inner_left]
      congr 1
      rw [← ContinuousLinearMap.mul_apply, (h_commute a).eq, ContinuousLinearMap.mul_apply, hPP]
    have hQ_sa : IsSelfAdjoint (1 - P : ω.GNS →L[ℂ] ω.GNS) :=
      (IsSelfAdjoint.one (ω.GNS →L[ℂ] ω.GNS)).sub hP_sa
    have hQQ : (1 - P) ((1 - P) Ω) = (1 - P) Ω := by
      have hidemQ : (1 - P) * (1 - P) = (1 - P : ω.GNS →L[ℂ] ω.GNS) := by
        have hexp : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        rw [hexp, hP_idem]; abel
      have := congrArg (fun T : ω.GNS →L[ℂ] ω.GNS => T Ω) hidemQ
      simpa [ContinuousLinearMap.mul_apply] using this
    have e2 : ⟪(1 - P) Ω, ω.gnsRep a ((1 - P) Ω)⟫_ℂ = ⟪Ω, ω.gnsRep a ((1 - P) Ω)⟫_ℂ := by
      have step1 : ⟪(1 - P) Ω, ω.gnsRep a ((1 - P) Ω)⟫_ℂ =
          ⟪(ContinuousLinearMap.adjoint (1 - P)) Ω, ω.gnsRep a ((1 - P) Ω)⟫_ℂ := by
        rw [← ContinuousLinearMap.star_eq_adjoint, hQ_sa.star_eq]
      rw [step1, ContinuousLinearMap.adjoint_inner_left]
      congr 1
      rw [← ContinuousLinearMap.mul_apply, (h_commute' a).eq, ContinuousLinearMap.mul_apply, hQQ]
    rw [e1, e2, ← inner_add_right]
    have : ω.gnsRep a (P Ω) + ω.gnsRep a ((1 - P) Ω) = ω.gnsRep a Ω := by
      rw [← map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      congr 1
      abel
    rw [this, ω.inner_gnsCyclicVector_gnsRep_gnsCyclicVector]
  -- Purity gives `ω₁ = ω`, via the genuine binary-mixture characterization
  -- (`UnitalPositiveLinearMap.IsPure`, `OrderUnit/State/Pure.lean`).
  have ht_ui : t ∈ unitInterval := ⟨ht_pos.le, ht_lt_one.le⟩
  set t_ui : unitInterval := ⟨t, ht_ui⟩ with ht_ui_def
  have hmix : mix ω₁ ω₂ t_ui = ω := by
    apply UnitalPositiveLinearMap.ext
    intro a
    rw [mix_apply, hdecomp a]
    simp [RCLike.real_smul_eq_coe_mul, ht_ui_def]
  have ht0 : t_ui ≠ 0 := by
    intro h
    have := congrArg (Subtype.val) h
    simp only [ht_ui_def] at this
    norm_num at this
    linarith [ht_pos]
  have ht1 : t_ui ≠ 1 := by
    intro h
    have := congrArg (Subtype.val) h
    simp only [ht_ui_def] at this
    norm_num at this
    linarith [ht_lt_one]
  have hωω1 : ∀ a : A, ω a = ω₁ a := by
    intro a
    rw [(hpure.eq_of_mix t_ui ht0 ht1 hmix).1]
  -- Every `π_ω(b)Ω`-generator satisfies `‖P(π_ω(b)Ω)‖² = t·‖π_ω(b)Ω‖²` (using `ω = ω₁`),
  -- extending by density and continuity to `‖Pξ‖² = t‖ξ‖²` for *every* `ξ`.
  have hgen : ∀ b : A, ‖P (ω.gnsRep b Ω)‖ ^ 2 = t * ‖ω.gnsRep b Ω‖ ^ 2 := by
    intro b
    rw [hPa b]
    have hL : ‖ω.gnsRep b (P Ω)‖ ^ 2 = (⟪ω.gnsRep b (P Ω), ω.gnsRep b (P Ω)⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have hR : ‖ω.gnsRep b Ω‖ ^ 2 = (⟪ω.gnsRep b Ω, ω.gnsRep b Ω⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [hL, hR, ← inner_gnsRep_self_eq, ← inner_gnsRep_self_eq]
    have : ⟪P Ω, ω.gnsRep (star b * b) (P Ω)⟫_ℂ = t * ⟪Ω, ω.gnsRep (star b * b) Ω⟫_ℂ := by
      have e1 : ⟪P Ω, ω.gnsRep (star b * b) (P Ω)⟫_ℂ = (t : ℂ) * ω₁ (star b * b) := by
        rw [hω₁_def, vectorState_apply]
        have hne : ((‖P Ω‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (by positivity : (‖P Ω‖ ^ 2 : ℝ) ≠ 0)
        rw [ht_def]; field_simp
      rw [e1, ← hωω1, ω.inner_gnsCyclicVector_gnsRep_gnsCyclicVector]
    rw [this, Complex.mul_re]
    have himZero : (⟪Ω, ω.gnsRep (star b * b) Ω⟫_ℂ).im = 0 := by
      rw [ω.inner_gnsCyclicVector_gnsRep_gnsCyclicVector]
      have hnn := vectorFunctionalLM_nonneg ω Ω (star_mul_self_nonneg b)
      rw [show vectorFunctionalLM ω Ω (star b * b) = ω (star b * b) from
        ω.inner_gnsCyclicVector_gnsRep_gnsCyclicVector _] at hnn
      exact (Complex.le_def.mp hnn).2.symm
    rw [himZero, Complex.ofReal_re]
    ring
  have hcont1 : Continuous (fun ξ : ω.GNS => ‖P ξ‖ ^ 2) := (P.continuous.norm).pow 2
  have hcont2 : Continuous (fun ξ : ω.GNS => t * ‖ξ‖ ^ 2) :=
    continuous_const.mul (continuous_norm.pow 2)
  have hall : ∀ ξ : ω.GNS, ‖P ξ‖ ^ 2 = t * ‖ξ‖ ^ 2 :=
    congrFun (hcyc.equalizer hcont1 hcont2 (funext hgen))
  -- Apply at `ξ₀ := (1-P)Ω`: `P ξ₀ = 0` (idempotence), so `t · ‖ξ₀‖² = 0`, contradicting `t > 0`.
  have hcontra := hall ((1 - P) Ω)
  have hPξ0 : P ((1 - P) Ω) = 0 := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub, hPP, sub_self]
  rw [hPξ0, norm_zero] at hcontra
  simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at hcontra
  have hQnorm_pos : 0 < ‖(1 - P) Ω‖ ^ 2 := by positivity
  nlinarith [hcontra.symm, ht_pos, hQnorm_pos]

end UnitalPositiveLinearMap

/-! ## The Weyl-specific corollary -/

namespace QuantumMechanics
namespace WeylFamily

variable {ℏ : ℝ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **A generating Weyl family's GNS representation at a pure state is irreducible.** Replaces
`Quasifree.lean`'s old, unconditionally-false `gnsRep_irreducible` claim: purity alone (not merely
positive-definiteness of a Gaussian covariance) is exactly the right hypothesis, and it is proved
in general above, independently of anything Gaussian. The remaining gap for a genuinely complete
`Quasifree.lean` fix is the Gaussian-specific half: a quasifree state with positive-definite
covariance is pure — a separate, real fact not attempted here.

The two pieces of this proof: (1) `IsIrreducible`'s hypothesis only gives invariance of `K` under
the *generators* `X.weyl v`, not all of `π_ω(A)` — `gnsRep_mem_of_mem_generatedSubalgebra`
(`Regularity.lean`) extends it, using `hgen`. (2) that same hypothesis, quantified over *every*
`v` (hence also `-v`), gives invariance of `Kᗮ` too via the standard unitary-adjoint trick
(`star_weyl` + `ContinuousLinearMap.orthogonal_mem_invtSubmodule`) — exactly as in
`Irreducible.lean`'s own backward direction — so `K` is a genuine *reducing* subspace for the whole
algebra, and `UnitalPositiveLinearMap.IsPure.reducing_eq_bot_or_top` applies directly. -/
theorem IsPure.gnsRep_irreducible {σ : LinearMap.BilinForm ℝ V} {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {X : WeylFamily ℏ σ A} {ω : 𝓢[A]} (hpure : ω.IsPure)
    (hgen : X.IsGenerating) :
    (X.gnsWeylFamily ω).IsIrreducible := by
  intro K hK_inv hK_closed
  set Y := X.gnsWeylFamily ω with hY_def
  have hK_inv_gen : ∀ a ∈ X.generatedSubalgebra, ∀ ξ ∈ K, ω.gnsRep a ξ ∈ K :=
    gnsRep_mem_of_mem_generatedSubalgebra hK_inv hK_closed
  have hKperp_inv_gen : ∀ v : V, ∀ ξ ∈ Kᗮ, (Y.weyl v : ω.GNS →L[ℂ] ω.GNS) ξ ∈ Kᗮ := by
    intro v
    have hK_adj_invt : K ∈ Module.End.invtSubmodule
        (ContinuousLinearMap.adjoint (Y.weyl v : ω.GNS →L[ℂ] ω.GNS)).toLinearMap := by
      rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
      intro x hx
      show (ContinuousLinearMap.adjoint (Y.weyl v : ω.GNS →L[ℂ] ω.GNS)) x ∈ K
      rw [← ContinuousLinearMap.star_eq_adjoint, Y.star_weyl v, ContinuousLinearMap.smul_apply]
      exact K.smul_mem _ (hK_inv (-v) x hx)
    have hKperp := ContinuousLinearMap.orthogonal_mem_invtSubmodule hK_adj_invt
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
      (Y.weyl v : ω.GNS →L[ℂ] ω.GNS).toLinearMap).mp hKperp
  have hKperp_inv : ∀ a ∈ X.generatedSubalgebra, ∀ ξ ∈ Kᗮ, ω.gnsRep a ξ ∈ Kᗮ :=
    gnsRep_mem_of_mem_generatedSubalgebra hKperp_inv_gen (Submodule.isClosed_orthogonal K)
  refine UnitalPositiveLinearMap.IsPure.reducing_eq_bot_or_top ω hpure K
    (fun a ξ hξ => hK_inv_gen a ?_ ξ hξ) (fun a ξ hξ => hKperp_inv a ?_ ξ hξ) <;>
    rw [hgen] <;> exact StarSubalgebra.mem_top

end WeylFamily
