/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.InnerProductSpace.PseudoInner
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Index of a pseudo-inner product, and stability of the signature

The index is `QuadraticForm.sigNeg` of the associated quadratic form: the largest dimension of a
subspace on which the form is negative definite. Index `0` is the Riemannian case, index `1` the
Lorentzian one.

`ContinuousLinearMap.eventually_sigNeg_eq` shows the signature cannot jump, which is what makes
local constancy of the index of a pseudo-Riemannian metric a theorem rather than a hypothesis.
The argument is classical: maximal definite subspaces for `b` stay definite for nearby `c`, so
`sigPos` and `sigNeg` can only grow, while `QuadraticForm.sigPos_add_sigNeg_add_radical` caps
their sum. No symmetry is used.

## Main definitions

* `PseudoInnerProductSpace.index` and `coindex`: the negative and positive inertia.

## Main results

* `QuadraticForm.sigNeg_eq_of_negDef_of_posDef`: a splitting into a negative definite and a
  positive definite part of complementary dimensions determines the whole signature.
* `ContinuousLinearMap.eventually_forall_pos`, `eventually_forall_neg`: definiteness on a fixed
  subspace is an open condition on the form. `IsCoercive.of_posDef` is the unrestricted case.
* `ContinuousLinearMap.eventually_sigNeg_eq`: `sigPos`, `sigNeg` and triviality of the radical are
  locally constant.
* `PseudoInnerProductSpace.index_eq_of_negDef_of_posDef` and `coindex_eq_of_negDef_of_posDef`
  compute them from a splitting; `index_eq_zero_iff_posDef`, `index_dual_eq` and
  `index_eq_zero_of_innerProductSpace` identify the Riemannian case.

## Tags

signature, index, inertia, Sylvester, nondegenerate, locally constant
-/

@[expose] public section

open Filter Module Metric Set QuadraticMap
open scoped Topology

/-! ## Determining a signature from a splitting

`sigPos` and `sigNeg` are defined as maxima, so mathlib's API bounds them from below. For a
nondegenerate form the two bounds are complementary, which pins both down. -/

namespace QuadraticForm

variable {𝕜 M : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [FiniteDimensional 𝕜 M] {Q : QuadraticForm 𝕜 M}
  {V W : Submodule 𝕜 M}

lemma sigPos_add_sigNeg_of_radical_eq_bot (hrad : Q.radical = ⊥) :
    sigPos Q + sigNeg Q = finrank 𝕜 M := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  rwa [hrad, finrank_bot, Nat.add_zero] at h

/-- **Sylvester's law of inertia, in the form used to read off a signature.** A form negative
definite on `V` and positive definite on `W`, with `V` and `W` of complementary dimensions, has
index exactly `finrank V`. Nondegeneracy is not assumed: it follows, see
`radical_eq_bot_of_negDef_of_posDef`. -/
theorem sigNeg_eq_of_negDef_of_posDef (hV : ((-Q).restrict V).PosDef)
    (hW : (Q.restrict W).PosDef) (hdim : finrank 𝕜 V + finrank 𝕜 W = finrank 𝕜 M) :
    sigNeg Q = finrank 𝕜 V := by
  have h1 := le_sigNeg_of_negDef Q hV
  have h2 := le_sigPos_of_posDef Q hW
  have h3 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  omega

theorem sigPos_eq_of_negDef_of_posDef (hV : ((-Q).restrict V).PosDef)
    (hW : (Q.restrict W).PosDef) (hdim : finrank 𝕜 V + finrank 𝕜 W = finrank 𝕜 M) :
    sigPos Q = finrank 𝕜 W := by
  have h1 := le_sigNeg_of_negDef Q hV
  have h2 := le_sigPos_of_posDef Q hW
  have h3 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  omega

/-- Such a splitting also forces the form to be nondegenerate. -/
theorem radical_eq_bot_of_negDef_of_posDef (hV : ((-Q).restrict V).PosDef)
    (hW : (Q.restrict W).PosDef) (hdim : finrank 𝕜 V + finrank 𝕜 W = finrank 𝕜 M) :
    Q.radical = ⊥ := by
  have h1 := le_sigNeg_of_negDef Q hV
  have h2 := le_sigPos_of_posDef Q hW
  have h3 := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  exact Submodule.finrank_eq_zero.mp (by omega)

end QuadraticForm

namespace ContinuousLinearMap

section Perturbation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Positive definiteness on a subspace is quantitative: `ε ‖v‖ ^ 2 ≤ b v v` for some `ε > 0`. -/
lemma exists_pos_forall_le_of_posDef (b : F →L[ℝ] F →L[ℝ] ℝ) {V : Submodule ℝ F}
    (hV : ∀ v : V, v ≠ 0 → 0 < b v v) :
    ∃ ε > 0, ∀ v : V, ε * ‖(v : F)‖ ^ 2 ≤ b v v := by
  have hcont : Continuous fun v : V ↦ b (v : F) (v : F) :=
    b.continuous₂.comp (continuous_subtype_val.prodMk continuous_subtype_val)
  rcases subsingleton_or_nontrivial V with _ | _
  · -- The subspace is trivial: every vector is `0` and both sides vanish.
    refine ⟨1, one_pos, fun v ↦ ?_⟩
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · obtain ⟨v₀, hv₀, hmin⟩ :=
      (isCompact_sphere (0 : V) 1).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    have hv₀norm : ‖v₀‖ = 1 := by simpa using hv₀
    have hv₀ne : v₀ ≠ 0 := by
      intro h; rw [h] at hv₀norm; simp at hv₀norm
    refine ⟨b (v₀ : F) (v₀ : F), hV v₀ hv₀ne, fun v ↦ ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    -- Normalise `v` to the unit sphere and use homogeneity of `v ↦ b v v`.
    have hvn : (0 : ℝ) < ‖(v : F)‖ := by
      simpa using norm_pos_iff.mpr hv
    set u : V := ‖(v : F)‖⁻¹ • v with hu_def
    have hu : u ∈ sphere (0 : V) 1 := by
      simp only [mem_sphere_iff_norm, sub_zero, hu_def, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (by simpa using hvn.ne')
    have hbu : b (v₀ : F) (v₀ : F) ≤ b (u : F) (u : F) := hmin hu
    have hcoe : (u : F) = ‖(v : F)‖⁻¹ • (v : F) := rfl
    have hscale : b (u : F) (u : F) = (‖(v : F)‖ ^ 2)⁻¹ * b (v : F) (v : F) := by
      simp only [hcoe, map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hscale] at hbu
    have hpos : (0 : ℝ) < ‖(v : F)‖ ^ 2 := pow_pos hvn 2
    calc b (v₀ : F) (v₀ : F) * ‖(v : F)‖ ^ 2
        ≤ ((‖(v : F)‖ ^ 2)⁻¹ * b (v : F) (v : F)) * ‖(v : F)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hbu hpos.le
      _ = b (v : F) (v : F) := by field_simp

/-- A positive definite continuous bilinear form on a finite-dimensional real space is coercive. -/
theorem _root_.IsCoercive.of_posDef {b : F →L[ℝ] F →L[ℝ] ℝ} (h : ∀ v : F, v ≠ 0 → 0 < b v v) :
    IsCoercive b := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_forall_le_of_posDef b (V := ⊤) fun v hv ↦
    h v fun hv0 ↦ hv (Subtype.ext hv0)
  refine ⟨ε, hε, fun u ↦ ?_⟩
  have h1 : ε * ‖u‖ ^ 2 ≤ b u u := by
    simpa using hle ⟨u, _root_.Submodule.mem_top⟩
  nlinarith [h1, sq_nonneg ‖u‖]

omit [FiniteDimensional ℝ F] in
private lemma pos_of_norm_sub_lt {b c : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F} {ε : ℝ}
    (hle : ∀ v : V, ε * ‖(v : F)‖ ^ 2 ≤ b v v) (hc : ‖c - b‖ < ε) :
    ∀ v : V, v ≠ 0 → 0 < c (v : F) (v : F) := by
  intro v hv
  have hvn : (0 : ℝ) < ‖(v : F)‖ := by simpa using norm_pos_iff.mpr hv
  have hbound : |c (v : F) (v : F) - b (v : F) (v : F)| ≤ ‖c - b‖ * ‖(v : F)‖ ^ 2 := by
    have h := (c - b).le_opNorm₂ (v : F) (v : F)
    simp only [sub_apply, Real.norm_eq_abs] at h
    calc |c (v : F) (v : F) - b (v : F) (v : F)| ≤ ‖c - b‖ * ‖(v : F)‖ * ‖(v : F)‖ := h
      _ = ‖c - b‖ * ‖(v : F)‖ ^ 2 := by ring
  have hsq : (0 : ℝ) < ‖(v : F)‖ ^ 2 := by positivity
  nlinarith [hle v, (abs_le.mp hbound).1, (abs_le.mp hbound).2]

/-- Positive definiteness on a fixed subspace is an open condition on the bilinear form. -/
lemma eventually_forall_pos {b : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F}
    (hV : ∀ v : V, v ≠ 0 → 0 < b v v) :
    ∀ᶠ c in 𝓝 b, ∀ v : V, v ≠ 0 → 0 < c (v : F) (v : F) := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_forall_le_of_posDef b hV
  filter_upwards [ball_mem_nhds b hε] with c hc
  have h1 : dist c b < ε := Metric.mem_ball.mp hc
  rw [dist_eq_norm c b] at h1
  exact pos_of_norm_sub_lt hle h1

lemma eventually_forall_neg {b : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F}
    (hV : ∀ v : V, v ≠ 0 → b v v < 0) :
    ∀ᶠ c in 𝓝 b, ∀ v : V, v ≠ 0 → c (v : F) (v : F) < 0 := by
  have hneg : ∀ v : V, v ≠ 0 → 0 < (-b) (v : F) (v : F) := fun v hv ↦ by simpa using hV v hv
  obtain ⟨ε, hε, hle⟩ := exists_pos_forall_le_of_posDef (-b) hneg
  filter_upwards [ball_mem_nhds b hε] with c hc v hv
  have hcb : dist c b < ε := Metric.mem_ball.mp hc
  rw [dist_eq_norm c b] at hcb
  have heq : (-c) - (-b) = -(c - b) := by abel
  have hnorm : ‖(-c) - (-b)‖ < ε := by
    have h2 : ‖(-c) - (-b)‖ = ‖c - b‖ := by rw [heq]; exact norm_neg (c - b)
    rw [h2]; exact hcb
  have := pos_of_norm_sub_lt hle hnorm v hv
  simpa using this

/-! ### Local constancy of the signature -/

variable {b : F →L[ℝ] F →L[ℝ] ℝ}

/-- **The signature is locally constant.** If `b.toQuadraticForm` has trivial radical, so does
every nearby form, with the same `sigPos` and `sigNeg`.

No symmetry is assumed: `sigPos`, `sigNeg` and `radical` see only `v ↦ b v v`, which is unchanged
by symmetrising `b`. -/
theorem eventually_sigNeg_eq (hb : b.toQuadraticForm.radical = ⊥) :
    ∀ᶠ c in 𝓝 b, c.toQuadraticForm.radical = ⊥ ∧
      sigPos c.toQuadraticForm = sigPos b.toQuadraticForm ∧
      sigNeg c.toQuadraticForm = sigNeg b.toQuadraticForm := by
  obtain ⟨Vp, hVpdim, hVppos⟩ :=
    exists_finrank_eq_sigPos_and_posDef b.toQuadraticForm
  obtain ⟨Vn, hVndim, hVnneg⟩ :=
    exists_finrank_eq_sigNeg_and_negDef b.toQuadraticForm
  have hsum := QuadraticForm.sigPos_add_sigNeg_of_radical_eq_bot hb
  have hpos : ∀ v : Vp, v ≠ 0 → 0 < b (v : F) (v : F) := fun v hv ↦ hVppos v hv
  have hneg : ∀ v : Vn, v ≠ 0 → b (v : F) (v : F) < 0 := fun v hv ↦ by
    have h : (0 : ℝ) < -(b (v : F) (v : F)) := hVnneg v hv
    linarith
  filter_upwards [eventually_forall_pos hpos, eventually_forall_neg hneg] with c hcp hcn
  -- Both maximal subspaces stay definite, so the two parts of the signature can only grow.
  have hle_pos : sigPos b.toQuadraticForm ≤ sigPos c.toQuadraticForm := by
    rw [← hVpdim]
    exact le_sigPos_of_posDef _ fun v hv ↦ hcp v hv
  have hle_neg : sigNeg b.toQuadraticForm ≤ sigNeg c.toQuadraticForm := by
    rw [← hVndim]
    refine le_sigNeg_of_negDef _ fun v hv ↦ ?_
    show (0 : ℝ) < -(c (v : F) (v : F))
    linarith [hcn v hv]
  -- Sylvester's law caps the total, so both inequalities are equalities.
  have hc := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := c.toQuadraticForm)
  have hrad : finrank ℝ c.toQuadraticForm.radical = 0 := by omega
  refine ⟨Submodule.finrank_eq_zero.mp hrad, by omega, by omega⟩

/-! ### Transport along a linear equivalence -/

section Congr

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]

/-- A linear equivalence intertwining two continuous bilinear forms preserves `sigNeg`. Used to
transport a fibrewise computation to the model fibre of a vector bundle. -/
lemma sigNeg_toQuadraticForm_of_congr (b : X →L[ℝ] X →L[ℝ] ℝ) (b' : Y →L[ℝ] Y →L[ℝ] ℝ)
    (φ : X ≃ₗ[ℝ] Y) (h : ∀ u w : X, b' (φ u) (φ w) = b u w) :
    sigNeg b.toQuadraticForm = sigNeg b'.toQuadraticForm :=
  QuadraticMap.Equivalent.sigNeg_eq ⟨{ toLinearEquiv := φ, map_app' := fun m ↦ h m m }⟩

lemma radical_toQuadraticForm_eq_bot_of_congr (b : X →L[ℝ] X →L[ℝ] ℝ) (b' : Y →L[ℝ] Y →L[ℝ] ℝ)
    (φ : X ≃ₗ[ℝ] Y) (h : ∀ u w : X, b' (φ u) (φ w) = b u w)
    (hb : b.toQuadraticForm.radical = ⊥) : b'.toQuadraticForm.radical = ⊥ := by
  have hiso : QuadraticMap.IsometryEquiv b.toQuadraticForm b'.toQuadraticForm :=
    { toLinearEquiv := φ, map_app' := fun m ↦ h m m }
  rw [← QuadraticMap.IsometryEquiv.map_radical hiso, hb, Submodule.map_bot]

end Congr

end Perturbation

end ContinuousLinearMap

/-! ## The index of a pseudo-inner product space -/

namespace PseudoInnerProductSpace

variable (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [PseudoInnerProductSpace E]

/-- The index, or negative inertia: the largest dimension of a subspace on which the form is
negative definite. Index `0` is the Riemannian case, index `1` the Lorentzian one.

As for `QuadraticForm.sigNeg`, this is `0` when `E` is infinite-dimensional, so the results below
assume `[FiniteDimensional ℝ E]`. -/
noncomputable def index : ℕ := sigNeg (toQuadraticForm E)

lemma index_eq_sigNeg : index E = sigNeg (toQuadraticForm E) := rfl

lemma index_le_finrank : index E ≤ finrank ℝ E := by
  simpa [index] using sigPos_le_finrank (-toQuadraticForm E)

/-- The coindex, or positive inertia: the largest dimension of a subspace on which the form is
positive definite. In the "mostly minus" convention a Lorentzian form is one of coindex `1`. -/
noncomputable def coindex : ℕ := sigPos (toQuadraticForm E)

lemma coindex_eq_sigPos : coindex E = sigPos (toQuadraticForm E) := rfl

lemma coindex_le_finrank : coindex E ≤ finrank ℝ E := sigPos_le_finrank _

variable {E} in
/-- A form of positive coindex lives on a finite-dimensional space. -/
lemma finiteDimensional_of_coindex_pos (h : 0 < coindex E) : FiniteDimensional ℝ E :=
  Module.finite_of_finrank_pos (lt_of_lt_of_le h (coindex_le_finrank E))

variable {E} in
/-- A form of positive index lives on a finite-dimensional space: `sigNeg` vanishes otherwise. -/
lemma finiteDimensional_of_index_pos (h : 0 < index E) : FiniteDimensional ℝ E :=
  Module.finite_of_finrank_pos (lt_of_lt_of_le h (index_le_finrank E))

/-- Nondegeneracy, restated: the quadratic form has trivial radical. -/
lemma radical_toQuadraticForm_eq_bot : (toQuadraticForm E).radical = ⊥ := by
  rw [QuadraticMap.radical_eq_ker_polarBilin, Submodule.eq_bot_iff]
  intro v hv
  refine eq_zero_of_pseudoInner_eq_zero fun w ↦ ?_
  have h0 : QuadraticMap.polar (toQuadraticForm E) v w = 0 := by
    simpa using DFunLike.congr_fun (LinearMap.mem_ker.mp hv) w
  have hpolar : QuadraticMap.polar (toQuadraticForm E) v w = 2 * pseudoInner v w := by
    simp only [QuadraticMap.polar, toQuadraticForm_apply, pseudoInner_add_left,
      pseudoInner_add_right]
    rw [pseudoInner_comm w v]
    ring
  linarith

variable [FiniteDimensional ℝ E]

/-- The positive and negative inertia add up to the dimension: the form is nondegenerate, so
Sylvester's law leaves no radical. -/
lemma coindex_add_index_eq_finrank : coindex E + index E = finrank ℝ E :=
  QuadraticForm.sigPos_add_sigNeg_of_radical_eq_bot (radical_toQuadraticForm_eq_bot E)


variable {E} in
/-- **Computing the index.** A splitting into a negative definite `V` and a positive definite `W`
of complementary dimensions determines the index, namely `finrank V`. -/
lemma index_eq_of_negDef_of_posDef {V W : Submodule ℝ E}
    (hV : ∀ v : V, v ≠ 0 → pseudoInner (v : E) (v : E) < 0)
    (hW : ∀ w : W, w ≠ 0 → 0 < pseudoInner (w : E) (w : E))
    (hdim : finrank ℝ V + finrank ℝ W = finrank ℝ E) :
    index E = finrank ℝ V := by
  refine QuadraticForm.sigNeg_eq_of_negDef_of_posDef (fun v hv ↦ ?_) (fun w hw ↦ ?_) hdim
  · show (0 : ℝ) < -(toQuadraticForm E (v : E))
    have := hV v hv
    simp only [toQuadraticForm_apply]
    linarith
  · show (0 : ℝ) < toQuadraticForm E (w : E)
    simpa using hW w hw

variable {E} in
/-- The companion of `index_eq_of_negDef_of_posDef` for the positive inertia. -/
lemma coindex_eq_of_negDef_of_posDef {V W : Submodule ℝ E}
    (hV : ∀ v : V, v ≠ 0 → pseudoInner (v : E) (v : E) < 0)
    (hW : ∀ w : W, w ≠ 0 → 0 < pseudoInner (w : E) (w : E))
    (hdim : finrank ℝ V + finrank ℝ W = finrank ℝ E) :
    coindex E = finrank ℝ W := by
  refine QuadraticForm.sigPos_eq_of_negDef_of_posDef (fun v hv ↦ ?_) (fun w hw ↦ ?_) hdim
  · show (0 : ℝ) < -(toQuadraticForm E (v : E))
    have := hV v hv
    simp only [toQuadraticForm_apply]
    linarith
  · show (0 : ℝ) < toQuadraticForm E (w : E)
    simpa using hW w hw

variable {E} in
lemma one_le_index_of_neg {v : E} (hv : v ≠ 0) (h : pseudoInner v v < 0) : 1 ≤ index E := by
  have key : Module.finrank ℝ (ℝ ∙ v : Submodule ℝ E) ≤ sigNeg (toQuadraticForm E) := by
    refine le_sigNeg_of_negDef _ fun x hx ↦ ?_
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hx (Subtype.ext (by simpa using hc.symm))
    have hval : toQuadraticForm E (x : E) = c * c * pseudoInner v v := by
      rw [← hc, ← toQuadraticForm_apply v, QuadraticMap.map_smul]
      simp [smul_eq_mul]
    show (0 : ℝ) < -(toQuadraticForm E (x : E))
    rw [hval]
    nlinarith [mul_self_pos.mpr hc0]
  rwa [finrank_span_singleton hv] at key

variable {E} in
lemma index_eq_zero_of_posDef (h : (toQuadraticForm E).PosDef) : index E = 0 := by
  obtain ⟨W, hW, hWneg⟩ :=
    exists_finrank_eq_sigNeg_and_negDef (Q := toQuadraticForm E)
  have hWbot : W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have hxW : (⟨x, hx⟩ : W) ≠ 0 := fun hcontra ↦ hx0 (congrArg Subtype.val hcontra)
    have hlt : toQuadraticForm E x < 0 := by
      have := hWneg _ hxW
      simp only [QuadraticMap.restrict_apply, neg_apply] at this
      linarith
    exact absurd (h x hx0) (by linarith)
  simp [index, ← hW, hWbot]

/-- A form is Riemannian exactly when its index vanishes. -/
lemma index_eq_zero_iff_posDef : index E = 0 ↔ (toQuadraticForm E).PosDef := by
  refine ⟨fun h ↦ ?_, index_eq_zero_of_posDef⟩
  obtain ⟨V, hV, hVpos⟩ := exists_finrank_eq_sigPos_and_posDef (toQuadraticForm E)
  have hfull : finrank ℝ V = finrank ℝ E := by
    have hc := coindex_eq_sigPos E
    have := coindex_add_index_eq_finrank E
    omega
  have hVtop : V = ⊤ := Submodule.eq_top_of_finrank_eq hfull
  intro v hv
  subst hVtop
  simpa using hVpos ⟨v, Submodule.mem_top⟩ (fun h0 ↦ hv (congrArg Subtype.val h0))

/-- Raising both indices is an isometry, so the inverse metric on `E⋆` has the same index. -/
lemma index_dual_eq [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] :
    letI := dual E
    index (E →L[ℝ] ℝ) = index E := by
  have key : ∀ u w : E, dualPseudoInnerSL E (flatL E u) (flatL E w) = pseudoInner u w := by
    intro u w
    rw [dualPseudoInnerSL_apply, sharpL_flatL, flatL_apply]
  exact (ContinuousLinearMap.sigNeg_toQuadraticForm_of_congr
    (PseudoInnerProductSpace.pseudoInnerSL (E := E)) (dualPseudoInnerSL E)
    (flatEquiv E).toLinearEquiv key).symm

/-- **Riemannian geometry is the index-zero case.** -/
@[simp]
lemma index_eq_zero_of_innerProductSpace (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] : index F = 0 :=
  index_eq_zero_of_posDef fun v hv ↦ by
    simpa using real_inner_self_pos.mpr hv

end PseudoInnerProductSpace
