/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!

# The Cayley transform for a self-adjoint operator

The Cayley transform `c(x) = (x - i) / (x + i)` maps the real line onto the unit circle minus the
point `1` (which corresponds to `x = ∞`). Applied to a self-adjoint operator in place of a real
number, it turns an (unbounded, densely-defined) self-adjoint operator into a bounded unitary
operator — the standard device, due to von Neumann, for reducing unbounded self-adjoint spectral
theory to the bounded/unitary case, where tools such as the continuous functional calculus already
apply.

This file develops the elementary scalar transform `cayley`/`cayleyInverse` first — the inverse is
only needed away from `1`, the point corresponding to infinity, and is defined arbitrarily there;
on the actual Cayley image it is a genuine inverse — and then transports it to an unbounded
self-adjoint operator `T : H →ₗ.[ℂ] H`: `cayleyPMap T` is the resulting Cayley-transformed partial
operator, which turns out to be everywhere-defined and bounded (`cayleyContinuousLinearMap`), and
in fact a genuine unitary (`cayleyUnitary`) once `T` is self-adjoint. No unbounded theorem is
hidden in a definition: everything here is elementary Hilbert-space algebra once self-adjointness
supplies the resolvent set membership at `± i`.

- `cayley`, `cayleyInverse` : the scalar Möbius maps `(x - i) / (x + i)` and its (one-sided)
  inverse, together with their real/imaginary-part formulas and round-trip identities.
- `cayleyPMap` : the Cayley transform of a partial operator, before forgetting boundedness.
- `cayleyContinuousLinearMap`, `cayleyUnitary` : the resulting bounded operator, proved to be a
  genuine unitary once `T` is self-adjoint.

-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ComplexOrder InnerProductSpace

namespace QuantumMechanics

/-! ## A. The scalar Cayley transform -/

/-- The scalar Cayley transform from the real line to the unit circle. -/
def cayley (x : ℝ) : ℂ := (x - Complex.I) / (x + Complex.I)

/-- The inverse Cayley coordinate, with an arbitrary value at the point `1` (infinity). -/
def cayleyInverse (z : ℂ) : ℝ := if z = 1 then 0 else -z.im / (1 - z.re)

lemma cayley_ne_one (x : ℝ) : cayley x ≠ 1 := by
  intro h
  have hden : (x : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    norm_num at hi
  have h' : (x : ℂ) - Complex.I = (x : ℂ) + Complex.I := by
    have h' := (div_eq_iff hden).mp (by simpa [cayley] using h)
    simpa using h'
  have hi := congrArg Complex.im h'
  norm_num at hi

lemma cayley_re (x : ℝ) : (cayley x).re = (x ^ 2 - 1) / (x ^ 2 + 1) := by
  rw [cayley, Complex.div_re]
  simp [Complex.normSq, pow_two]
  ring_nf

lemma cayley_im (x : ℝ) : (cayley x).im = (-2 * x) / (x ^ 2 + 1) := by
  rw [cayley, Complex.div_im]
  simp [Complex.normSq, pow_two]
  ring_nf

lemma cayleyInverse_cayley (x : ℝ) : cayleyInverse (cayley x) = x := by
  rw [cayleyInverse, if_neg (cayley_ne_one x), cayley_im, cayley_re]
  have h : x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
  field_simp
  ring

lemma cayley_norm (x : ℝ) : ‖cayley x‖ = 1 := by
  have hs : ‖cayley x‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, cayley_re, cayley_im]
    have h : x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
    field_simp
    ring
  nlinarith [norm_nonneg (cayley x)]

lemma cayley_cayleyInverse {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    cayley (cayleyInverse z) = z := by
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        simp [Complex.normSq_apply, pow_two]
      _ = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
      _ = 1 := by rw [hz]; norm_num
  have hden : 1 - z.re ≠ 0 := by
    intro hd
    have hre : z.re = 1 := by linarith
    have him : z.im = 0 := by nlinarith [hnorm]
    apply hz1
    apply Complex.ext <;> assumption
  rw [Complex.ext_iff]
  simp only [cayleyInverse, if_neg hz1]
  rw [cayley_re, cayley_im]
  have hx : (-(z.im) / (1 - z.re)) ^ 2 + 1 ≠ 0 := by
    positivity
  have hrel : z.im ^ 2 + (1 - z.re) ^ 2 = 2 * (1 - z.re) := by
    nlinarith [hnorm]
  constructor
  · field_simp [hden]
    nlinarith [hrel]
  · field_simp [hden]
    have hm := congrArg (fun t : ℝ => z.im * t) hnorm
    nlinarith [hm]

lemma measurable_cayley : Measurable cayley := by
  unfold cayley
  fun_prop

lemma measurable_cayleyInverse : Measurable cayleyInverse := by
  unfold cayleyInverse
  apply Measurable.ite
  · exact measurableSet_eq
  · fun_prop
  · fun_prop

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## B. The Cayley transform of a partial operator -/

/-- The Cayley transform before forgetting that it is bounded. -/
def cayleyPMap (T : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  (T - Complex.I • 1) * (T + Complex.I • 1).inverse

lemma cayleyPMap_domain_top {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) :
    (cayleyPMap T).domain = ⊤ := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  have hker' : (T - (-Complex.I) • 1).toFun.ker = ⊥ := hres.1
  have hrange' : (T - (-Complex.I) • 1).toFun.range = ⊤ := hres.2.1
  have hker : (T + Complex.I • 1).toFun.ker = ⊥ := by
    rw [heq] at hker'
    exact hker'
  have hrange : (T + Complex.I • 1).toFun.range = ⊤ := by
    rw [heq] at hrange'
    exact hrange'
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  have hinvdom : (T + Complex.I • 1).inverse.domain = ⊤ := by
    rw [LinearPMap.inverse_domain, hrange]
  rw [cayleyPMap, LinearPMap.mul_def, LinearPMap.compRestricted_domain]
  apply le_antisymm le_top
  intro x hx
  let xi : (T + Complex.I • 1).inverse.domain :=
    ⟨x, by rw [hinvdom]; exact Submodule.mem_top⟩
  have hv' : (T + Complex.I • 1).inverse xi ∈
      (T + Complex.I • 1).domain := by
    rw [← LinearPMap.inverse_range hker]
    exact LinearMap.mem_range_self _ xi
  have hv : (T + Complex.I • 1).inverse xi ∈ T.domain := hplusdom ▸ hv'
  have hxi' : xi ∈
      Submodule.comap (T + Complex.I • 1).inverse.toFun
        (T - Complex.I • 1).domain := by
    change (T + Complex.I • 1).inverse xi ∈ (T - Complex.I • 1).domain
    simpa [LinearPMap.sub_domain] using hv
  refine ⟨xi, hxi', ?_⟩
  rfl

/-- Turn a continuous partial linear map with full domain into a bounded operator on `H`. -/
def topDomainToContinuousLinearMap (A : H →ₗ.[ℂ] H) (hdom : A.domain = ⊤)
    (hc : Continuous A.toFun) : H →L[ℂ] H := by
  let i : H →ₗ[ℂ] A.domain :=
    { toFun := fun x => ⟨x, hdom ▸ Submodule.mem_top⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let L : H →ₗ[ℂ] H := A.toFun.comp i
  have hL : Continuous L := by
    dsimp [L]
    apply hc.comp
    dsimp [i]
    fun_prop
  exact ⟨L, hL⟩

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma topDomainToContinuousLinearMap_apply (A : H →ₗ.[ℂ] H) (hdom : A.domain = ⊤)
    (hc : Continuous A.toFun) (x : H) :
    topDomainToContinuousLinearMap A hdom hc x = A ⟨x, hdom ▸ Submodule.mem_top⟩ := by
  rfl

lemma cayleyPMap_eq_one_sub {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) :
    cayleyPMap T = 1 - (2 * Complex.I) • (T + Complex.I • 1).inverse := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  have hker : (T + Complex.I • 1).toFun.ker = ⊥ := by
    rw [← heq]
    exact hres.1
  have hrange : (T + Complex.I • 1).toFun.range = ⊤ := by
    rw [← heq]
    exact hres.2.1
  have hinvdom : (T + Complex.I • 1).inverse.domain = ⊤ := by
    rw [LinearPMap.inverse_domain, hrange]
  have hdom := cayleyPMap_domain_top hT
  have hdom' : (1 - (2 * Complex.I) • (T + Complex.I • 1).inverse).domain = ⊤ := by
    simp [LinearPMap.sub_domain, hinvdom]
  apply LinearPMap.ext (hdom.trans hdom'.symm)
  intro x hx hx'
  let xi : (T + Complex.I • 1).inverse.domain :=
    ⟨x, by rw [hinvdom]; exact Submodule.mem_top⟩
  have hxi : (T + Complex.I • 1).inverse xi ∈ (T + Complex.I • 1).domain := by
    rw [← LinearPMap.inverse_range hker]
    exact LinearMap.mem_range_self _ xi
  have hxi_range : (x : H) ∈ LinearMap.range (T + Complex.I • 1).toFun := by
    rw [← LinearPMap.inverse_domain]
    exact xi.property
  obtain ⟨x₀, hx₀⟩ := hxi_range
  have hxy : (T + Complex.I • 1) x₀ = xi := by
    change (T + Complex.I • 1) x₀ = x
    exact hx₀
  have hinv₀ : (T + Complex.I • 1).inverse xi = x₀ :=
    LinearPMap.inverse_apply_eq hker hxy
  have hinv : (T + Complex.I • 1)
      ⟨(T + Complex.I • 1).inverse xi, hxi⟩ = x := by
    have heq : (⟨(T + Complex.I • 1).inverse xi, hxi⟩ :
        (T + Complex.I • 1).domain) = x₀ := Subtype.ext hinv₀
    rw [heq]
    exact hx₀
  let y : (T + Complex.I • 1).domain :=
    ⟨(T + Complex.I • 1).inverse xi, hxi⟩
  have hy : (T + Complex.I • 1) y = x := hinv
  change (T - Complex.I • 1) y = x - (2 * Complex.I) • (y : H)
  rw [← hy]
  simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply]
  module

lemma cayleyPMap_eq_one_sub_minus {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) :
    cayleyPMap T = 1 - (2 * Complex.I) • (T - (-Complex.I) • 1).inverse := by
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  have heq' := congrArg LinearPMap.inverse heq
  rw [cayleyPMap_eq_one_sub hT, ← heq']

/-! ## C. The bounded, unitary Cayley transform -/

/-- The bounded operator represented by the Cayley transform of a self-adjoint `LinearPMap`. -/
noncomputable def cayleyContinuousLinearMap (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    H →L[ℂ] H := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have hinvdom : (T - (-Complex.I) • 1).inverse.domain = ⊤ := by
    rw [LinearPMap.inverse_domain, hres.2.1]
  exact 1 - (2 * Complex.I) •
    topDomainToContinuousLinearMap (T - (-Complex.I) • 1).inverse hinvdom hres.2.2

/-- A bounded operator, viewed as an everywhere-defined `LinearPMap`. -/
def continuousLinearMapToPMap (L : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  ⟨⊤, L.toLinearMap.comp Submodule.topEquiv.toLinearMap⟩

lemma cayleyPMap_eq_continuousLinearMapToPMap {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) :
    cayleyPMap T = continuousLinearMapToPMap (cayleyContinuousLinearMap T hT) := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  calc
    cayleyPMap T = 1 - (2 * Complex.I) • (T - (-Complex.I) • 1).inverse :=
      cayleyPMap_eq_one_sub_minus hT
    _ = continuousLinearMapToPMap (cayleyContinuousLinearMap T hT) := by
      have hinvdom : (T - (-Complex.I) • 1).inverse.domain = ⊤ := by
        rw [LinearPMap.inverse_domain]
        exact hres.2.1
      have hdom : (1 - (2 * Complex.I) •
          (T - (-Complex.I) • 1).inverse).domain = ⊤ := by
        simp [LinearPMap.sub_domain, hinvdom]
      have hdom' : (continuousLinearMapToPMap
          (cayleyContinuousLinearMap T hT)).domain = ⊤ := rfl
      apply LinearPMap.ext (hdom.trans hdom'.symm)
      intro x hx hx'
      simp only [LinearPMap.sub_apply, LinearPMap.smul_apply, continuousLinearMapToPMap]
      simp [cayleyContinuousLinearMap,
        topDomainToContinuousLinearMap_apply (T - (-Complex.I) • 1).inverse
          hinvdom hres.2.2 x]

lemma cayleyContinuousLinearMap_norm_shift {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) (y : T.domain) :
    ‖T y - Complex.I • (y : H)‖ = ‖T y + Complex.I • (y : H)‖ := by
  have hsym : T.IsSymmetric := LinearPMap.IsSelfAdjoint.isSymmetric hT
  have hreal : (⟪T y, (y : H)⟫_ℂ).im = 0 := by
    exact Complex.conj_eq_iff_im.mp
      ((LinearPMap.isSymmetric_iff_inner_map_self_real).mp hsym y)
  have hsub := norm_sub_sq (𝕜 := ℂ) (T y) (Complex.I • (y : H))
  have hadd := norm_add_sq (𝕜 := ℂ) (T y) (Complex.I • (y : H))
  have hinner : (⟪T y, Complex.I • (y : H)⟫_ℂ).re = 0 := by
    rw [inner_smul_right]
    simp [Complex.mul_re, hreal]
  have hnorm : ‖Complex.I • (y : H)‖ ^ 2 = ‖(y : H)‖ ^ 2 := by
    rw [norm_smul]
    simp
  have hsquares : ‖T y - Complex.I • (y : H)‖ ^ 2 =
      ‖T y + Complex.I • (y : H)‖ ^ 2 := by
    rw [hsub, hadd]
    rw [show RCLike.re ⟪T y, Complex.I • (y : H)⟫_ℂ = 0 from hinner, hnorm]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares

lemma cayleyContinuousLinearMap_apply_of_mem_range {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) (y : (T + Complex.I • 1).domain) (x : H)
    (hy : (T + Complex.I • 1) y = x) :
    cayleyContinuousLinearMap T hT x = (T - Complex.I • 1) y := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  have hres' := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := Complex.I) (by norm_num)
  have hker' : (T - Complex.I • 1).toFun.ker = ⊥ := hres'.1
  have hminusdom : (T - (-Complex.I) • 1).domain = T.domain := by
    simp [LinearPMap.sub_domain]
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  have hyT : (y : H) ∈ T.domain := by
    rw [← hplusdom]
    exact y.property
  have hym : (y : H) ∈ (T - (-Complex.I) • 1).domain := by
    rw [hminusdom]
    exact hyT
  let hyminus : (T - (-Complex.I) • 1).domain :=
    ⟨(y : H), hym⟩
  have hyminus_eq : (T - (-Complex.I) • 1) hyminus = x := by
    have hyt : (⟨(hyminus : H), hminusdom ▸ hyminus.property⟩ : T.domain) =
        ⟨(y : H), hyT⟩ := by
      apply Subtype.ext
      change (y : H) = (y : H)
      rfl
    simp only [LinearPMap.sub_apply, LinearPMap.smul_apply]
    rw [hyt]
    simpa [LinearPMap.add_apply, LinearPMap.smul_apply] using hy
  have hxinv : x ∈ (T - (-Complex.I) • 1).inverse.domain := by
    rw [LinearPMap.inverse_domain]
    rw [hres.2.1]
    exact Submodule.mem_top
  have hminus_inv : (T - (-Complex.I) • 1).inverse
      ⟨x, hxinv⟩ = hyminus := by
    exact LinearPMap.inverse_apply_eq hres.1 hyminus_eq
  have hc : Continuous (T - (-Complex.I) • 1).inverse.toFun := hres.2.2
  simp only [cayleyContinuousLinearMap, sub_apply, smul_apply]
  rw [topDomainToContinuousLinearMap_apply _ _ hc]
  rw [hminus_inv]
  have hycoe : (hyminus : H) = (y : H) := by
    change (y : H) = (y : H)
    rfl
  rw [hycoe]
  change x - (2 * Complex.I) • (y : H) = (T - Complex.I • 1) y
  rw [← hy]
  simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply]
  module

lemma cayleyContinuousLinearMap_norm_map {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) (x : H) :
    ‖cayleyContinuousLinearMap T hT x‖ = ‖x‖ := by
  obtain ⟨y, hy⟩ := LinearPMap.IsSelfAdjoint.sub_smul_surjective hT
    (z := -Complex.I) (by norm_num) x
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  let yp : (T + Complex.I • 1).domain :=
    ⟨(y : H), by rw [hplusdom]; exact (show (y : H) ∈ T.domain from by
      simpa [LinearPMap.sub_domain] using y.property)⟩
  have hyp : (T + Complex.I • 1) yp = x := by
    simpa [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply] using hy
  rw [cayleyContinuousLinearMap_apply_of_mem_range hT yp x hyp]
  rw [← hyp]
  have hypp : (yp : H) ∈ (T + Complex.I • 1).domain := yp.property
  let yT : T.domain := ⟨(yp : H), hplusdom ▸ hypp⟩
  have hcoey : (yp : H) = (yT : H) := by
    dsimp [yp, yT]
  have hshift := cayleyContinuousLinearMap_norm_shift hT yT
  convert hshift using 1 <;>
    simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, hcoey]

lemma cayleyContinuousLinearMap_isometry {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) : Isometry (cayleyContinuousLinearMap T hT) := by
  intro x y
  have hdist : dist (cayleyContinuousLinearMap T hT x)
      (cayleyContinuousLinearMap T hT y) = dist x y := by
    simpa [dist_eq_norm, map_sub] using cayleyContinuousLinearMap_norm_map hT (x - y)
  rw [edist_dist, hdist, edist_dist]

lemma cayleyContinuousLinearMap_surjective {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) : Function.Surjective (cayleyContinuousLinearMap T hT) := by
  intro x
  obtain ⟨y, hy⟩ := LinearPMap.IsSelfAdjoint.sub_smul_surjective hT
    (z := Complex.I) (by norm_num) x
  have hminusdom : (T - Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.sub_domain]
  have hym : (y : H) ∈ T.domain := by
    have h := y.property
    exact hminusdom ▸ h
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  have hypmem : (y : H) ∈ (T + Complex.I • 1).domain := by
    rw [hplusdom]
    exact hym
  let yp : (T + Complex.I • 1).domain := ⟨(y : H), hypmem⟩
  refine ⟨(T + Complex.I • 1) yp, ?_⟩
  rw [cayleyContinuousLinearMap_apply_of_mem_range hT yp _ rfl]
  simpa [LinearPMap.sub_apply, LinearPMap.smul_apply] using hy

/-- The unitary Cayley transform of a self-adjoint partial operator. -/
noncomputable def cayleyUnitary (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    ((cayleyContinuousLinearMap T hT).toLinearMap.toLinearIsometry
      (cayleyContinuousLinearMap_isometry hT))
    (cayleyContinuousLinearMap_surjective hT)

@[simp]
lemma cayleyUnitary_apply (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    cayleyUnitary T hT x = cayleyContinuousLinearMap T hT x := by
  rfl

end QuantumMechanics

end
