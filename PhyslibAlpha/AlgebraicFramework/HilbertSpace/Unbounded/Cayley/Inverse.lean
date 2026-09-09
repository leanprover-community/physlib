/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.Cayley.Basic

/-!

# The inverse Cayley operator

This file contains the reusable operator-side converse to `Cayley/Basic.lean`'s Cayley transform.
A unitary operator `u` has a possible missing point at `1`; its inverse Cayley transform is
therefore the partial operator

`i (1 + u) (1 - u)⁻¹`.

The inverse is defined on the range of `1 - u`. The no-fixed-vector hypothesis in
`CayleyUnitaryData` makes the inverse unambiguous. For a unitary, the same hypothesis also forces
the range of `1 - u` to be dense; that fact is proved here using orthogonal complements and the
Hilbert-space adjoint theorem. The range calculations at `± i` then prove self-adjointness
directly from the symmetric-operator criterion already available for `LinearPMap`.

No model-specific completeness theorem is used here: this is the general layer that a concrete
Hamiltonian can use after producing its Cayley unitary.

- `inverseCayleyPMap` : the partial inverse Cayley transform of a unitary operator.
- `inverseCayleyPMap_isSelfAdjoint` : the inverse Cayley transform of a unitary with `1` not a
  fixed vector, and with `1 - u` having dense range, is self-adjoint.
- `CayleyUnitaryData` : the standard hypotheses for taking an inverse Cayley transform.
- `cayleyContinuousLinearMap_inverseCayleyPMap_eq` : the inverse Cayley transform of `u`'s Cayley
  transform recovers `u` itself.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Function Set

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. The partial inverse Cayley transform -/

/-- A bounded unitary operator viewed as a total `LinearPMap`. -/
def unitaryToPMap (u : H ≃ₗᵢ[ℂ] H) : H →ₗ.[ℂ] H :=
  continuousLinearMapToPMap (u.toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace H] in
@[nolint unusedArguments, simp]
lemma unitaryToPMap_domain (u : H ≃ₗᵢ[ℂ] H) : (unitaryToPMap u).domain = ⊤ := by
  rfl

omit [CompleteSpace H] in
@[nolint unusedArguments, simp]
lemma one_sub_unitaryToPMap_domain (u : H ≃ₗᵢ[ℂ] H) :
    (1 - unitaryToPMap u).domain = ⊤ := by
  simp [unitaryToPMap, continuousLinearMapToPMap, LinearPMap.sub_domain]

/-- The partial inverse Cayley transform of a unitary operator. -/
def inverseCayleyPMap (u : H ≃ₗᵢ[ℂ] H) : H →ₗ.[ℂ] H :=
  Complex.I • (1 + unitaryToPMap u) * (1 - unitaryToPMap u).inverse

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma inverseCayleyPMap_domain (u : H ≃ₗᵢ[ℂ] H) :
    (inverseCayleyPMap u).domain = (1 - unitaryToPMap u).toFun.range := by
  rw [inverseCayleyPMap, LinearPMap.mul_def, LinearPMap.compRestricted_domain]
  simp only [LinearPMap.smul_domain, LinearPMap.add_domain]
  have hgd : ((1 : H →ₗ.[ℂ] H).domain ⊓ (unitaryToPMap u).domain) = ⊤ := by
    simp [unitaryToPMap, continuousLinearMapToPMap, LinearPMap.one_domain]
  rw [hgd]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    rw [← LinearPMap.inverse_domain]
    exact y.property
  · intro x hx
    have hxdom : x ∈ (1 - unitaryToPMap u).inverse.domain := by
      rw [LinearPMap.inverse_domain]
      exact hx
    refine ⟨⟨x, hxdom⟩, ?_, rfl⟩
    exact Submodule.mem_top

/-! ## B. Density of the range of `1 - u` -/

/- The range of `1 - u` is dense as soon as its orthogonal complement is shown to be zero. The
proof below is deliberately written with the continuous representative: this is the version of
the adjoint/orthogonal-range theorem that remains available in infinite dimension. -/
lemma one_sub_unitaryToPMap_denseRange_of_ker_eq_bot {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥) :
    Dense ((1 - unitaryToPMap u).toFun.range : Set H) := by
  have hrange_eq : (1 - unitaryToPMap u).toFun.range =
      (1 - u.toLinearIsometry.toContinuousLinearMap).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨(y : H), ?_⟩
      rfl
    · rintro ⟨y, rfl⟩
      let y' : (1 - unitaryToPMap u).domain :=
        ⟨y, by
          rw [one_sub_unitaryToPMap_domain u]
          exact Submodule.mem_top⟩
      refine ⟨y', ?_⟩
      rfl
  rw [hrange_eq]
  let F : H →L[ℂ] H := 1 - u.toLinearIsometry.toContinuousLinearMap
  have horthbot : F.rangeᗮ = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxinner : ∀ y : H, ⟪x, F y⟫_ℂ = 0 := by
        intro y
        apply (Submodule.mem_orthogonal' F.range x).mp hx
        exact ⟨y, rfl⟩
      have hinner : ∀ y : H, ⟪x, y⟫_ℂ = ⟪u.symm x, y⟫_ℂ := by
        intro y
        have hz := hxinner y
        have hflip := u.inner_map_eq_flip (u.symm x) (u y)
        change ⟪x, y - u y⟫_ℂ = 0 at hz
        rw [inner_sub_right] at hz
        have hflip' : ⟪x, u y⟫_ℂ = ⟪u.symm x, y⟫_ℂ := by
          simpa only [u.symm_apply_apply, u.apply_symm_apply] using hflip
        rw [hflip'] at hz
        exact sub_eq_zero.mp hz
      have hfixed : x = u x := by
        have hxeq : x = u.symm x := ext_inner_right ℂ hinner
        have hxeq' := congrArg (fun z : H => u z) hxeq
        simpa only [u.apply_symm_apply] using hxeq'.symm
      have hxker : (⟨x, by
          rw [one_sub_unitaryToPMap_domain u]
          exact Submodule.mem_top⟩ : (1 - unitaryToPMap u).domain) ∈
          (1 - unitaryToPMap u).toFun.ker := by
        rw [LinearMap.mem_ker]
        change x - u x = 0
        exact sub_eq_zero.mpr hfixed
      have hxzero : (⟨x, by
          rw [one_sub_unitaryToPMap_domain u]
          exact Submodule.mem_top⟩ : (1 - unitaryToPMap u).domain) = 0 := by
        rw [hker] at hxker
        exact ((Submodule.mem_bot ℂ).mp hxker)
      exact congrArg Subtype.val hxzero
    · exact bot_le
  change Dense (F.range : Set H)
  rw [dense_iff_closure_eq]
  rw [← Submodule.topologicalClosure_coe]
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  rw [horthbot, Submodule.bot_orthogonal_eq_top]
  rfl

lemma unitaryToPMap_cayleyUnitary_eq_cayleyPMap {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) :
    unitaryToPMap (cayleyUnitary T hT) = cayleyPMap T := by
  have hc : (cayleyUnitary T hT).toLinearIsometry.toContinuousLinearMap =
      cayleyContinuousLinearMap T hT := by
    ext x
    exact cayleyUnitary_apply T hT x
  rw [unitaryToPMap, hc]
  exact (cayleyPMap_eq_continuousLinearMapToPMap hT).symm

lemma cayleyUnitary_one_sub_ker_eq_bot {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) :
    (1 - unitaryToPMap (cayleyUnitary T hT)).toFun.ker = ⊥ := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have hker : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have heq : T - (-Complex.I) • (1 : H →ₗ.[ℂ] H) = T + Complex.I • 1 := by
      exact LinearPMap.ext rfl fun x hf hg => by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, neg_smul]
    rw [← heq]
    exact hres.1
  have hinvker := LinearPMap.inverse_ker hker
  have hEq : 1 - unitaryToPMap (cayleyUnitary T hT) =
      (2 * Complex.I) • (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse := by
    rw [unitaryToPMap_cayleyUnitary_eq_cayleyPMap hT, cayleyPMap_eq_one_sub hT]
    have hdom : (1 - (1 - (2 * Complex.I) •
        (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse)).domain =
        ((2 * Complex.I) • (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse).domain := by
      simp [LinearPMap.sub_domain]
    apply LinearPMap.ext hdom
    intro x hx hx'
    simp only [LinearPMap.sub_apply, LinearPMap.smul_apply]
    module
  rw [hEq]
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hx' : (2 * Complex.I) •
      (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse x = 0 := hx
  have hxinv : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse x = 0 := by
    rcases smul_eq_zero.mp hx' with h | h
    · norm_num at h
    · exact h
  have hxker : x ∈ (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse.toFun.ker :=
    LinearMap.mem_ker.mpr hxinv
  rw [hinvker] at hxker
  exact (Submodule.mem_bot ℂ).mp hxker

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma linearPMap_range_smul {Q : H →ₗ.[ℂ] H} (a : ℂ) (ha : a ≠ 0) :
    (a • Q).toFun.range = Q.toFun.range := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    let yQ : Q.domain :=
      ⟨(y : H), by simp [LinearPMap.smul_domain]⟩
    let y' : Q.domain := a • yQ
    refine ⟨y', ?_⟩
    change a • Q.toFun yQ = x at hy
    simpa [y', Q.toFun.map_smul] using hy
  · rintro ⟨y, hy⟩
    let yQ : Q.domain :=
      ⟨(y : H), by simp [y.property]⟩
    let y' : (a • Q).domain :=
      ⟨a⁻¹ • (yQ : H), by
        rw [LinearPMap.smul_domain]
        exact Q.domain.smul_mem _ (by simp [yQ.property])⟩
    refine ⟨y', ?_⟩
    change a • Q.toFun y' = x
    change Q.toFun yQ = x at hy
    change a • Q.toFun (a⁻¹ • yQ) = x
    rw [map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]
    exact hy

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma linearPMap_comp_inverse_apply {Q : H →ₗ.[ℂ] H}
    (hker : Q.toFun.ker = ⊥) (y : Q.inverse.domain) :
    Q (⟨Q.inverse y, by
      rw [← LinearPMap.inverse_range hker]
      exact LinearMap.mem_range_self _ y⟩ : Q.domain) = y := by
  have hc := LinearPMap.compRestricted_inverse_eq hker
  obtain ⟨hcd, hcf⟩ := LinearPMap.dExt_iff.mp hc
  let ac : (Q ∘ᵣ Q.inverse).domain :=
    ⟨(y : H), by
      refine LinearPMap.mem_compRestricted_domain_iff.mpr ⟨y.property, ?_⟩
      rw [← LinearPMap.inverse_range hker]
      exact LinearMap.mem_range_self _ y⟩
  let ad : (LinearPMap.domRestrict (1 : H →ₗ.[ℂ] H) Q.inverse.domain).domain :=
    ⟨(y : H), by
      rw [LinearPMap.domRestrict_domain]
      exact ⟨y.property, Submodule.mem_top⟩⟩
  have h := hcf (x := ac) (y := ad) rfl
  have had : LinearPMap.domRestrict (1 : H →ₗ.[ℂ] H) Q.inverse.domain ad = y := by
    change (ad : H) = (y : H)
    rfl
  rw [had] at h
  simpa [ac, LinearPMap.compRestricted_apply] using h

lemma inverseCayleyPMap_cayleyUnitary_domain {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) :
    (inverseCayleyPMap (cayleyUnitary T hT)).domain = T.domain := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have hplusker : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have heq : T - (-Complex.I) • (1 : H →ₗ.[ℂ] H) = T + Complex.I • 1 := by
      exact LinearPMap.ext rfl fun x hf hg => by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, neg_smul]
    rw [← heq]
    exact hres.1
  have hplusrange : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
    have heq : T - (-Complex.I) • (1 : H →ₗ.[ℂ] H) = T + Complex.I • 1 := by
      exact LinearPMap.ext rfl fun q hq hq' => by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, neg_smul]
    rw [← heq]
    exact hres.2.1
  have hEq : 1 - unitaryToPMap (cayleyUnitary T hT) =
      (2 * Complex.I) • (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse := by
    rw [unitaryToPMap_cayleyUnitary_eq_cayleyPMap hT, cayleyPMap_eq_one_sub hT]
    have hdom : (1 - (1 - (2 * Complex.I) •
        (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse)).domain =
        ((2 * Complex.I) • (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse).domain := by
      simp [LinearPMap.sub_domain]
    apply LinearPMap.ext hdom
    intro x hx hx'
    simp only [LinearPMap.sub_apply, LinearPMap.smul_apply]
    module
  have hrange : (1 - unitaryToPMap (cayleyUnitary T hT)).toFun.range = T.domain := by
    rw [hEq, linearPMap_range_smul _ (by norm_num), LinearPMap.inverse_range hplusker]
    simp [LinearPMap.add_domain]
  rw [inverseCayleyPMap_domain, hrange]

omit [CompleteSpace H] in
lemma inverseCayleyPMap_apply_on_range {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥) (a : (1 - unitaryToPMap u).domain) :
    inverseCayleyPMap u (⟨(1 - unitaryToPMap u) a, by
          rw [inverseCayleyPMap_domain u]
          exact LinearMap.mem_range_self _ a⟩) =
      Complex.I • (1 + unitaryToPMap u) a := by
  let y : (1 - unitaryToPMap u).inverse.domain :=
    ⟨(1 - unitaryToPMap u) a, by
      rw [LinearPMap.inverse_domain]
      exact LinearMap.mem_range_self _ a⟩
  have hy : (1 - unitaryToPMap u).inverse y = a := by
    apply LinearPMap.inverse_apply_eq hker
    rfl
  simp only [inverseCayleyPMap, LinearPMap.mul_def, LinearPMap.compRestricted_apply,
    LinearPMap.smul_apply]
  rw [hy]
  congr 2

lemma inverseCayleyPMap_cayleyUnitary {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) :
    inverseCayleyPMap (cayleyUnitary T hT) = T := by
  let u := cayleyUnitary T hT
  have hker : (1 - unitaryToPMap u).toFun.ker = ⊥ := by
    simpa [u] using cayleyUnitary_one_sub_ker_eq_bot hT
  have hdom : (inverseCayleyPMap u).domain = T.domain := by
    simpa [u] using inverseCayleyPMap_cayleyUnitary_domain hT
  have hEq : 1 - unitaryToPMap u =
      (2 * Complex.I) • (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse := by
    rw [show unitaryToPMap u = cayleyPMap T by
      simpa [u] using unitaryToPMap_cayleyUnitary_eq_cayleyPMap hT]
    rw [cayleyPMap_eq_one_sub hT]
    have hdom0 : (1 - (1 - (2 * Complex.I) •
        (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse)).domain =
        ((2 * Complex.I) • (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse).domain := by
      simp [LinearPMap.sub_domain]
    apply LinearPMap.ext hdom0
    intro q hq hq'
    simp only [LinearPMap.sub_apply, LinearPMap.smul_apply]
    module
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have hplusker : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have heq : T - (-Complex.I) • (1 : H →ₗ.[ℂ] H) = T + Complex.I • 1 := by
      exact LinearPMap.ext rfl fun q hq hq' => by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, neg_smul]
    rw [← heq]
    exact hres.1
  have hplusrange : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
    have heq : T - (-Complex.I) • (1 : H →ₗ.[ℂ] H) = T + Complex.I • 1 := by
      exact LinearPMap.ext rfl fun q hq hq' => by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, neg_smul]
    rw [← heq]
    exact hres.2.1
  apply LinearPMap.ext hdom
  intro x hx hx'
  have hxrange : (x : H) ∈ (1 - unitaryToPMap u).toFun.range := by
    rw [← inverseCayleyPMap_domain u]
    exact hx
  obtain ⟨a, ha⟩ := hxrange
  let ai : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse.domain :=
    ⟨(a : H), by
      rw [LinearPMap.inverse_domain, hplusrange]
      exact Submodule.mem_top⟩
  let zp : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse ai, by
      rw [← LinearPMap.inverse_range hplusker]
      exact LinearMap.mem_range_self _ ai⟩
  let zpT : T.domain :=
    ⟨(zp : H), by simpa [LinearPMap.add_domain] using zp.property⟩
  have hza : (T + Complex.I • (1 : H →ₗ.[ℂ] H)) zp = (a : H) := by
    exact linearPMap_comp_inverse_apply hplusker ai
  let al : (1 - unitaryToPMap u).domain :=
    ⟨(a : H), by
      exact a.property⟩
  let ar : ((2 * Complex.I) •
      (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse).domain :=
    ⟨(a : H), by
      rw [LinearPMap.smul_domain, LinearPMap.inverse_domain, hplusrange]
      exact Submodule.mem_top⟩
  obtain ⟨hEq_dom, hEq_fun⟩ := LinearPMap.dExt_iff.mp hEq
  have hEq_a := hEq_fun (x := al) (y := ar) rfl
  change (1 - unitaryToPMap u) al =
    (2 * Complex.I) • (T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse ai at hEq_a
  have hxval : (x : H) = (2 * Complex.I) • (zp : H) := by
    rw [← hEq_a]
    exact ha.symm
  let xi : (inverseCayleyPMap u).domain :=
    ⟨(1 - unitaryToPMap u) a, by
      rw [inverseCayleyPMap_domain u]
      exact LinearMap.mem_range_self _ a⟩
  have hxi : (⟨(x : H), hx⟩ : (inverseCayleyPMap u).domain) = xi := by
    apply Subtype.ext
    exact ha.symm
  let zt : T.domain :=
    ⟨(2 * Complex.I) • (zpT : H), by
      rw [← hxval]
      exact hx'⟩
  have hxt : (⟨(x : H), hx'⟩ : T.domain) = zt := by
    apply Subtype.ext
    exact hxval
  rw [hxi, inverseCayleyPMap_apply_on_range hker a]
  change Complex.I • ((a : H) + u (a : H)) = T ⟨(x : H), hx'⟩
  rw [hxt]
  dsimp [zt]
  change Complex.I • ((a : H) + u (a : H)) =
    T.toFun ((2 * Complex.I) • zpT)
  rw [T.toFun.map_smul]
  have hua : u (a : H) = T zpT - Complex.I • (zpT : H) := by
    have hEq_a' := hEq_a
    change (a : H) - u (a : H) = (2 * Complex.I) • (zpT : H) at hEq_a'
    have hza' := hza
    change T zpT + Complex.I • (zpT : H) = (a : H) at hza'
    have hua' : u (a : H) = (a : H) - (2 * Complex.I) • (zpT : H) := by
      rw [eq_sub_iff_add_eq]
      rw [← hEq_a']
      module
    calc
      u (a : H) = (a : H) - (2 * Complex.I) • (zpT : H) := hua'
      _ = T zpT - Complex.I • (zpT : H) := by
        rw [← hza']
        module
  rw [hua]
  have hza' := hza
  change T zpT + Complex.I • (zpT : H) = (a : H) at hza'
  rw [← hza']
  have hsum : (T zpT + Complex.I • (zpT : H)) +
      (T zpT - Complex.I • (zpT : H)) = (2 : ℂ) • T zpT := by
    module
  rw [hsum]
  simp [smul_smul, mul_comm]

omit [CompleteSpace H] in
@[nolint unusedArguments]
lemma cayley_inner_identity (u : H ≃ₗᵢ[ℂ] H) (a b : H) :
    ⟪Complex.I • (a + u a), b - u b⟫_ℂ =
      ⟪a - u a, Complex.I • (b + u b)⟫_ℂ := by
  have hub : ⟪u a, u b⟫_ℂ = ⟪a, b⟫_ℂ := by
    simp
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  rw [show starRingEnd ℂ Complex.I = -Complex.I by simp]
  rw [hub]
  ring

omit [CompleteSpace H] in
/-- The inverse Cayley operator is symmetric whenever `1 - u` is injective. -/
lemma inverseCayleyPMap_isSymmetric {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥) :
    (inverseCayleyPMap u).IsSymmetric := by
  intro x y
  have hxrange : (x : H) ∈ (1 - unitaryToPMap u).toFun.range := by
    rw [← inverseCayleyPMap_domain u]
    exact x.property
  have hyrange : (y : H) ∈ (1 - unitaryToPMap u).toFun.range := by
    rw [← inverseCayleyPMap_domain u]
    exact y.property
  obtain ⟨a, ha⟩ := hxrange
  obtain ⟨b, hb⟩ := hyrange
  let xa : (inverseCayleyPMap u).domain :=
    ⟨(1 - unitaryToPMap u) a, by
      rw [inverseCayleyPMap_domain u]
      exact LinearMap.mem_range_self _ a⟩
  let ya : (inverseCayleyPMap u).domain :=
    ⟨(1 - unitaryToPMap u) b, by
      rw [inverseCayleyPMap_domain u]
      exact LinearMap.mem_range_self _ b⟩
  have hxa : x = xa := by
    apply Subtype.ext
    exact ha.symm
  have hya : y = ya := by
    apply Subtype.ext
    exact hb.symm
  rw [hxa, hya, inverseCayleyPMap_apply_on_range hker a,
    inverseCayleyPMap_apply_on_range hker b]
  dsimp [xa, ya]
  change ⟪Complex.I • ((a : H) + u (a : H)), (b : H) - u (b : H)⟫_ℂ =
    ⟪(a : H) - u (a : H), Complex.I • ((b : H) + u (b : H))⟫_ℂ
  exact cayley_inner_identity u (a : H) (b : H)

omit [CompleteSpace H] in
lemma inverseCayleyPMap_add_I_apply_on_range {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥) (a : (1 - unitaryToPMap u).domain) :
    let x : (inverseCayleyPMap u).domain :=
      ⟨(1 - unitaryToPMap u) a, by
        rw [inverseCayleyPMap_domain u]
        exact LinearMap.mem_range_self _ a⟩
    inverseCayleyPMap u x + Complex.I • x = (2 * Complex.I) • (a : H) := by
  dsimp
  rw [inverseCayleyPMap_apply_on_range hker a]
  change Complex.I • ((a : H) + u (a : H)) + Complex.I • ((a : H) - u (a : H)) = _
  module

omit [CompleteSpace H] in
lemma inverseCayleyPMap_sub_I_apply_on_range {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥) (a : (1 - unitaryToPMap u).domain) :
    let x : (inverseCayleyPMap u).domain :=
      ⟨(1 - unitaryToPMap u) a, by
        rw [inverseCayleyPMap_domain u]
        exact LinearMap.mem_range_self _ a⟩
    inverseCayleyPMap u x - Complex.I • x = (2 * Complex.I) • u (a : H) := by
  dsimp
  rw [inverseCayleyPMap_apply_on_range hker a]
  change Complex.I • ((a : H) + u (a : H)) - Complex.I • ((a : H) - u (a : H)) = _
  module

omit [CompleteSpace H] in
lemma inverseCayleyPMap_hasDenseDomain {u : H ≃ₗᵢ[ℂ] H}
    (h_dense : Dense ((1 - unitaryToPMap u).toFun.range : Set H)) :
    (inverseCayleyPMap u).HasDenseDomain := by
  change Dense ((inverseCayleyPMap u).domain : Set H)
  rw [inverseCayleyPMap_domain u]
  exact h_dense

omit [CompleteSpace H] in
lemma inverseCayleyPMap_add_I_range_eq_top {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥) :
    (inverseCayleyPMap u + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro y
  let a : (1 - unitaryToPMap u).domain :=
    ⟨(2 * Complex.I)⁻¹ • y, by
      rw [one_sub_unitaryToPMap_domain u]
      exact Submodule.mem_top⟩
  let x : (inverseCayleyPMap u).domain :=
    ⟨(1 - unitaryToPMap u) a, by
      rw [inverseCayleyPMap_domain u]
      exact LinearMap.mem_range_self _ a⟩
  let xp : (inverseCayleyPMap u + Complex.I • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(x : H), by
      simp [LinearPMap.add_domain, x, inverseCayleyPMap_domain u]⟩
  refine ⟨xp, ?_⟩
  have hx := inverseCayleyPMap_add_I_apply_on_range hker a
  change inverseCayleyPMap u x + Complex.I • (x : H) = y
  rw [hx]
  change (2 * Complex.I) • ((2 * Complex.I)⁻¹ • y) = y
  rw [smul_smul]
  have hscalar : (2 : ℂ) * Complex.I * ((2 * Complex.I)⁻¹) = 1 := by
    exact mul_inv_cancel₀ (by norm_num)
  rw [hscalar, one_smul]

omit [CompleteSpace H] in
lemma inverseCayleyPMap_sub_I_range_eq_top {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥) :
    (inverseCayleyPMap u - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro y
  let a : (1 - unitaryToPMap u).domain :=
    ⟨u.symm ((2 * Complex.I)⁻¹ • y), by
      rw [one_sub_unitaryToPMap_domain u]
      exact Submodule.mem_top⟩
  let x : (inverseCayleyPMap u).domain :=
    ⟨(1 - unitaryToPMap u) a, by
      rw [inverseCayleyPMap_domain u]
      exact LinearMap.mem_range_self _ a⟩
  let xp : (inverseCayleyPMap u - Complex.I • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(x : H), by
      rw [LinearPMap.sub_domain, LinearPMap.smul_domain, LinearPMap.one_domain]
      exact ⟨x.property, Submodule.mem_top⟩⟩
  refine ⟨xp, ?_⟩
  have hx := inverseCayleyPMap_sub_I_apply_on_range hker a
  change inverseCayleyPMap u x - Complex.I • (x : H) = y
  rw [hx]
  change (2 * Complex.I) • u (u.symm ((2 * Complex.I)⁻¹ • y)) = y
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [smul_smul]
  have hscalar : (2 : ℂ) * Complex.I * ((2 * Complex.I)⁻¹) = 1 := by
    exact mul_inv_cancel₀ (by norm_num)
  rw [hscalar, one_smul]

/-! ## C. Self-adjointness of the inverse Cayley transform -/

/-- The standard hypotheses for taking an inverse Cayley transform. -/
structure CayleyUnitaryData (u : H ≃ₗᵢ[ℂ] H) : Prop where
  /-- The point `1` is not an eigenvalue of the unitary. -/
  one_sub_injective : (1 - unitaryToPMap u).toFun.ker = ⊥

lemma inverseCayleyPMap_isSelfAdjoint {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥)
    (h_dense : Dense ((1 - unitaryToPMap u).toFun.range : Set H)) :
    IsSelfAdjoint (inverseCayleyPMap u) := by
  apply LinearPMap.IsSymmetric.isSelfAdjoint_of_range_eq_top
    (inverseCayleyPMap_isSymmetric hker) (inverseCayleyPMap_hasDenseDomain h_dense)
  · exact inverseCayleyPMap_add_I_range_eq_top hker
  · exact inverseCayleyPMap_sub_I_range_eq_top hker

/-! ## D. Round trip with the forward Cayley transform -/

lemma cayleyContinuousLinearMap_inverseCayleyPMap_apply {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥)
    (h_dense : Dense ((1 - unitaryToPMap u).toFun.range : Set H)) (x : H) :
    cayleyContinuousLinearMap (inverseCayleyPMap u)
      (inverseCayleyPMap_isSelfAdjoint hker h_dense) x = u x := by
  let T : H →ₗ.[ℂ] H := inverseCayleyPMap u
  have hT : IsSelfAdjoint T := inverseCayleyPMap_isSelfAdjoint hker h_dense
  have hrange := inverseCayleyPMap_add_I_range_eq_top hker
  have hxrange : x ∈ (T + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range := by
    rw [hrange]
    exact Submodule.mem_top
  obtain ⟨y, hy⟩ := hxrange
  have hcalc := cayleyContinuousLinearMap_apply_of_mem_range hT y x hy
  rw [hcalc]
  have hyT : (y : H) ∈ T.domain := by
    simpa [LinearPMap.add_domain] using y.property
  have hyI : (y : H) ∈ (inverseCayleyPMap u).domain := hyT
  rw [inverseCayleyPMap_domain u] at hyI
  obtain ⟨a, ha⟩ := hyI
  let ya : (T + Complex.I • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(1 - unitaryToPMap u) a, by
      simp [LinearPMap.add_domain, T, inverseCayleyPMap_domain u]⟩
  have hya : y = ya := by
    apply Subtype.ext
    exact ha.symm
  rw [hya]
  have hsub : (T - Complex.I • (1 : H →ₗ.[ℂ] H)) ya =
      (2 * Complex.I) • u (a : H) := by
    change inverseCayleyPMap u
      (⟨(1 - unitaryToPMap u) a, by
        rw [inverseCayleyPMap_domain u]
        exact LinearMap.mem_range_self _ a⟩) - Complex.I •
        ((1 - unitaryToPMap u) a : H) = _
    rw [inverseCayleyPMap_sub_I_apply_on_range hker a]
  rw [hsub]
  have hadd := inverseCayleyPMap_add_I_apply_on_range hker a
  have hadd' : (T + Complex.I • (1 : H →ₗ.[ℂ] H)) ya =
      (2 * Complex.I) • (a : H) := by
    simpa [LinearPMap.add_apply, T, ya] using hadd
  change (2 * Complex.I) • u (a : H) = u x
  rw [← map_smul]
  congr 1
  rw [← hadd']
  rw [← hya]
  exact hy

lemma cayleyContinuousLinearMap_inverseCayleyPMap_eq {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥)
    (h_dense : Dense ((1 - unitaryToPMap u).toFun.range : Set H)) :
    cayleyContinuousLinearMap (inverseCayleyPMap u)
        (inverseCayleyPMap_isSelfAdjoint hker h_dense) =
      u.toLinearIsometry.toContinuousLinearMap := by
  ext x
  exact cayleyContinuousLinearMap_inverseCayleyPMap_apply hker h_dense x

lemma inverseCayleyPMap_isSelfAdjoint_of_ker_eq_bot {u : H ≃ₗᵢ[ℂ] H}
    (hker : (1 - unitaryToPMap u).toFun.ker = ⊥) :
    IsSelfAdjoint (inverseCayleyPMap u) :=
  inverseCayleyPMap_isSelfAdjoint hker
    (one_sub_unitaryToPMap_denseRange_of_ker_eq_bot hker)

lemma CayleyUnitaryData.inverse_isSelfAdjoint {u : H ≃ₗᵢ[ℂ] H}
    (hu : CayleyUnitaryData u) : IsSelfAdjoint (inverseCayleyPMap u) :=
  inverseCayleyPMap_isSelfAdjoint_of_ker_eq_bot hu.one_sub_injective

end QuantumMechanics

end
