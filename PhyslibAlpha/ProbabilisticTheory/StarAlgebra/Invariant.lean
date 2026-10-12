/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.QuasiLocal.Limit
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!

# Invariant states by Følner averaging

A state of a `*`-algebra with a group of automorphisms has invariant limit points, obtained by
averaging over larger and larger finite subsets of the group.

## i. Overview

A system in thermal equilibrium on an infinite crystal need not be translation invariant, because
the Gibbs states of finite boxes see the boundary of the box. Averaging a state `φ` over the
translates `α_g` with `g` in a finite set `F` gives the state `φ_F = |F|⁻¹ ∑_{g ∈ F} φ ∘ α_g`.
When the sets `F` become invariant under right translation, `|F h Δ F| / |F| → 0` for every `h`
(a Følner condition), the averaged states become invariant: `φ_F ∘ α_h - φ_F → 0`. If the values
of the averaged states on each observable are bounded, they have limit points along an
ultrafilter, and every limit point is an invariant state.

Nothing is assumed about the algebra beyond a bound `a* a + p = c · 1` with `p` a sum of squares
for each observable `a`. The statement therefore holds for the quasi-local algebra of any net,
quantum or classical, and for every state, in particular for the thermodynamic limit states of a
Gibbs ensemble.

## ii. Key results

- `IsBounded` : an observable is bounded by a multiple of the identity up to a sum of squares.
- `AlgState.limit` : the ultrafilter limit of a bounded net of states.
- `AlgState.average` : the average of a state over a finite set of automorphisms.
- `AlgState.invariantLimit` : the limit of Følner averages.
- `AlgState.invariantLimit_invariant` : the limit state is invariant under the group.

## iii. Table of contents

- A. Bounded observables
- B. Limits of states
- C. Averages over a finite set of automorphisms
- D. Invariance of Følner limits
- E. Boundedness in the quasi-local algebra

## iv. References

* F. Greenleaf, Invariant Means on Topological Groups.
* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Section 4.3.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open Filter Topology ProbabilisticTheory.QuasiLocal
open scoped ComplexOrder

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-! ## A. Bounded observables -/

/-- An observable `a` is **bounded** if some multiple `c · 1` of the identity exceeds `a* a` by a
sum of squares. -/
def IsBounded (a : A) : Prop :=
  ∃ c : ℝ, ∃ p ∈ sumSq A, star a * a + p = (c : ℂ) • (1 : A)

/-- **Every state is bounded on a bounded observable**, by the same constant. -/
lemma AlgState.norm_sq_le_of_isBounded {a : A} {c : ℝ} {p : A} (hp : p ∈ sumSq A)
    (h : star a * a + p = (c : ℂ) • (1 : A)) (ω : AlgState A) : ‖ω a‖ ^ 2 ≤ c := by
  have h1 := ω.normSq_le a
  have h2 := ω.nonneg_of_mem_sumSq hp
  have h3 : ω (star a * a) = (c : ℂ) - ω p := by
    have := congrArg ω h
    rw [ω.map_add, ω.map_smul, ω.map_one, mul_one] at this
    linear_combination this
  have h4 : ((‖ω a‖ ^ 2 : ℝ) : ℂ) ≤ (c : ℂ) := by
    calc _ ≤ _ := h1
      _ = _ := h3
      _ ≤ _ := sub_le_self _ h2
  exact Complex.real_le_real.1 h4

omit [StarModule ℂ A] in
/-- A star-algebra equivalence maps sums of squares to sums of squares. -/
lemma sumSq_map {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B]
    (σ : A ≃⋆ₐ[ℂ] B) {p : A} (hp : p ∈ sumSq A) : σ p ∈ sumSq B := by
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact AddSubmonoid.subset_closure ⟨σ s, by rw [map_mul, map_star]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy

omit [StarModule ℂ A] in
/-- A star-algebra automorphism preserves boundedness. -/
lemma IsBounded.map {a : A} (ha : IsBounded a) (σ : A ≃⋆ₐ[ℂ] A) : IsBounded (σ a) := by
  obtain ⟨c, p, hp, h⟩ := ha
  refine ⟨c, σ p, sumSq_map σ hp, ?_⟩
  have := congrArg σ h
  rwa [map_add, map_mul, map_star, map_smul, map_one] at this

/-! ## B. Limits of states -/

section Limit

variable {ι : Type*}

/-- The values of a bounded net of states on an observable have a limit along an ultrafilter. -/
lemma exists_tendsto_state (ψ : ι → AlgState A) (𝒰 : Ultrafilter ι)
    (hb : ∀ a : A, ∃ c : ℝ, ∀ i, ‖ψ i a‖ ≤ c) (a : A) :
    ∃ z, Tendsto (fun i => ψ i a) 𝒰 (𝓝 z) := by
  obtain ⟨c, hc⟩ := hb a
  obtain ⟨z, -, hz⟩ := (isCompact_closedBall (0 : ℂ) c).ultrafilter_le_nhds'
    (𝒰.map fun i => ψ i a)
    (Filter.eventually_map.2 (Filter.Eventually.of_forall fun i => by
      simpa [mem_closedBall_zero_iff] using hc i))
  exact ⟨z, hz⟩

/-- **The limit of a bounded net of states along an ultrafilter** is a state. -/
def AlgState.limit (ψ : ι → AlgState A) (𝒰 : Ultrafilter ι)
    (hb : ∀ a : A, ∃ c : ℝ, ∀ i, ‖ψ i a‖ ≤ c) : AlgState A where
  toLinearMap :=
    { toFun a := Classical.choose (exists_tendsto_state ψ 𝒰 hb a)
      map_add' a b := by
        refine tendsto_nhds_unique (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb (a + b)))
          ?_
        have : (fun i => ψ i (a + b)) = fun i => ψ i a + ψ i b := by
          funext i; exact (ψ i).map_add a b
        rw [this]
        exact (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb a)).add
          (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb b))
      map_smul' c a := by
        refine tendsto_nhds_unique (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb (c • a)))
          ?_
        have : (fun i => ψ i (c • a)) = fun i => c * ψ i a := by
          funext i; exact (ψ i).map_smul c a
        rw [this]
        exact (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb a)).const_mul c }
  map_one' := by
    refine tendsto_nhds_unique (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb 1)) ?_
    exact tendsto_const_nhds.congr fun i => ((ψ i).map_one).symm
  map_star' a := by
    refine tendsto_nhds_unique (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb (star a))) ?_
    have : (fun i => ψ i (star a)) = fun i => star (ψ i a) := by
      funext i; exact (ψ i).map_star a
    rw [this]
    exact ((continuous_star).tendsto _).comp
      (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb a))
  nonneg' a := by
    refine ge_of_tendsto
      (Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb (star a * a))) ?_
    exact Filter.Eventually.of_forall fun i => (ψ i).nonneg a

lemma AlgState.tendsto_limit (ψ : ι → AlgState A) (𝒰 : Ultrafilter ι)
    (hb : ∀ a : A, ∃ c : ℝ, ∀ i, ‖ψ i a‖ ≤ c) (a : A) :
    Tendsto (fun i => ψ i a) 𝒰 (𝓝 (AlgState.limit ψ 𝒰 hb a)) :=
  Classical.choose_spec (exists_tendsto_state ψ 𝒰 hb a)

end Limit

/-! ## C. Averages over a finite set of automorphisms -/

section Average

variable {Γ : Type*}

omit [StarModule ℂ A] in
lemma starAlgEquiv_smul (σ : A ≃⋆ₐ[ℂ] A) (c : ℂ) (a : A) : σ (c • a) = c • σ a :=
  σ.map_smul' c a

/-- The linear functional `a ↦ |F|⁻¹ ∑_{g ∈ F} φ (α g a)`. -/
def averageMap (φ : AlgState A) (α : Γ → (A ≃⋆ₐ[ℂ] A)) (F : Finset Γ) : A →ₗ[ℂ] ℂ where
  toFun a := ((F.card : ℂ))⁻¹ * ∑ g ∈ F, φ (α g a)
  map_add' a b := by
    simp only [map_add, φ.map_add, Finset.sum_add_distrib, mul_add]
  map_smul' c a := by
    simp only [starAlgEquiv_smul, φ.map_smul, ← Finset.mul_sum, RingHom.id_apply, smul_eq_mul]
    ring

lemma averageMap_apply (φ : AlgState A) (α : Γ → (A ≃⋆ₐ[ℂ] A)) (F : Finset Γ) (a : A) :
    averageMap φ α F a = ((F.card : ℂ))⁻¹ * ∑ g ∈ F, φ (α g a) := rfl

/-- **The average of a state over a finite set of automorphisms** is a state. -/
def AlgState.average (φ : AlgState A) (α : Γ → (A ≃⋆ₐ[ℂ] A)) (F : Finset Γ)
    (hF : F.Nonempty) : AlgState A where
  toLinearMap := averageMap φ α F
  map_one' := by
    have hc : (F.card : ℂ) ≠ 0 := by exact_mod_cast hF.card_pos.ne'
    rw [averageMap_apply]
    have h1 : ∀ g, φ (α g 1) = 1 := fun g => by rw [_root_.map_one, φ.map_one]
    simp only [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hc
  map_star' a := by
    have hr : star ((F.card : ℂ))⁻¹ = ((F.card : ℂ))⁻¹ := by simp
    rw [averageMap_apply, averageMap_apply, star_mul', hr, star_sum]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [StarHomClass.map_star, φ.map_star]
  nonneg' a := by
    rw [averageMap_apply]
    refine mul_nonneg ?_ (Finset.sum_nonneg fun g _ => ?_)
    · exact_mod_cast inv_nonneg.2 (Nat.cast_nonneg _)
    · rw [_root_.map_mul, StarHomClass.map_star]
      exact φ.nonneg _

lemma AlgState.average_apply (φ : AlgState A) (α : Γ → (A ≃⋆ₐ[ℂ] A)) (F : Finset Γ)
    (hF : F.Nonempty) (a : A) :
    φ.average α F hF a = ((F.card : ℂ))⁻¹ * ∑ g ∈ F, φ (α g a) := rfl

end Average

/-! ## D. Invariance of Følner limits -/

section Folner

variable {Γ : Type*} [Group Γ] [DecidableEq Γ] {ι : Type*}

/-- The linear functional `a ↦ φ (σ a)`. -/
def compMap (φ : AlgState A) (σ : A ≃⋆ₐ[ℂ] A) : A →ₗ[ℂ] ℂ where
  toFun a := φ (σ a)
  map_add' a b := by rw [_root_.map_add, φ.map_add]
  map_smul' c a := by rw [starAlgEquiv_smul, φ.map_smul]; rfl

lemma compMap_apply (φ : AlgState A) (σ : A ≃⋆ₐ[ℂ] A) (a : A) : compMap φ σ a = φ (σ a) := rfl

/-- **The composition of a state with an automorphism** is a state. -/
def AlgState.comp (φ : AlgState A) (σ : A ≃⋆ₐ[ℂ] A) : AlgState A where
  toLinearMap := compMap φ σ
  map_one' := by rw [compMap_apply, _root_.map_one, φ.map_one]
  map_star' a := by
    rw [compMap_apply, compMap_apply, StarHomClass.map_star, φ.map_star]
  nonneg' a := by
    rw [compMap_apply, _root_.map_mul, StarHomClass.map_star]
    exact φ.nonneg _

lemma AlgState.comp_apply (φ : AlgState A) (σ : A ≃⋆ₐ[ℂ] A) (a : A) : φ.comp σ a = φ (σ a) :=
  rfl

/-- The bound on a state on a bounded observable, as a norm bound. -/
lemma AlgState.norm_le_of_isBounded {a : A} {c : ℝ} {p : A} (hp : p ∈ sumSq A)
    (h : star a * a + p = (c : ℂ) • (1 : A)) (ω : AlgState A) : ‖ω a‖ ≤ c + 1 := by
  have := AlgState.norm_sq_le_of_isBounded hp h ω
  nlinarith [sq_nonneg (‖ω a‖ - 1), norm_nonneg (ω a)]

omit [Group Γ] in
/-- A difference of two sums of a bounded function is bounded by the size of the symmetric
difference of the index sets. -/
lemma norm_sum_sub_le (f : Γ → ℂ) (C : ℝ) (hf : ∀ k, ‖f k‖ ≤ C) (S T : Finset Γ) :
    ‖∑ k ∈ S, f k - ∑ k ∈ T, f k‖ ≤ ((S \ T).card + (T \ S).card) * C := by
  have e1 := Finset.sum_inter_add_sum_sdiff S T f
  have e2 := Finset.sum_inter_add_sum_sdiff T S f
  rw [Finset.inter_comm] at e2
  have e : ∑ k ∈ S, f k - ∑ k ∈ T, f k = ∑ k ∈ S \ T, f k - ∑ k ∈ T \ S, f k := by
    rw [← e1, ← e2]; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖∑ k ∈ S \ T, f k‖ ≤ (S \ T).card * C :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hf k).trans (by simp))
  have h2 : ‖∑ k ∈ T \ S, f k‖ ≤ (T \ S).card * C :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hf k).trans (by simp))
  linarith

/-- The finite sets `F i` are **asymptotically invariant under right translation** along an
ultrafilter (a Følner condition): `|F h Δ F| / |F| → 0` for every `h`. -/
def IsRightFolner (F : ι → Finset Γ) (𝒰 : Ultrafilter ι) : Prop :=
  ∀ h : Γ, Tendsto (fun i => ((((F i).image (· * h)) \ F i).card +
    (F i \ (F i).image (· * h)).card : ℝ) / (F i).card) 𝒰 (𝓝 0)

variable (α : Γ →* (A ≃⋆ₐ[ℂ] A)) (F : ι → Finset Γ) (hne : ∀ i, (F i).Nonempty)

omit [DecidableEq Γ] in
/-- The averaged states of a state over the sets `F i` are bounded on every observable. -/
lemma average_bounded (φ : AlgState A) (hb : ∀ a : A, IsBounded a) (a : A) :
    ∃ c : ℝ, ∀ i, ‖(φ.average (fun g => α g) (F i) (hne i)) a‖ ≤ c := by
  obtain ⟨c, p, hp, h⟩ := hb a
  refine ⟨c + 1, fun i => ?_⟩
  rw [AlgState.average_apply, norm_mul]
  have hterm : ∀ g, ‖φ (α g a)‖ ≤ c + 1 := fun g => by
    have h' := congrArg (α g) h
    rw [_root_.map_add, _root_.map_mul, StarHomClass.map_star, starAlgEquiv_smul,
      _root_.map_one] at h'
    exact AlgState.norm_le_of_isBounded (sumSq_map (α g) hp) h' φ
  have hn : (F i).card ≠ 0 := (hne i).card_pos.ne'
  have hsum : ‖∑ g ∈ F i, φ (α g a)‖ ≤ (F i).card * (c + 1) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun g _ => hterm g).trans (by simp [mul_add]))
  have hpos : (0 : ℝ) < (F i).card := by exact_mod_cast (hne i).card_pos
  calc ‖((F i).card : ℂ)⁻¹‖ * ‖∑ g ∈ F i, φ (α g a)‖
      ≤ ((F i).card : ℝ)⁻¹ * ((F i).card * (c + 1)) := by
        rw [norm_inv, Complex.norm_natCast]
        gcongr
    _ = c + 1 := by field_simp

/-- **The Følner limit of a state**: the ultrafilter limit of its averages over the sets `F i`. -/
def AlgState.invariantLimit (φ : AlgState A) (hb : ∀ a : A, IsBounded a) (𝒰 : Ultrafilter ι) :
    AlgState A :=
  AlgState.limit (fun i => φ.average (fun g => α g) (F i) (hne i)) 𝒰
    (average_bounded α F hne φ hb)

/-- **The Følner limit of a state is invariant.** When the sets `F i` are asymptotically invariant
under right translation along `𝒰`, every limit of the averages of a state over them is invariant
under the group. -/
lemma AlgState.invariantLimit_invariant (φ : AlgState A) (hb : ∀ a : A, IsBounded a)
    (𝒰 : Ultrafilter ι) (hF : IsRightFolner F 𝒰) (h : Γ) (a : A) :
    AlgState.invariantLimit α F hne φ hb 𝒰 (α h a) = AlgState.invariantLimit α F hne φ hb 𝒰 a := by
  set ψ : ι → AlgState A := fun i => φ.average (fun g => α g) (F i) (hne i) with hψ
  have t1 := AlgState.tendsto_limit ψ 𝒰 (average_bounded α F hne φ hb) (α h a)
  have t2 := AlgState.tendsto_limit ψ 𝒰 (average_bounded α F hne φ hb) a
  obtain ⟨c, p, hp, hc⟩ := hb a
  have hterm : ∀ k, ‖φ (α k a)‖ ≤ c + 1 := fun k => by
    have h' := congrArg (α k) hc
    rw [_root_.map_add, _root_.map_mul, StarHomClass.map_star, starAlgEquiv_smul,
      _root_.map_one] at h'
    exact AlgState.norm_le_of_isBounded (sumSq_map (α k) hp) h' φ
  have hdiff : ∀ i, ‖ψ i (α h a) - ψ i a‖ ≤
      ((((F i).image (· * h)) \ F i).card + (F i \ (F i).image (· * h)).card : ℝ) /
        (F i).card * (c + 1) := by
    intro i
    have hpos : (0 : ℝ) < (F i).card := by exact_mod_cast (hne i).card_pos
    have hshift : ∑ g ∈ F i, φ (α g (α h a)) = ∑ k ∈ (F i).image (· * h), φ (α k a) := by
      rw [Finset.sum_image (fun x _ y _ hxy => mul_right_cancel hxy)]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [_root_.map_mul]
      rfl
    have e : ψ i (α h a) - ψ i a = ((F i).card : ℂ)⁻¹ *
        (∑ k ∈ (F i).image (· * h), φ (α k a) - ∑ k ∈ F i, φ (α k a)) := by
      simp only [hψ, AlgState.average_apply, hshift]
      ring
    rw [e, norm_mul, norm_inv, Complex.norm_natCast, div_mul_eq_mul_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (norm_sum_sub_le _ _ hterm _ _) hpos.le
  have t3 : Tendsto (fun i => ψ i (α h a) - ψ i a) 𝒰 (𝓝 0) := by
    refine squeeze_zero_norm hdiff ?_
    simpa using (hF h).mul_const (c + 1)
  have t4 := t1.sub t2
  have := tendsto_nhds_unique t4 t3
  exact sub_eq_zero.1 this

end Folner

/-! ## E. Boundedness in the quasi-local algebra -/

section Quasilocal

variable {S : Type*} [DecidableEq S] {N : AlgebraNet S}

omit [StarModule ℂ A] in
/-- A star-algebra homomorphism maps sums of squares to sums of squares. -/
lemma sumSq_map_hom {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B]
    (σ : A →⋆ₐ[ℂ] B) {p : A} (hp : p ∈ sumSq A) : σ p ∈ sumSq B := by
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact AddSubmonoid.subset_closure ⟨σ s, by rw [_root_.map_mul, StarHomClass.map_star]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [_root_.map_add]; exact add_mem hx hy

omit [DecidableEq S] in
/-- **Every observable of the quasi-local algebra of a locally bounded net is bounded.** -/
lemma AlgebraNet.isBounded_of_isLocallyBounded (hb : N.IsLocallyBounded) (x : N.Quasilocal) :
    IsBounded x := by
  obtain ⟨X, a, rfl⟩ := N.exists_of x
  obtain ⟨c, p, hp, h⟩ := hb X a
  refine ⟨c, N.of X p, sumSq_map_hom (N.of X) hp, ?_⟩
  have := congrArg (N.of X) h
  rwa [_root_.map_add, _root_.map_mul, StarHomClass.map_star, map_smul, _root_.map_one] at this

end Quasilocal

end ProbabilisticTheory

end
