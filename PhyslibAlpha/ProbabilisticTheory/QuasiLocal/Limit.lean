/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.QuasiLocal.State
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!

# Limit states of the quasi-local algebra

A net of local states, one for each finite region, has limit points that are states of the
quasi-local algebra.

## i. Overview

Let `ω_Λ` be a state of the algebra of the finite region `Λ`, for every `Λ`. The expectation value
of a fixed local observable `a`, taken in the larger and larger regions `Λ`, is a net of complex
numbers. If every local observable has a bounded such net, the net has a limit along every
ultrafilter finer than the filter of large regions, by compactness of closed balls in `ℂ`. The
limits are compatible, normalized, Hermitian and positive, so they form a `LocalStateFamily`, and
hence a state of the quasi-local algebra.

Boundedness is expressed without any norm: an observable `a` is *locally bounded* if some
multiple `c · 1` of the identity exceeds `a* a` by a sum of squares. In a matrix algebra this
holds with `c = ‖a‖²`. Each state then satisfies `|ω(a)|² ≤ ω(a* a) ≤ c`, by the Cauchy–Schwarz
inequality for states.

Nothing is assumed about the nature of the local states: they may be Gibbs states with any
boundary condition. Different ultrafilters can give different limit states, which is how phase
coexistence appears.

## ii. Key results

- `AlgState.normSq_le` : the Cauchy–Schwarz inequality `|ω(a)|² ≤ ω(a* a)`.
- `AlgebraNet.IsLocallyBounded` : every local observable is bounded by a multiple of the identity.
- `limitFamily` : the ultrafilter limit of a net of local states, as a compatible family.
- `limitState` : the limit state of the quasi-local algebra.
- `limitState_of` : its value on a local observable is the limit of the local expectations.

## iii. Table of contents

- A. The Cauchy–Schwarz inequality and sums of squares
- B. Local boundedness
- C. The ultrafilter limit

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.2.3 (existence of limit Gibbs states by weak-⋆ compactness).

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

namespace QuasiLocal

open Filter Topology
open scoped ComplexOrder

/-! ## A. The Cauchy–Schwarz inequality and sums of squares -/

section Squares

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- The sums of squares `∑ s_i* s_i` of a `*`-algebra. -/
def sumSq (A : Type*) [Ring A] [StarRing A] : AddSubmonoid A :=
  AddSubmonoid.closure (Set.range fun s : A => star s * s)

/-- **The Cauchy–Schwarz inequality for states**: `|ω(a)|² ≤ ω(a* a)`. -/
lemma _root_.ProbabilisticTheory.AlgState.normSq_le (ω : AlgState A) (a : A) :
    ((‖ω a‖ ^ 2 : ℝ) : ℂ) ≤ ω (star a * a) := by
  set z := ω a with hz
  have h := ω.nonneg (a - z • (1 : A))
  have hexp : star (a - z • (1 : A)) * (a - z • (1 : A)) =
      star a * a - z • star a - star z • a + (star z * z) • (1 : A) := by
    simp only [star_sub, star_smul, star_one, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_sub]
    module
  rw [hexp] at h
  have e : ω (star a * a - z • star a - star z • a + (star z * z) • (1 : A)) =
      ω (star a * a) - z * star z - star z * z + star z * z := by
    have hl : ∀ x, ω x = ω.toLinearMap x := fun _ => rfl
    have hs : ω.toLinearMap (star a) = star z := by rw [← hl, ω.map_star]
    simp only [hl, map_sub, map_add, map_smul, smul_eq_mul, ω.map_one', hs, mul_one]
    rw [show ω.toLinearMap a = z from rfl]
  rw [e] at h
  have hn : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : ω (star a * a) - z * star z - star z * z + star z * z =
      ω (star a * a) - ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hn, mul_comm (star z) z, hn]; ring
  rw [h2] at h
  exact sub_nonneg.1 h

end Squares

/-! ## B. Local boundedness -/

variable {S : Type*} [DecidableEq S] (N : AlgebraNet S)

/-- **Local boundedness**: for every local observable `a` some multiple `c · 1` of the identity
exceeds `a* a` by a sum of squares. -/
def AlgebraNet.IsLocallyBounded : Prop :=
  ∀ (X : Finset S) (a : N.A X), ∃ c : ℝ, ∃ p ∈ sumSq (N.A X),
    star a * a + p = (c : ℂ) • (1 : N.A X)

variable {N}

/-- A state is nonnegative on sums of squares. -/
lemma _root_.ProbabilisticTheory.AlgState.nonneg_of_mem_sumSq
    {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (ω : AlgState A)
    {p : A} (hp : p ∈ sumSq A) : 0 ≤ ω p := by
  induction hp using AddSubmonoid.closure_induction with
  | mem x hx => obtain ⟨s, rfl⟩ := hx; exact ω.nonneg s
  | zero => simp [show ω 0 = 0 from map_zero ω.toLinearMap]
  | add x y _ _ hx hy => rw [ω.map_add]; exact add_nonneg hx hy

omit [DecidableEq S] in
/-- **The expectation of a locally bounded observable in any larger region is bounded.** -/
lemma AlgebraNet.norm_sq_le (hb : N.IsLocallyBounded) {X Λ : Finset S} (h : X ≤ Λ)
    (ω : AlgState (N.A Λ)) (a : N.A X) :
    ∃ c : ℝ, ‖ω (N.incl h a)‖ ^ 2 ≤ c ∧ ∀ Λ' (h' : X ≤ Λ') (ω' : AlgState (N.A Λ')),
      ‖ω' (N.incl h' a)‖ ^ 2 ≤ c := by
  obtain ⟨c, p, hp, hc⟩ := hb X a
  have key : ∀ Λ' (h' : X ≤ Λ') (ω' : AlgState (N.A Λ')), ‖ω' (N.incl h' a)‖ ^ 2 ≤ c := by
    intro Λ' h' ω'
    have h1 := ω'.normSq_le (N.incl h' a)
    have h2 := ω'.nonneg_of_mem_sumSq (A := N.A Λ') (p := N.incl h' p) (by
      clear h1 hc
      revert p
      intro p hp
      induction hp using AddSubmonoid.closure_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        exact AddSubmonoid.subset_closure ⟨N.incl h' s, by simp only [map_mul, map_star]⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy)
    have h3 : ω' (N.incl h' (star a * a)) = (c : ℂ) - ω' (N.incl h' p) := by
      have := congrArg (fun x => ω' (N.incl h' x)) hc
      simp only [map_add, map_smul, map_one, ω'.map_add, ω'.map_smul, ω'.map_one,
        mul_one] at this
      rw [← this]; ring
    rw [map_mul, map_star] at h3
    have h4 : ((‖ω' (N.incl h' a)‖ ^ 2 : ℝ) : ℂ) ≤ (c : ℂ) := by
      calc _ ≤ _ := h1
        _ = _ := h3
        _ ≤ _ := sub_le_self _ h2
    exact Complex.real_le_real.1 h4
  exact ⟨c, key Λ h ω, key⟩

/-! ## C. The ultrafilter limit -/

variable (ω : ∀ Λ : Finset S, AlgState (N.A Λ))

/-- The expectation of a local observable `a` of the region `X` in the region `Λ`, zero if `Λ`
does not contain `X`. -/
def localSeq (X : Finset S) (a : N.A X) (Λ : Finset S) : ℂ :=
  if h : X ≤ Λ then ω Λ (N.incl h a) else 0

lemma localSeq_eq (X : Finset S) (a : N.A X) {Λ : Finset S} (h : X ≤ Λ) :
    localSeq ω X a Λ = ω Λ (N.incl h a) := by simp [localSeq, h]

variable {𝒰 : Ultrafilter (Finset S)}

/-- The expectations of a local observable have a limit along a fine ultrafilter. -/
lemma exists_tendsto_localSeq (hb : N.IsLocallyBounded) (h𝒰 : (𝒰 : Filter (Finset S)) ≤ atTop)
    (X : Finset S) (a : N.A X) : ∃ z, Tendsto (localSeq ω X a) 𝒰 (𝓝 z) := by
  obtain ⟨c, -, hc⟩ := N.norm_sq_le hb (le_refl X) (ω X) a
  have hev : ∀ᶠ Λ in (𝒰 : Filter (Finset S)), X ≤ Λ := h𝒰 (eventually_ge_atTop X)
  have hmem : ∀ᶠ Λ in (𝒰 : Filter (Finset S)), localSeq ω X a Λ ∈ Metric.closedBall (0 : ℂ)
      (c + 1) := by
    filter_upwards [hev] with Λ hΛ
    rw [localSeq_eq ω X a hΛ, mem_closedBall_zero_iff]
    have := hc Λ hΛ (ω Λ)
    nlinarith [norm_nonneg (ω Λ (N.incl hΛ a)), sq_nonneg (‖ω Λ (N.incl hΛ a)‖ - 1)]
  obtain ⟨z, -, hz⟩ := (isCompact_closedBall (0 : ℂ) (c + 1)).ultrafilter_le_nhds'
    (𝒰.map (localSeq ω X a)) (Filter.eventually_map.2 hmem)
  exact ⟨z, hz⟩

variable (hb : N.IsLocallyBounded) (h𝒰 : (𝒰 : Filter (Finset S)) ≤ atTop)

/-- The limit along the ultrafilter of the expectations of a local observable. -/
def limitValue (X : Finset S) (a : N.A X) : ℂ :=
  Classical.choose (exists_tendsto_localSeq ω hb h𝒰 X a)

lemma tendsto_limitValue (X : Finset S) (a : N.A X) :
    Tendsto (localSeq ω X a) 𝒰 (𝓝 (limitValue ω hb h𝒰 X a)) :=
  Classical.choose_spec (exists_tendsto_localSeq ω hb h𝒰 X a)

/-- **The limit of a net of local states along an ultrafilter** is a compatible family of local
states. -/
def limitFamily : LocalStateFamily N where
  state X :=
    { toFun := limitValue ω hb h𝒰 X
      map_add' a b := by
        have : localSeq ω X (a + b) = localSeq ω X a + localSeq ω X b := by
          funext Λ
          by_cases h : X ≤ Λ <;> simp [localSeq, h, map_add, (ω Λ).map_add]
        refine tendsto_nhds_unique (tendsto_limitValue ω hb h𝒰 X (a + b)) ?_
        rw [this]
        exact (tendsto_limitValue ω hb h𝒰 X a).add (tendsto_limitValue ω hb h𝒰 X b)
      map_smul' c a := by
        have : localSeq ω X (c • a) = c • localSeq ω X a := by
          funext Λ
          by_cases h : X ≤ Λ <;> simp [localSeq, h, map_smul, (ω Λ).map_smul]
        refine tendsto_nhds_unique (tendsto_limitValue ω hb h𝒰 X (c • a)) ?_
        rw [this]
        exact (tendsto_limitValue ω hb h𝒰 X a).const_smul c }
  compat {X Y} h a := by
    refine tendsto_nhds_unique (tendsto_limitValue ω hb h𝒰 Y (N.incl h a)) ?_
    refine (tendsto_limitValue ω hb h𝒰 X a).congr' ?_
    filter_upwards [h𝒰 (eventually_ge_atTop Y)] with Λ hΛ
    rw [localSeq_eq ω X a (h.trans hΛ), localSeq_eq ω Y _ hΛ, ← N.incl_trans]
  map_one X := by
    refine tendsto_nhds_unique (tendsto_limitValue ω hb h𝒰 X 1) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h𝒰 (eventually_ge_atTop X)] with Λ hΛ
    rw [localSeq_eq ω X _ hΛ, map_one, (ω Λ).map_one]
  map_star X a := by
    refine tendsto_nhds_unique (tendsto_limitValue ω hb h𝒰 X (star a)) ?_
    have : localSeq ω X (star a) = fun Λ => star (localSeq ω X a Λ) := by
      funext Λ
      by_cases h : X ≤ Λ <;> simp [localSeq, h, map_star, (ω Λ).map_star]
    rw [this]
    exact ((continuous_star).tendsto _).comp (tendsto_limitValue ω hb h𝒰 X a)
  nonneg X a := by
    refine ge_of_tendsto (tendsto_limitValue ω hb h𝒰 X (star a * a)) ?_
    filter_upwards [h𝒰 (eventually_ge_atTop X)] with Λ hΛ
    rw [localSeq_eq ω X _ hΛ, map_mul, map_star]
    exact (ω Λ).nonneg _

/-- **The limit state** of a net of local states along an ultrafilter: a state of the
quasi-local algebra. -/
def limitState : AlgState N.Quasilocal := (limitFamily ω hb h𝒰).toAlgState

/-- The limit state on a local observable is the limit of the local expectations. -/
lemma limitState_of (X : Finset S) (a : N.A X) :
    Tendsto (fun Λ => localSeq ω X a Λ) 𝒰 (𝓝 (limitState ω hb h𝒰 (N.of X a))) :=
  tendsto_limitValue ω hb h𝒰 X a

end QuasiLocal

end ProbabilisticTheory

end
