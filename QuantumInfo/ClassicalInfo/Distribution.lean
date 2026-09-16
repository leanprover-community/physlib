/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ClassicalInfo.Prob

public import Mathlib.Analysis.Convex.Combination

/-! # Distributions on finite sets

We define the type `Distribution α` on a `Fintype α`. By restricting ourselves to distributoins on
finite types, a lot of notation and casts are greatly simplified.
This suffices for (most) finite-dimensional quantum theory.

-/

@[expose] public section

noncomputable section
open NNReal
open Classical
open BigOperators

/--
We define our own (discrete) probability distribution notion here, instead
of using `PMF` from Mathlib, because that uses ENNReals everywhere to maintain compatibility
with `MeasureTheory.Measure`.

The probabilities internal to a Distribution are NNReals. This lets us more easily
write the statement that they sum to 1, since NNReals can be added. (Probabilities,
on their own, cannot.) But the FunLike instance gives `Prob` out, which carry the
information that they are all in the range [0,1].
-/
def ProbDistribution (α : Type u) [Fintype α] : Type u :=
  { f : α → Prob // Finset.sum Finset.univ (fun i ↦ (f i : ℝ)) = 1 }

namespace ProbDistribution

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Make a distribution, proving only that the values are nonnegative and that the
sum is 1. The fact that the values are at most 1 is derived as a consequence. -/
def mk' (f : α → ℝ) (h₁ : ∀i, 0 ≤ f i) (hN : ∑ i, f i = 1) : ProbDistribution α :=
  have h₃ : ∀x, f x ≤ 1 := by
    intro x
    simp [← hN, Fintype.sum_eq_sum_compl_add x]
    exact Finset.sum_nonneg' h₁
  ⟨ fun i ↦ ⟨f i, ⟨h₁ i, h₃ i⟩⟩, hN⟩

instance instFunLikeProb : FunLike (ProbDistribution α) α Prob where
  coe p a := p.1 a
  coe_injective _ _ h :=
    Subtype.ext <| funext fun v ↦ by
      simpa only [Subtype.mk.injEq, coe_inj] using congrFun h v

@[simp]
theorem normalized (d : ProbDistribution α) : Finset.sum Finset.univ (fun i ↦ (d i : ℝ)) = 1 :=
  d.2

abbrev prob (d : ProbDistribution α) := (d : α → Prob)

@[simp]
theorem fun_eq_val (d : ProbDistribution α) : d.val = d :=
  rfl

@[simp]
theorem funlike_apply (d : α → Prob) (h : _) (x : α) :
    DFunLike.coe (self := instFunLikeProb) ⟨d, h⟩ x = d x :=
  rfl

@[ext]
theorem ext {p q : ProbDistribution α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

/-- A distribution provides a witness that d is nonempty. -/
theorem nonempty (d : ProbDistribution α) : Nonempty α := by
  by_contra h
  simpa [not_nonempty_iff.mp h] using d.2

/-- Make an constant distribution: supported on a single element. This is also called, variously, a
 "One-point distribution", a "Degenerate distribution", a "Deterministic distribution", a
 "Delta function", or a "Point mass distribution". -/
def constant (x : α) : ProbDistribution α :=
  ⟨fun y ↦ if x = y then 1 else 0,
    by simp [apply_ite]⟩

theorem constant_def (x : α) : (constant x : α → Prob) = fun y ↦ if x = y then 1 else 0 := by
  rfl

@[simp]
theorem constant_eq (x : α) : constant x y = if x = y then 1 else 0 := by
  rfl

@[simp]
theorem constant_def' (x y : α) : (constant x : α → Prob) y = if x = y then 1 else 0 := by
  rw [← Prob.eq_iff_nnreal]
  change (Prob.toNNReal ∘ (constant x)) y = (if x = y then 1 else 0 : Prob)
  rw [constant_def x]
  split_ifs with h
  <;> simp [h]

/-- If a distribution has an element with probability 1, the distribution has a constant. -/
theorem constant_of_exists_one {D : ProbDistribution α} {x : α} (h : D x = 1) :
    D = ProbDistribution.constant x := by
  ext y
  by_cases h₂ : x = y
  · simp [h, ← h₂]
  · simp only [constant_eq, h₂, ↓reduceIte, Prob.coe_zero]
    by_contra h₃
    replace h₃ : 0 < (D y : ℝ) := by
      linarith (config := {splitNe := true}) only [h₃, @Prob.zero_le_coe (D y)]
    have := D.normalized
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), h, Prob.coe_one] at this
    rw [← Finset.add_sum_erase _ _ (a := y) (by simpa using (Ne.symm h₂))] at this
    have : 0 ≤ ∑ x ∈ Finset.erase (Finset.erase Finset.univ x) y, (D x : ℝ) :=
      Finset.sum_nonneg' (fun _ ↦ Prob.zero_le_coe)
    linarith

/-- Make an uniform distribution. -/
def uniform [n : Nonempty α] : ProbDistribution α :=
  ⟨fun _ ↦ ⟨1 / (Finset.univ.card (α := α)), by
    have : 0 < Finset.univ.card (α := α) :=
      Finset.Nonempty.card_pos (Finset.univ_nonempty_iff.mpr n)
    bound⟩, by simp⟩

@[simp]
theorem uniform_def [Nonempty α] (y : α) : ((uniform y) : ℝ) = 1 / (Finset.univ.card (α := α)) :=
  rfl

/-- Make a distribution on a product of two Fintypes. -/
def prod (d1 : ProbDistribution α) (d2 : ProbDistribution β) : ProbDistribution (Prod α β) :=
  ⟨fun x ↦ (d1 x.1) * (d2 x.2), by
    simp [← Finset.mul_sum, Fintype.sum_prod_type]⟩

@[simp]
theorem prod_def (x : α) (y : β) : prod d1 d2 ⟨x, y⟩ = (d1 x) * (d2 y) :=
  rfl

/-- Given a distribution on α, extend it to a distribution on `Sum α β` by
  giving it no support on `β`. -/
def extend_right (d : ProbDistribution α) : ProbDistribution (α ⊕ β) :=
  ⟨fun x ↦ Sum.casesOn x d.val (Function.const _ 0), by simp⟩

/-- Given a distribution on α, extend it to a distribution on `Sum β α` by
  giving it no support on `β`. -/
def extend_left (d : ProbDistribution α) : ProbDistribution (β ⊕ α) :=
  ⟨fun x ↦ Sum.casesOn x (Function.const _ 0) d.val, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- Make a convex mixture of two distributions on the same set. -/
instance instMixable : Mixable (α → ℝ) (ProbDistribution α) :=
  Mixable.instSubtype (inferInstance) (fun _ _ hab hx hy ↦ by
    simp [Mixable.mix_ab, Finset.sum_add_distrib, ← Finset.mul_sum, hab, hx, hy]
  )

/-- Given a distribution on type α and an equivalence to type β, get the corresponding
distribution on type β. -/
def relabel (d : ProbDistribution α) (σ : β ≃ α) : ProbDistribution β :=
  ⟨fun b ↦ d (σ b),
   by rw [Equiv.sum_comp σ (fun a ↦ (d a : ℝ))]; exact d.prop⟩

-- The two properties below (and congrRandVar) follow from the fact that Distribution is a
-- contravariant functor.
-- However, mathlib does not seem to support that outside of the CategoryTheory namespace
set_option backward.isDefEq.respectTransparency false in
/-- ProbDistribution on α and β are equivalent for equivalent types α ≃ β. -/
def congr (σ : α ≃ β) : ProbDistribution α ≃ ProbDistribution β := by
  constructor
  case toFun => exact fun d ↦ relabel d σ.symm
  case invFun => exact fun d ↦ relabel d σ
  case left_inv =>
    intro d
    ext i
    unfold relabel
    simp only [← fun_eq_val, Equiv.symm_apply_apply, Subtype.coe_eta]
  case right_inv =>
    intro d
    ext i
    unfold relabel
    simp only [← fun_eq_val, Equiv.apply_symm_apply, Subtype.coe_eta]

@[simp]
theorem congr_apply (σ : α ≃ β) (d : ProbDistribution α) (j : β): (congr σ d) j = d (σ.symm j) := by
  rfl

/-- The inverse and congruence operations for distributions commute -/
@[simp]
theorem congr_symm_apply (σ : α ≃ β) :
    (ProbDistribution.congr σ).symm = ProbDistribution.congr σ.symm := by
  rfl

/-- The distribution on Fin 2 corresponding to a coin with probability p.
  Chance p of 1, 1-p of 0. -/
def coin (p : Prob) : ProbDistribution (Fin 2) :=
  ⟨(if · = 0 then p else 1 - p), by simp⟩

@[simp]
theorem coin_val_zero (p : Prob) : coin p 0 = p := by
  simp [coin]

@[simp]
theorem coin_val_one (p : Prob) : coin p 1 = 1 - p := by
  simp [coin]

/-- Every distribution on two variable is some coin. -/
theorem fin_two_eq_coin (d : ProbDistribution (Fin 2)) : d = coin (d 0) := by
  ext i
  fin_cases i
  · simp [coin]
  · simpa only [coin, Fin.mk_one, funlike_apply, one_ne_zero, ↓reduceIte,
    Prob.coe_one_minus, Subtype.ext_iff, Prob.coe_one_minus, eq_sub_iff_add_eq, add_comm,
        fun_eq_val, Fin.sum_univ_two] using d.property

theorem coin_eq_iff (p : Prob) (f : ProbDistribution (Fin 2)) :
    ProbDistribution.coin p = f ↔ p = f 0 := by
  constructor
  · rintro rfl
    rfl
  · rintro rfl
    rw [← ProbDistribution.fin_two_eq_coin f]

section randvar

/-- A `T`-valued random variable over `α` is a map `var : α → T` along
with a probability distribution `distr : Distribution α`. -/
structure RandVar (α : Type*) [Fintype α] (T : Type*) where
  var : α → T
  distr : ProbDistribution α

instance instFunctor : Functor (RandVar α) where map f e := ⟨f ∘ e.1, e.2⟩

instance instLawfulFunctor : LawfulFunctor (RandVar α) where
  map_const {α} {β} := by rfl
  id_map _ := by rfl
  comp_map _ _ _ := by rfl

-- `U` is required to be a group just because mix below uses Convex.sum_mem,
-- but it should be provable with just `AddCommMonoid U`
variable {T U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T]

/-- `Distribution.exp_val` is the expectation value of a random variable `X`. Under the hood,
it is the "convex combination over a finite family" on the type `T`, afforded by
the `Mixable` instance, with the probability distribution of `X` as weights. -/
def expect_val (X : RandVar α T) : T := by
  let u : U := ∑ i ∈ Finset.univ, (X.distr i : ℝ) • (inst.to_U (X.var i))
  have ht : ∃ t : T, inst.to_U t = u := by
    have h₀ : ∀ i ∈ Finset.univ, 0 ≤ ↑(X.distr i) := by simp
    have h₁ : ∑ i ∈ Finset.univ, (X.distr i : ℝ) = 1 := by simp
    have hz : ∀ i ∈ Finset.univ, inst.to_U (X.var i) ∈ Set.range inst.to_U := by
      simp [Finset.mem_univ]
    exact Set.mem_range.mp (inst.convex.sum_mem h₀ h₁ hz)
  exact (inst.mkT ht).1

/-- The defining property of `expect_val`: in the ambient module `U`, it is the weighted sum. -/
@[simp]
theorem to_U_expect_val (X : RandVar α T) :
    inst.to_U (expect_val X) = ∑ i, (X.distr i : ℝ) • inst.to_U (X.var i) :=
  (inst.mkT _).2

set_option backward.isDefEq.respectTransparency false in
/-- The expectation value of a random variable over `α = Fin 2` is the same as `Mixable.mix`
with probabiliy weight `X.distr 0` -/
theorem expect_val_eq_mixable_mix (d : ProbDistribution (Fin 2)) (x₁ x₂ : T) :
    expect_val ⟨![x₁, x₂], d⟩ = Mixable.mix (d 0) x₁ x₂ := by
  apply Mixable.to_U_inj
  simp only [Mixable.mix, expect_val, DFunLike.coe, Mixable.to_U_of_mkT]
  calc
    ∑ i : Fin (Nat.succ 0).succ, (d i : ℝ) • Mixable.to_U (![x₁, x₂] i) =
        ∑ i, (d i : ℝ) • Mixable.to_U (![x₁, x₂] i) := by
      simp
    _ = (d 0 : ℝ) • Mixable.to_U (![x₁, x₂] 0) + (d 1 : ℝ) • Mixable.to_U (![x₁, x₂] 1) := by
      simp
    _ = (d 0 : ℝ) • Mixable.to_U x₁ + (1 - d 0).val • Mixable.to_U x₂ := by
      congr
      simpa only [Subtype.ext_iff, Prob.coe_one_minus, eq_sub_iff_add_eq, add_comm,
        fun_eq_val, Fin.sum_univ_two] using d.property

set_option backward.isDefEq.respectTransparency false in
/-- The expectation value of a random variable with constant probability distribution
  `constant x` is its value at `x` -/
theorem expect_val_constant (x : α) (f : α → T) : expect_val ⟨f, (constant x)⟩ = f x := by
  apply Mixable.to_U_inj
  simp only [expect_val, constant, DFunLike.coe, Mixable.to_U_of_mkT, apply_ite, Prob.coe_one,
    Prob.coe_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The expectation value of a nonnegative real random variable is also nonnegative -/
theorem zero_le_expect_val (d : ProbDistribution α) (f : α → ℝ) (hpos : 0 ≤ f) :
    0 ≤ expect_val ⟨f, d⟩ := by
  simp only [expect_val, Mixable.mkT, Mixable.to_U, id]
  apply Fintype.sum_nonneg
  intro x
  specialize hpos x
  exact mul_nonneg Prob.zero_le_coe hpos

/-- `T`-valued random variables on `α` and `β` are equivalent if `α ≃ β` -/
def congrRandVar (σ : α ≃ β) : RandVar α T ≃ RandVar β T := by
  constructor
  case toFun => exact fun X ↦ { var := X.var ∘ σ.symm, distr := ProbDistribution.congr σ X.distr }
  case invFun => exact fun X ↦ { var := X.var ∘ σ, distr := ProbDistribution.congr σ.symm X.distr }
  case left_inv =>
    intro e
    dsimp
    congr
    · simp [Function.comp_assoc]
    · rw [← ProbDistribution.congr_symm_apply, Equiv.symm_apply_apply]
  case right_inv =>
    intro e
    dsimp
    congr
    · simp [Function.comp_assoc]
    · rw [← ProbDistribution.congr_symm_apply, Equiv.apply_symm_apply]

omit inst in
/-- Given a `T`-valued random variable `X` over `α`, mapping over `T` commutes
  with the equivalence over `α` -/
lemma map_congr_eq_congr_map {S : Type _} [Mixable U S] (f : T → S) (σ : α ≃ β) (X : RandVar α T) :
  f <$> congrRandVar σ X = congrRandVar σ (f <$> X) := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- The expectation value is invariant under equivalence of random variables -/
@[simp]
theorem expect_val_congr_eq_expect_val (σ : α ≃ β) (X : RandVar α T) :
    expect_val (congrRandVar σ X) = expect_val X := by
  apply Mixable.to_U_inj
  simp only [expect_val, congrRandVar, Equiv.coe_fn_mk, Function.comp_apply, Mixable.to_U_of_mkT,
    congr_apply]
  rw [Equiv.sum_comp σ.symm (fun i : α ↦ (X.distr i : ℝ) • Mixable.to_U (X.var i))]

end randvar

end ProbDistribution
