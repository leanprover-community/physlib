/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.PolyBounded
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Basic

/-!
# The hydrogen bound states in `L²`

## i. Overview

The bound states `boundState H N l P` of `Eigenfunctions.lean` are square integrable: they are a
polynomial in the coordinates and in `‖y‖` times `e^(-κ‖y‖)`, and such functions decay faster than
any power of `1 + ‖y‖`. They therefore define vectors of the Hilbert space `SpaceDHilbertSpace d`.
Since they are continuous, the linear independence of the bound states of one level
(`boundStateMap_injective`) carries over to the Hilbert space; since they are real valued, it
holds over `ℂ` as well.

## ii. Key results

- `memHS_boundState`, `boundStateHS` : the bound states as vectors of `SpaceDHilbertSpace d`.
- `boundStateMapHS_injective` : the bound states of one level are linearly independent in
  `SpaceDHilbertSpace d`.
- `finrank_range_boundStateMapHS_three` : in three dimensions they span a real subspace of
  dimension `(n + 1)²`.
- `linearIndependent_complex_of_real_inner` : vectors with real Gram matrix which are linearly
  independent over `ℝ` are linearly independent over `ℂ`.
- `finrank_span_range_boundStateMapHS_three` : in three dimensions the bound states of the level
  `n` span a complex subspace of dimension `(n + 1)²`.

## iii. Table of contents

- A. The bound states in the Hilbert space
- B. Linear independence in the Hilbert space

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open MeasureTheory Space
open scoped SchwartzMap LineDeriv

/-!

## A. The bound states in the Hilbert space

-/

open QuantumMechanics

/-- The decay constant `κ = 1/(a L_n)` of a bound state is positive for `k > 0` and `d ≥ 2`. -/
lemma boundKappa_pos (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (n : ℕ) :
    0 < boundKappa H n :=
  one_div_pos.mpr (mul_pos (bohrRadius_pos H hk) (HydrogenAtom.levelIndex_pos hd n))

lemma continuous_boundState (H : HydrogenAtom d) (N l : ℕ) (P : MvPolynomial (Fin d) ℝ) :
    Continuous (boundState H N l (toFun P)) := by
  have hP : Continuous (toFun P) := (contDiff_toFun_infty P).continuous
  unfold boundState radialFactor
  fun_prop

/-- The bound states are square integrable. -/
lemma memHS_boundState (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (N l : ℕ)
    (P : MvPolynomial (Fin d) ℝ) :
    SpaceDHilbertSpace.MemHS (fun y => (boundState H N l (toFun P) y : ℂ)) := by
  have hc : Continuous fun y => (boundState H N l (toFun P) y : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_boundState H N l P)
  rw [SpaceDHilbertSpace.MemHS, memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  have hint := integrable_sq_of_le_mul_exp (boundKappa_pos H hd hk (N + l))
    (continuous_boundState H N l P).aestronglyMeasurable
    ((IsPolyBounded.norm.polynomial_eval (laguerreScaled (boundKappa H (N + l)) N
      (2 * l + d - 2))).mul (IsPolyBounded.toFun P))
    (fun y => by
      simp only [boundState, radialFactor, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact le_of_eq (by ring))
  simpa [Complex.norm_real, sq_abs] using hint

/-- The bound state `boundState H N l P` as a vector of `SpaceDHilbertSpace d`. -/
def boundStateHS (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (N l : ℕ)
    (P : MvPolynomial (Fin d) ℝ) : SpaceDHilbertSpace d :=
  SpaceDHilbertSpace.mk (memHS_boundState H hd hk N l P)

/-!

## B. Linear independence in the Hilbert space

All bound states of the level `n` share the decay constant `κ = boundKappa H n`, so their sums
are again `e^(-κ‖y‖)` times a polynomially bounded function.

-/

/-- `Σ_l boundState H (n - l) l P_l = e^(-κ‖y‖) Σ_l L_l(‖y‖) P_l(y)` with `κ = boundKappa H n`. -/
lemma boundStateMap_apply (H : HydrogenAtom d) (n : ℕ)
    (Ps : (l : Fin (n + 1)) → harmonicSubmodule d l) (y : Space d) :
    boundStateMap H n Ps y = Real.exp (-(boundKappa H n * ‖y‖)) *
      ∑ l : Fin (n + 1), (laguerreScaled (boundKappa H n) (n - l) (2 * l + d - 2)).eval ‖y‖ *
        toFun (Ps l : MvPolynomial (Fin d) ℝ) y := by
  simp only [boundStateMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [boundState, Nat.sub_add_cancel (Nat.lt_succ_iff.mp l.isLt), radialFactor]
  ring

lemma continuous_boundStateMap (H : HydrogenAtom d) (n : ℕ)
    (Ps : (l : Fin (n + 1)) → harmonicSubmodule d l) : Continuous (boundStateMap H n Ps) := by
  have h : boundStateMap H n Ps = fun y => ∑ l : Fin (n + 1),
      boundState H (n - l) l (toFun (Ps l : MvPolynomial (Fin d) ℝ)) y := by
    funext y
    simp [boundStateMap, Finset.sum_apply]
  rw [h]
  exact continuous_finsetSum _ fun l _ => continuous_boundState H _ _ _

/-- The sums of bound states of one level are square integrable. -/
lemma memHS_boundStateMap (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (n : ℕ)
    (Ps : (l : Fin (n + 1)) → harmonicSubmodule d l) :
    SpaceDHilbertSpace.MemHS (fun y => (boundStateMap H n Ps y : ℂ)) := by
  have hc : Continuous fun y => (boundStateMap H n Ps y : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_boundStateMap H n Ps)
  rw [SpaceDHilbertSpace.MemHS, memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  have hint := integrable_sq_of_le_mul_exp (boundKappa_pos H hd hk n)
    (continuous_boundStateMap H n Ps).aestronglyMeasurable
    (IsPolyBounded.sum Finset.univ fun l _ =>
      (IsPolyBounded.norm.polynomial_eval _).mul (IsPolyBounded.toFun _))
    (fun y => by
      rw [boundStateMap_apply, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm])
  simpa [Complex.norm_real, sq_abs] using hint

/-- The bound states of the level `n` as an `ℝ`-linear map into `SpaceDHilbertSpace d`. -/
def boundStateMapHS (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (n : ℕ) :
    ((l : Fin (n + 1)) → harmonicSubmodule d l) →ₗ[ℝ] SpaceDHilbertSpace d where
  toFun Ps := SpaceDHilbertSpace.mk (memHS_boundStateMap H hd hk n Ps)
  map_add' Ps Qs := by
    rw [SpaceDHilbertSpace.ext_iff]
    filter_upwards [SpaceDHilbertSpace.coeFn_mk (memHS_boundStateMap H hd hk n (Ps + Qs)),
      SpaceDHilbertSpace.coeFn_mk (memHS_boundStateMap H hd hk n Ps),
      SpaceDHilbertSpace.coeFn_mk (memHS_boundStateMap H hd hk n Qs),
      Lp.coeFn_add (SpaceDHilbertSpace.mk (memHS_boundStateMap H hd hk n Ps))
        (SpaceDHilbertSpace.mk (memHS_boundStateMap H hd hk n Qs))] with y h₁ h₂ h₃ h₄
    rw [h₁, h₄, Pi.add_apply, h₂, h₃, map_add, Pi.add_apply, Complex.ofReal_add]
  map_smul' c Ps := by
    rw [SpaceDHilbertSpace.ext_iff]
    filter_upwards [SpaceDHilbertSpace.coeFn_mk (memHS_boundStateMap H hd hk n (c • Ps)),
      SpaceDHilbertSpace.coeFn_mk (memHS_boundStateMap H hd hk n Ps),
      Lp.coeFn_smul c (SpaceDHilbertSpace.mk (memHS_boundStateMap H hd hk n Ps))] with y h₁ h₂ h₃
    rw [h₁, RingHom.id_apply, h₃, Pi.smul_apply, h₂, map_smul, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_mul, Complex.real_smul]

/-- The bound states of one level are linearly independent in `SpaceDHilbertSpace d`. -/
lemma boundStateMapHS_injective (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (n : ℕ) :
    Function.Injective (boundStateMapHS H hd hk n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Ps h
  apply boundStateMap_injective H n
  rw [map_zero]
  have hae : (fun y => (boundStateMap H n Ps y : ℂ)) =ᵐ[volume] 0 :=
    (SpaceDHilbertSpace.coeFn_mk (memHS_boundStateMap H hd hk n Ps)).symm.trans
      ((show SpaceDHilbertSpace.mk (memHS_boundStateMap H hd hk n Ps) = 0 from h) ▸
        Lp.coeFn_zero ℂ 2 volume)
  have hcont := Complex.continuous_ofReal.comp (continuous_boundStateMap H n Ps)
  have h0 := (hcont.ae_eq_iff_eq volume continuous_const).mp hae
  funext y
  simpa using (Complex.ext_iff.mp (congr_fun h0 y)).1

/-- In three dimensions the bound states of the level `n` span a `(n + 1)²`-dimensional subspace
of `SpaceDHilbertSpace 3`. -/
lemma finrank_range_boundStateMapHS_three (H : HydrogenAtom 3) (hk : 0 < H.k)
    (n : ℕ) :
    Module.finrank ℝ (LinearMap.range (boundStateMapHS H (by omega) hk n)) = (n + 1) ^ 2 := by
  rw [LinearMap.finrank_range_of_inj (boundStateMapHS_injective H _ hk n),
    ← LinearMap.finrank_range_of_inj (boundStateMap_injective H n),
    finrank_range_boundStateMap_three H n]

open scoped InnerProductSpace in
/-- Vectors with real Gram matrix that are linearly independent over `ℝ` are linearly independent
over `ℂ`. -/
lemma linearIndependent_complex_of_real_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι] {v : ι → E}
    (him : ∀ k j, (⟪v k, v j⟫_ℂ).im = 0) (hv : LinearIndependent ℝ v) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc
  have hreal : ∀ x y : ι → ℝ, (⟪∑ j, x j • v j, ∑ j, y j • v j⟫_ℂ).im = 0 := by
    intro x y
    simp only [← Complex.coe_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      him, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  set wa := ∑ j, (c j).re • v j
  set wb := ∑ j, (c j).im • v j
  have hw : wa = -(Complex.I • wb) := by
    rw [eq_neg_iff_add_eq_zero, ← hc]
    simp only [wa, wb, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
    congr 1
    rw [mul_comm, Complex.re_add_im]
  have ha : wa = 0 := by
    have h1 : (⟪wa, wa⟫_ℂ).re = 0 := by
      nth_rw 2 [hw]
      rw [inner_neg_right, inner_smul_right, Complex.neg_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, hreal]
      ring
    have h2 : ‖wa‖ ^ 2 = 0 := by rw [← h1]; exact (inner_self_eq_norm_sq (𝕜 := ℂ) wa).symm
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  have hb : wb = 0 := by
    rw [ha, zero_eq_neg] at hw
    exact (smul_eq_zero.mp hw).resolve_left Complex.I_ne_zero
  intro j
  exact Complex.ext (hv _ ha j) (hv _ hb j)

open scoped InnerProductSpace in
/-- The bound states are real valued, so their inner products are real. -/
lemma im_inner_boundStateMapHS (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (n : ℕ)
    (Ps Qs : (l : Fin (n + 1)) → harmonicSubmodule d l) :
    (⟪boundStateMapHS H hd hk n Ps, boundStateMapHS H hd hk n Qs⟫_ℂ).im = 0 := by
  change (⟪SpaceDHilbertSpace.mk (memHS_boundStateMap H hd hk n Ps),
    SpaceDHilbertSpace.mk (memHS_boundStateMap H hd hk n Qs)⟫_ℂ).im = 0
  rw [SpaceDHilbertSpace.inner_mk_mk]
  simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_im]

/-- In three dimensions the bound states of the level `n` span a complex subspace of dimension
`(n + 1)²` of `SpaceDHilbertSpace 3`. -/
lemma finrank_span_range_boundStateMapHS_three (H : HydrogenAtom 3) (hk : 0 < H.k)
    (n : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (boundStateMapHS H (by omega) hk n))) =
      (n + 1) ^ 2 := by
  set T := boundStateMapHS H (by omega) hk n
  set b := Module.finBasis ℝ ((l : Fin (n + 1)) → harmonicSubmodule 3 l)
  have hli : LinearIndependent ℂ (T ∘ b) :=
    linearIndependent_complex_of_real_inner
      (fun k j => im_inner_boundStateMapHS H _ hk n (b k) (b j))
      (b.linearIndependent.map' T
        (LinearMap.ker_eq_bot.mpr (boundStateMapHS_injective H _ hk n)))
  have hspan : Submodule.span ℂ (Set.range T) = Submodule.span ℂ (Set.range (T ∘ b)) := by
    refine le_antisymm ?_ (Submodule.span_mono (Set.range_comp_subset_range _ _))
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin,
    ← LinearMap.finrank_range_of_inj (boundStateMapHS_injective H (by omega) hk n),
    finrank_range_boundStateMapHS_three H hk n]

end PhyslibAlpha.Hydrogen
