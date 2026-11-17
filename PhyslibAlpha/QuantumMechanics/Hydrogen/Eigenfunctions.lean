/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.RadialFunctions
public import Physlib.SpaceAndTime.Space.Derivatives.Laplacian

/-!

# The bound-state wave functions of the `d`-dimensional hydrogen atom

The bound-state wave functions of the hydrogen atom of physlib in `d ≥ 2` dimensions, as
explicit eigenfunctions of `-ℏ²/(2m) Δ - k/r` with the Bohr energies `HydrogenAtom.energyLevel`.

## i. Overview

The angular part is carried by a homogeneous harmonic polynomial `P` of degree `l`
(`Σᵢ yᵢ ∂ᵢP = l P`, `ΔP = 0`); in three dimensions these are the solid harmonics `r^l Y_lm`. For
a radial function `f`, the product rule and `Δ‖y‖² = 2d` give, away from the origin,

`Δ(f(r) P) = (f'' + (d - 1 + 2l) f'/r) P`

(`laplacian_radial_mul`, `laplacian_radial_harmonic`). This is the separation of variables in
spherical coordinates written without angles. The radial factor
`f(r) = e^(-κr) L_N^(2l+d-2)(2κr)` satisfies
`r f'' + (2l + d - 1) f' + (2κ(N + l + (d - 1)/2) - κ² r) f = 0` by the Laguerre equation
(`radialFactor_ode`). With `κ = 1/(a L)`, `a = ℏ²/(m k)` and `L = N + l + (d - 1)/2` the
Schrödinger equation holds with energy `-ℏ²κ²/(2m) = -Ry/L²`, physlib's Bohr level
`HydrogenAtom.energyLevel (N + l)` (`boundState_eigen`). The `s` and `p` states are spelled out
with `P = 1` and `P = yⱼ`.

The equation is proved pointwise away from the nucleus, where `ψ` is smooth. It does not say
that these are all eigenfunctions, nor that they lie in the domain of the self-adjoint
Hamiltonian; the spectral statements are the TODOs of `Physlib.QuantumMechanics.Hydrogen.Basic`.

## ii. Key results

- `laplacian_radial_mul`: the Laplacian of `G(‖y‖²) P(y)`.
- `laplacian_radial_harmonic`: the radial reduction for homogeneous harmonic `P`.
- `radialFactor_ode`: the radial equation of `e^(-κr) L_N^(α)(2κr)`.
- `boundState_eigen`: the bound states and their energies `E_{N+l}`.
- `boundState_eigen_s`, `boundState_eigen_p`: the `s` and `p` states.

## iii. Table of contents

- A. The Laplacian of a radial function times a polynomial
- B. Radial functions of `‖y‖`
- C. The radial factor
- D. The bound states of the `d`-dimensional hydrogen atom

## iv. References

- H. A. Bethe and E. E. Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*, Springer
  (1957).
- J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*, 3rd ed., Cambridge University
  Press (2020), section 3.7.

## A. The Laplacian of a radial function times a polynomial

-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open Space

variable {d : ℕ}

lemma isOpen_normSq_pos : IsOpen {y : Space d | 0 < ‖y‖ ^ 2} :=
  isOpen_lt continuous_const (continuous_norm.pow 2)

lemma differentiableAt_normSq (x : Space d) : DifferentiableAt ℝ (fun y : Space d => ‖y‖ ^ 2) x :=
  (hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt

/-- `∂ᵢ G(‖y‖²) = G'(‖y‖²) 2 yᵢ`. -/
lemma deriv_comp_normSq {G : ℝ → ℝ} {g : ℝ} {x : Space d} (hG : HasDerivAt G g (‖x‖ ^ 2))
    (i : Fin d) : ∂[i] (fun y : Space d => G (‖y‖ ^ 2)) x = g * (2 * x i) := by
  have h := hG.hasFDerivAt.comp x (differentiableAt_normSq x).hasFDerivAt
  rw [Space.deriv_eq, show (fun y : Space d => G (‖y‖ ^ 2)) = G ∘ (fun y => ‖y‖ ^ 2) from rfl,
    h.fderiv, ← deriv_norm_sq x i, Space.deriv_eq]
  simp only [fderiv_norm_sq_apply, ContinuousLinearMap.comp_smul, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, coe_innerSL_apply, inner_basis,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma differentiableAt_comp_normSq {G : ℝ → ℝ} {g : ℝ} {x : Space d}
    (hG : HasDerivAt G g (‖x‖ ^ 2)) : DifferentiableAt ℝ (fun y : Space d => G (‖y‖ ^ 2)) x :=
  (hG.differentiableAt.comp x (differentiableAt_normSq x))

lemma deriv_add_apply {A B : Space d → ℝ} {x : Space d} (hA : DifferentiableAt ℝ A x)
    (hB : DifferentiableAt ℝ B x) (i : Fin d) :
    ∂[i] (fun y => A y + B y) x = ∂[i] A x + ∂[i] B x := by
  rw [Space.deriv_eq, (hA.hasFDerivAt.fun_add hB.hasFDerivAt).fderiv, Space.deriv_eq,
    Space.deriv_eq]
  simp

lemma deriv_mul_apply {A B : Space d → ℝ} {x : Space d} (hA : DifferentiableAt ℝ A x)
    (hB : DifferentiableAt ℝ B x) (i : Fin d) :
    ∂[i] (fun y => A y * B y) x = A x * ∂[i] B x + B x * ∂[i] A x := by
  rw [Space.deriv_eq, fderiv_fun_mul hA hB, Space.deriv_eq, Space.deriv_eq]
  simp

/-- **The Laplacian of `G(‖y‖²) P(y)`** away from the origin:
`Δ(G P) = G ΔP + 4 G' Σᵢ yᵢ ∂ᵢP + (2d G' + 4‖y‖² G'') P`. -/
lemma laplacian_radial_mul {G G' G'' : ℝ → ℝ} (hG : ∀ s, 0 < s → HasDerivAt G (G' s) s)
    (hG' : ∀ s, 0 < s → HasDerivAt G' (G'' s) s) {P : Space d → ℝ} (hP : ContDiff ℝ 2 P)
    {x : Space d} (hx : x ≠ 0) :
    Δ (fun y => G (‖y‖ ^ 2) * P y) x = G (‖x‖ ^ 2) * Δ P x +
      4 * G' (‖x‖ ^ 2) * ∑ i, x i * ∂[i] P x +
        (2 * d * G' (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * G'' (‖x‖ ^ 2)) * P x := by
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have hPd : Differentiable ℝ P := hP.differentiable (by norm_num)
  have hdP : ∀ i, Differentiable ℝ (∂[i] P) := fun i => deriv_differentiable hP i
  -- the first derivative near `x`
  have h1 : ∀ i, ∀ y : Space d, 0 < ‖y‖ ^ 2 → ∂[i] (fun y => G (‖y‖ ^ 2) * P y) y =
      G (‖y‖ ^ 2) * ∂[i] P y + P y * (G' (‖y‖ ^ 2) * (2 * y i)) := fun i y hy => by
    rw [deriv_mul_apply (differentiableAt_comp_normSq (hG _ hy)) (hPd y),
      deriv_comp_normSq (hG _ hy)]
  have hev : ∀ i, ∂[i] (fun y => G (‖y‖ ^ 2) * P y) =ᶠ[nhds x]
      fun y => G (‖y‖ ^ 2) * ∂[i] P y + P y * (G' (‖y‖ ^ 2) * (2 * y i)) := fun i =>
    Filter.eventually_of_mem (isOpen_normSq_pos.mem_nhds hx2) fun y hy => h1 i y hy
  -- the second derivative at `x`
  have h2 : ∀ i, ∂[i] (∂[i] (fun y => G (‖y‖ ^ 2) * P y)) x =
      G (‖x‖ ^ 2) * ∂[i] (∂[i] P) x + 4 * G' (‖x‖ ^ 2) * (x i * ∂[i] P x) +
        (2 * G' (‖x‖ ^ 2) + 4 * x i ^ 2 * G'' (‖x‖ ^ 2)) * P x := fun i => by
    have hGd := differentiableAt_comp_normSq (hG _ hx2)
    have hG'd := differentiableAt_comp_normSq (hG' _ hx2)
    have hxi : DifferentiableAt ℝ (fun y : Space d => 2 * y i) x :=
      ((eval_differentiable i) x).const_mul 2
    rw [Space.deriv_eq, (hev i).fderiv_eq, ← Space.deriv_eq]
    rw [deriv_add_apply (A := fun y => G (‖y‖ ^ 2) * ∂[i] P y)
        (B := fun y => P y * (G' (‖y‖ ^ 2) * (2 * y i))) (hGd.mul (hdP i x))
        ((hPd x).mul (hG'd.mul hxi)),
      deriv_mul_apply hGd (hdP i x),
      deriv_mul_apply (B := fun y => G' (‖y‖ ^ 2) * (2 * y i)) (hPd x) (hG'd.mul hxi),
      deriv_mul_apply hG'd hxi,
      deriv_comp_normSq (hG _ hx2), deriv_comp_normSq (hG' _ hx2)]
    have hc : ∂[i] (fun y : Space d => 2 * y i) x = 2 := by
      rw [Space.deriv_eq, fderiv_const_mul ((eval_differentiable i) x),
        _root_.smul_apply, ← Space.deriv_eq, deriv_component_same]
      simp
    rw [hc]
    ring
  rw [laplacian_eq_sum_snd_deriv]
  simp only [h2]
  rw [show Δ P x = ∑ i, ∂[i] (∂[i] P) x by rw [laplacian_eq_sum_snd_deriv], norm_sq_eq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-!

## B. Radial functions of `‖y‖`

-/

lemma hasDerivAt_comp_sqrt {f f' : ℝ → ℝ} (hf : ∀ r, 0 < r → HasDerivAt f (f' r) r) {s : ℝ}
    (hs : 0 < s) :
    HasDerivAt (fun s => f (Real.sqrt s)) (f' (Real.sqrt s) / (2 * Real.sqrt s)) s := by
  have h := (hf _ (Real.sqrt_pos.mpr hs)).comp s (Real.hasDerivAt_sqrt hs.ne')
  refine h.congr_deriv ?_
  field_simp

lemma hasDerivAt_comp_sqrt' {f' f'' : ℝ → ℝ} (hf : ∀ r, 0 < r → HasDerivAt f' (f'' r) r) {s : ℝ}
    (hs : 0 < s) : HasDerivAt (fun s => f' (Real.sqrt s) / (2 * Real.sqrt s))
      ((f'' (Real.sqrt s) - f' (Real.sqrt s) / Real.sqrt s) / (4 * s)) s := by
  have hr := Real.sqrt_pos.mpr hs
  have hsq := Real.sq_sqrt hs.le
  have h := (hasDerivAt_comp_sqrt hf hs).div ((Real.hasDerivAt_sqrt hs.ne').const_mul 2)
    (by positivity)
  refine h.congr_deriv ?_
  generalize Real.sqrt s = t at hr hsq ⊢
  subst hsq
  field_simp
  ring

/-- The Laplacian of `f(‖y‖) P(y)` for a homogeneous harmonic polynomial `P` of degree `l`:
`Δ(f P) = (f'' + (d - 1 + 2l) f'/r) P`. -/
lemma laplacian_radial_harmonic {f f' f'' : ℝ → ℝ} (hf : ∀ r, 0 < r → HasDerivAt f (f' r) r)
    (hf' : ∀ r, 0 < r → HasDerivAt f' (f'' r) r) {P : Space d → ℝ} (hP : ContDiff ℝ 2 P) {l : ℕ}
    (hE : ∀ y : Space d, ∑ i, y i * ∂[i] P y = l * P y) (hΔ : ∀ y, Δ P y = 0) {x : Space d}
    (hx : x ≠ 0) :
    Δ (fun y => f ‖y‖ * P y) x =
      (f'' ‖x‖ + ((d : ℝ) - 1 + 2 * l) * f' ‖x‖ / ‖x‖) * P x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hfun : (fun y : Space d => f ‖y‖ * P y) = fun y => f (Real.sqrt (‖y‖ ^ 2)) * P y :=
    funext fun y => by rw [Real.sqrt_sq (norm_nonneg y)]
  rw [hfun, laplacian_radial_mul (fun s hs => hasDerivAt_comp_sqrt hf hs)
    (fun s hs => hasDerivAt_comp_sqrt' hf' hs) hP hx, hΔ, hE, Real.sqrt_sq (norm_nonneg x)]
  field_simp
  ring

/-!

## C. The radial factor

-/

open Polynomial

/-- The polynomial `L_N^(α)(2κr)` in `r`. -/
def laguerreScaled (κ : ℝ) (N α : ℕ) : ℝ[X] := (laguerre N α).comp (C (2 * κ) * X)

/-- The radial factor `e^(-κr) L_N^(α)(2κr)` of a bound state. -/
def radialFactor (κ : ℝ) (N α : ℕ) (r : ℝ) : ℝ :=
  (laguerreScaled κ N α).eval r * Real.exp (-(κ * r))

/-- The first derivative of `radialFactor`. -/
def radialFactor' (κ : ℝ) (N α : ℕ) (r : ℝ) : ℝ :=
  (derivative (laguerreScaled κ N α) - C κ * laguerreScaled κ N α).eval r * Real.exp (-(κ * r))

/-- The second derivative of `radialFactor`. -/
def radialFactor'' (κ : ℝ) (N α : ℕ) (r : ℝ) : ℝ :=
  (derivative (derivative (laguerreScaled κ N α) - C κ * laguerreScaled κ N α) -
    C κ * (derivative (laguerreScaled κ N α) - C κ * laguerreScaled κ N α)).eval r *
      Real.exp (-(κ * r))

lemma hasDerivAt_radialFactor (κ : ℝ) (N α : ℕ) (r : ℝ) :
    HasDerivAt (radialFactor κ N α) (radialFactor' κ N α r) r :=
  hasDerivAt_eval_mul_exp _ κ r

lemma hasDerivAt_radialFactor' (κ : ℝ) (N α : ℕ) (r : ℝ) :
    HasDerivAt (radialFactor' κ N α) (radialFactor'' κ N α r) r :=
  hasDerivAt_eval_mul_exp _ κ r

/-- The radial equation of the bound state:
`r f'' + (α + 1) f' + (2κ(N + (α + 1)/2) - κ² r) f = 0`. -/
lemma radialFactor_ode (κ : ℝ) (N α : ℕ) (r : ℝ) :
    r * radialFactor'' κ N α r + ((α : ℝ) + 1) * radialFactor' κ N α r +
      (2 * κ * ((N : ℝ) + ((α : ℝ) + 1) / 2) - κ ^ 2 * r) * radialFactor κ N α r = 0 := by
  have h := laguerre_ode (N := N) (α := α) (2 * κ * r)
  simp only [radialFactor, radialFactor', radialFactor'', laguerreScaled, eval_sub, eval_mul,
    eval_C, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp,
    eval_comp, eval_X, derivative_X, mul_one]
  linear_combination (2 * κ * Real.exp (-(κ * r))) * h

/-!

## D. The bound states of the `d`-dimensional hydrogen atom

-/

open QuantumMechanics Constants

/-- The decay constant `κ = 1/(a L_n)` of the level `n`, with `L_n = n + (d - 1)/2`. -/
def boundKappa (H : HydrogenAtom d) (n : ℕ) : ℝ := 1 / (bohrRadius H * HydrogenAtom.levelIndex d n)

/-- The bound state `ψ(y) = e^(-κ r) L_N^(2l+d-2)(2κ r) P(y)`, `r = ‖y‖`, of the level
`n = N + l`, built from a homogeneous harmonic polynomial `P` of degree `l`. -/
def boundState (H : HydrogenAtom d) (N l : ℕ) (P : Space d → ℝ) (y : Space d) : ℝ :=
  radialFactor (boundKappa H (N + l)) N (2 * l + d - 2) ‖y‖ * P y

/-- **Bound states of the hydrogen atom in `d ≥ 2` dimensions.** Let `P` be a homogeneous
(`Σᵢ yᵢ ∂ᵢP = l P`) harmonic (`ΔP = 0`) polynomial of degree `l`, for instance `r^l Y_lm` in
three dimensions. Then away from the nucleus
`-ℏ²/(2m) Δψ - (k/r) ψ = E_{N+l} ψ` for `ψ = boundState H N l P`, where `E_n` is the Bohr level
`HydrogenAtom.energyLevel n = -Ry/(n + (d - 1)/2)²`. -/
lemma boundState_eigen (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (N l : ℕ)
    {P : Space d → ℝ} (hP : ContDiff ℝ 2 P) (hE : ∀ y : Space d, ∑ i, y i * ∂[i] P y = l * P y)
    (hΔ : ∀ y, Δ P y = 0) {x : Space d} (hx : x ≠ 0) :
    -((ℏ : ℝ) ^ 2 / (2 * H.m)) * Δ (boundState H N l P) x + H.potential x * boundState H N l P x =
      H.energyLevel (N + l) * boundState H N l P x := by
  set κ := boundKappa H (N + l) with hκ
  set α := 2 * l + d - 2 with hα
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hL : 0 < HydrogenAtom.levelIndex d (N + l) := HydrogenAtom.levelIndex_pos hd (N + l)
  have hm := H.m_pos.ne'
  have hk0 := hk.ne'
  have hℏ := ℏ_ne_zero
  have hαR : (α : ℝ) + 1 = (d : ℝ) - 1 + 2 * l := by
    rw [hα, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hNL : (N : ℝ) + ((α : ℝ) + 1) / 2 = HydrogenAtom.levelIndex d (N + l) := by
    rw [hαR, HydrogenAtom.levelIndex_eq]
    push_cast
    ring
  rw [show boundState H N l P = fun y => radialFactor κ N α ‖y‖ * P y from rfl,
    laplacian_radial_harmonic (fun r _ => hasDerivAt_radialFactor κ N α r)
      (fun r _ => hasDerivAt_radialFactor' κ N α r) hP hE hΔ hx]
  have hode := radialFactor_ode κ N α ‖x‖
  rw [hNL, hαR] at hode
  have key : radialFactor'' κ N α ‖x‖ + ((d : ℝ) - 1 + 2 * l) * radialFactor' κ N α ‖x‖ / ‖x‖ =
      (κ ^ 2 - 2 * κ * HydrogenAtom.levelIndex d (N + l) / ‖x‖) * radialFactor κ N α ‖x‖ := by
    field_simp
    linear_combination hode
  rw [key, H.potential_eq, HydrogenAtom.energyLevel_eq, HydrogenAtom.rydbergEnergy_eq, hκ,
    boundKappa, bohrRadius]
  field_simp
  ring

/-- The constant polynomial is homogeneous of degree `0` and harmonic: the `s` states. -/
lemma boundState_eigen_s (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (N : ℕ)
    {x : Space d} (hx : x ≠ 0) :
    -((ℏ : ℝ) ^ 2 / (2 * H.m)) * Δ (boundState H N 0 fun _ => 1) x +
        H.potential x * boundState H N 0 (fun _ => 1) x =
      H.energyLevel N * boundState H N 0 (fun _ => 1) x := by
  have h := boundState_eigen H hd hk N 0 (P := fun _ => 1) contDiff_const (fun y => by simp)
    (fun y => ?_) hx
  · simpa using h
  · rw [laplacian_eq_sum_snd_deriv]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ∂[i] (fun _ : Space d => (1 : ℝ)) = fun _ => 0 :=
      funext fun z => Space.deriv_const 1 i
    rw [this, Space.deriv_const]

/-- A coordinate `yⱼ` is homogeneous of degree `1` and harmonic: the `p` states. -/
lemma boundState_eigen_p (H : HydrogenAtom d) (hd : 2 ≤ d) (hk : 0 < H.k) (N : ℕ) (j : Fin d)
    {x : Space d} (hx : x ≠ 0) :
    -((ℏ : ℝ) ^ 2 / (2 * H.m)) * Δ (boundState H N 1 fun y => y j) x +
        H.potential x * boundState H N 1 (fun y => y j) x =
      H.energyLevel (N + 1) * boundState H N 1 (fun y => y j) x := by
  refine boundState_eigen H hd hk N 1 (eval_contDiff j) (fun y => ?_) (fun y => ?_) hx
  · simp only [deriv_component, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Nat.cast_one, one_mul]
  · rw [laplacian_eq_sum_snd_deriv]
    simp only
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ∂[i] (fun y : Space d => y j) = fun _ => if i = j then 1 else 0 :=
      funext fun z => deriv_component j i z
    rw [this, Space.deriv_const]

end PhyslibAlpha.Hydrogen
