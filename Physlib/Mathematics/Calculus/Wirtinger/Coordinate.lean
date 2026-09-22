/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Calculus.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Data.Fintype.Defs

/-!

# Partial Wirtinger derivatives `∂_I`, `∂̄_I` in a complex coordinate basis on `ℂ^n`

## Notation

The conventions of `Wirtinger.Basic` carry over verbatim, with the directional subscript `v`
replaced by a coordinate index `I` (standing for the direction `Pi.single I 1`).

* `∂_I f` and `∂̄_I f` are the holomorphic and anti-holomorphic coordinate Wirtinger
  derivatives of `f` in the I-th coordinate direction `Pi.single I 1` — the bar sits on the
  operator, never on the subscript. They are the directional `∂_v f` / `∂̄_v f` of
  `Wirtinger.Basic` at `v = Pi.single I 1`. For iterated derivatives the operators compose,
  `∂_I ∂̄_J f`.
* `z^I` is the I-th coordinate `u ↦ u^I`; `z̄^I = star z^I` is its pointwise conjugate (the
  `f̄` convention of `Wirtinger.Basic`).
* `∂_x`, `∂_y` are the slot-I real and imaginary Fréchet derivatives, along the directions
  `Pi.single I 1` and `Pi.single I i`.
* `δ_IJ` is the Kronecker delta.

## i. Overview

Coordinate specialization of `Wirtinger.Basic` to `V = ℂ^n` (spelled `ι → ℂ`,
`n = |ι|`, `ι` a `Fintype`), fixing the direction to the I-th basis vector
`Pi.single I 1`:

  `∂_I f  := ∂_v f`   at `v = Pi.single I 1`   (`dWirtingerCoord`)
  `∂̄_I f := ∂̄_v f`  at `v = Pi.single I 1`   (`dWirtingerAntiCoord`)

`∂_I`, `∂̄_I` are the partial Wirtinger derivatives w.r.t. coordinate `I`, the
other coordinates fixed. Coordinate values:

  `∂_I z^J = δ_IJ`,   `∂̄_I z̄^J = δ_IJ`,   `∂̄_I z^J = ∂_I z̄^J = 0`.

The basis makes the directional calculus computational. The operators
`dWirtingerCoord` / `dWirtingerAntiCoord` (§A, with real-Fréchet unfolding
`(1/2)(∂_x ∓ i ∂_y)`) come with:

- independence: `∂_I` annihilates every `z̄` and `∂̄_I` every `z` (the coordinate
  values above), so `z` and `z̄` behave as independent variables;
- additivity, `ℂ`-linearity, the Leibniz product rule, and the finite-sum rule
  (§B–C), so any polynomial in the coordinates and their conjugates differentiates
  termwise;
- conjugation, swapping the two operators (§B–C): `∂_I f̄ = conj (∂̄_I f)` and
  `∂̄_I f̄ = conj (∂_I f)`;
- holomorphic collapse (§B–C): for holomorphic `f`, `∂̄_I f = 0` and `∂_I f` is
  the ordinary complex partial `fderiv ℂ f u (Pi.single I 1)` (anti-holomorphic
  `f` dually);
- the per-coordinate chain rule for an outer `g : ℂ → ℂ` (§D), collapsing to a
  single term `∂_I (g ∘ f) = deriv g (f u) · ∂_I f` on holomorphic `g` (and `∂̄_I`
  likewise);
- the coordinate difference `z^J − z̄^J` (§C);
- Schwarz's theorem `∂_I ∂̄_J f = ∂̄_J ∂_I f` on `C²` `f` (§E,
  `dWirtingerCoord_dWirtingerAntiCoord_comm`).

Indexing by `I` casts the calculus in the language of several complex variables.
The first derivatives assemble into a gradient, the family of partials `∂_I f`
ranging over the coordinates `I`; the critical points of a holomorphic `h` are
then where `∂_I h = 0` for every `I`. The mixed second derivatives assemble into a
complex Hessian, the matrix with entries `∂_I ∂̄_J f` indexed by the pair `(I, J)`;
for a real function `Φ` the entries `∂_I ∂̄_J Φ` record its second-order behaviour.

That Hessian is Hermitian, by Schwarz (§E). For a real `K`, write the Kähler
metric `g_{IJ̄} = ∂_I ∂̄_J K`; conjugation gives `star (g_{JĪ}) = ∂̄_J ∂_I K`,
which Schwarz equates with `∂_I ∂̄_J K`, so `g_{IJ̄} = star (g_{JĪ})`. That is
Kähler-metric hermiticity.

The coordinate maps are Mathlib primitives — `z^I` is `ContinuousLinearMap.proj`, `z̄^I` its
`star` — and the holomorphic collapse reads `fderiv ℝ f = fderiv ℂ f` off the `restrictScalars`
bridge (§B).

Differentiability convention: hypothesis-bearing rules are pointwise (at `u`,
`DifferentiableAt`), valid on a proper subdomain (e.g. a slit-domain log Kähler
potential); `funext` locally for a function-level form. Hypothesis-free constant
and coordinate facts are function equalities.

## ii. Key results

- `Physlib.Wirtinger.dWirtingerCoord` / `dWirtingerAntiCoord` : the
    coordinate Wirtinger operators, definitionally the directional operators
    along `Pi.single I 1`; their real-Fréchet form `dWirtingerCoord_apply` /
    `dWirtingerAntiCoord_apply` is `∂_I f = (1/2)(∂_x ∓ i ∂_y) f`.
- `Physlib.Wirtinger.dWirtingerCoord_coordProj` /
    `dWirtingerAntiCoord_coordProj` / `dWirtingerCoord_conjCoord` /
    `dWirtingerAntiCoord_conjCoord` : the four Kronecker coordinate values
    `∂_I z^J = δ_IJ`, `∂̄_I z̄^J = δ_IJ`, `∂̄_I z^J = ∂_I z̄^J = 0`.
- `Physlib.Wirtinger.dWirtingerCoord_add_apply` / `dWirtingerCoord_smul_apply` /
    `dWirtingerCoord_mul_apply` / `dWirtingerCoord_fun_sum_apply` : additivity,
    `ℂ`-linearity, the Leibniz rule, and the finite-sum rule (with
    anti-holomorphic duals).
- `Physlib.Wirtinger.dWirtingerCoord_star_comp_apply` /
    `dWirtingerAntiCoord_star_comp_apply` : conjugating the inner field swaps the
    two operators, `∂_I f̄ = conj (∂̄_I f)`.
- `Physlib.Wirtinger.dWirtingerCoord_eq_complex_fderiv_apply` /
    `dWirtingerAntiCoord_eq_zero_of_holomorphic_apply` : holomorphic collapse for
    the coordinate operators (with anti-holomorphic duals).
- `Physlib.Wirtinger.dWirtingerCoord_comp_apply` /
    `dWirtingerCoord_comp_holomorphic_apply` (and their anti-holomorphic duals): the
    two-term Wirtinger chain rule for an outer `g : ℂ → ℂ`, collapsing to the
    single-term `deriv g (f u) · ∂_I f` for holomorphic `g`.
- `Physlib.Wirtinger.dWirtingerCoord_coordDiff` /
    `dWirtingerAntiCoord_coordDiff` : Wirtinger derivatives of the
    coordinate difference `z^J − z̄^J`.
- `Physlib.Wirtinger.differentiableAt_dWirtingerCoord` /
    `differentiableAt_dWirtingerAntiCoord` : a first coordinate Wirtinger derivative of a
    `C²` function is itself real-differentiable (§E).
- `Physlib.Wirtinger.dWirtingerCoord_dWirtingerAntiCoord_comm` : Schwarz's
    theorem for the coordinate operators, `∂_I ∂̄_J f = ∂̄_J ∂_I f` on
    `C²` `f`.

## iii. Table of contents

- A. The coordinate Wirtinger operators
- B. Properties of `dWirtingerCoord`
- C. Properties of `dWirtingerAntiCoord`
- D. Wirtinger chain rules for an outer function
- E. Schwarz's theorem for the coordinate operators

-/

@[expose] public section
noncomputable section

namespace Physlib.Wirtinger

variable {ι : Type*}

/-!

## A. The coordinate Wirtinger operators

The two coordinate Wirtinger operators are the directional Wirtinger derivatives
of `Wirtinger.Basic` along the I-th coordinate direction `Pi.single I 1`:

  dWirtingerCoord f I    = (1/2) · (∂_x − i · ∂_y) f
  dWirtingerAntiCoord f I = (1/2) · (∂_x + i · ∂_y) f

where `∂_x` and `∂_y` are the real Fréchet derivatives of `f` along the slot-I
real and imaginary coordinate directions `Pi.single I 1` and
`Pi.single I Complex.I` (the latter is `Complex.I • Pi.single I 1`). The sign on
the imaginary-direction term is the only difference, making the two operators
dual on (anti)holomorphic functions (§B, §C).

Each `∂_I` is thus a 1-D directional derivative taken along the standard basis vector
`Pi.single I 1` — the whole calculus is the one-variable theory applied direction by
direction. The coordinates decouple (`∂_I z^J = δ_IJ`, §B) because the coordinate functionals
`z^J` are the dual basis to the standard basis: `z^J (Pi.single I 1) = δ_IJ`.

-/

variable [Fintype ι] [DecidableEq ι]

/-- Holomorphic Wirtinger derivative along the I-th coordinate of `ι → ℂ`. -/
def dWirtingerCoord (f : (ι → ℂ) → ℂ) (I : ι) : (ι → ℂ) → ℂ :=
  fun u => dWirtingerDir f (Pi.single I 1) u

/-- Anti-holomorphic Wirtinger derivative along the I-th coordinate of `ι → ℂ`. -/
def dWirtingerAntiCoord (f : (ι → ℂ) → ℂ) (I : ι) : (ι → ℂ) → ℂ :=
  fun u => dWirtingerAntiDir f (Pi.single I 1) u

/-- Real-Fréchet form of `dWirtingerCoord`:
`dWirtingerCoord f I u = (1/2)(∂_x − i · ∂_y) f`,
the derivatives along the slot-I real and imaginary coordinate directions.
Unconditional — the directional definition makes it definitional
(`Complex.I • Pi.single I 1 = Pi.single I Complex.I`); no differentiability
hypothesis is needed. -/
lemma dWirtingerCoord_apply {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (I : ι) :
    dWirtingerCoord f I u = (1 / 2 : ℂ) * (fderiv ℝ f u (Pi.single I 1)
      - Complex.I * fderiv ℝ f u (Pi.single I Complex.I)) := by
  simp only [dWirtingerCoord, dWirtingerDir_apply, ← Pi.single_smul', smul_eq_mul, mul_one]

/-- Real-Fréchet form of `dWirtingerAntiCoord`:
`∂̄_I f = (1/2)(∂_x + i · ∂_y) f`,
mirror of `dWirtingerCoord_apply` with the sign flip on the imaginary-direction term.
Unconditional, as for `dWirtingerCoord_apply`. -/
lemma dWirtingerAntiCoord_apply {f : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (I : ι) :
    dWirtingerAntiCoord f I u = (1 / 2 : ℂ) * (fderiv ℝ f u (Pi.single I 1)
      + Complex.I * fderiv ℝ f u (Pi.single I Complex.I)) := by
  simp only [dWirtingerAntiCoord, dWirtingerAntiDir_apply, ← Pi.single_smul', smul_eq_mul, mul_one]

/-!

## B. Properties of `dWirtingerCoord`

Each rule is the `d = Pi.single I 1` specialisation of its `Wirtinger`
foundation analogue. Rules carrying a differentiability hypothesis are stated
**pointwise** (at `u`, hypothesis `DifferentiableAt`) — the weakest form, and the
one to reach for on a function differentiable only on a proper domain; a consumer wanting
a function-level equation `funext`s locally. The hypothesis-free constant and
coordinate facts are stated as function equalities — the constant and
holomorphic-coordinate ones (`dWirtingerCoord_const`, `dWirtingerCoord_coordProj`) `@[simp]`.

The holomorphic collapse `∂_I f = fderiv ℂ f` for holomorphic `f` below (with the dual
`∂̄_I f = 0` in §C) needs the *real* derivative `fderiv ℝ f u` to be `ℂ`-linear. For holomorphic
`f`, `fderiv ℝ f u` is the `ℂ`-linear `fderiv ℂ f u` with scalars restricted to
`ℝ`, `fderiv ℝ f u = (fderiv ℂ f u).restrictScalars ℝ` (`HasFDerivAt.restrictScalars`).
Restricting scalars drops the `ℂ`-linear *bundling*, not the behaviour: the map still commutes
with `i`, `fderiv ℝ f u (i • d) = i • fderiv ℝ f u d` — the `ℂ`-linearity the collapse consumes.
`clinear_of_holomorphic` packages this, via `DifferentiableAt.fderiv_restrictScalars` and
`ContinuousLinearMap.coe_restrictScalars'`; `DifferentiableAt.restrictScalars` supplies the
`ℝ`-differentiability.

-/

/-- The real derivative of a holomorphic `f : E → ℂ` is `ℂ`-linear along every direction —
the hypothesis the foundation collapse `dWirtingerDir_eq_of_clinear` consumes. A holomorphic
`f` has `fderiv ℝ f u = (fderiv ℂ f u).restrictScalars ℝ`
(`DifferentiableAt.fderiv_restrictScalars`), so its real derivative agrees with the `ℂ`-linear
complex derivative on every direction. Used at `E = ι → ℂ` for the coordinate collapse and at
`E = ℂ` for the outer-`g` chain rule (§D). -/
private lemma clinear_of_holomorphic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {u : E}
    (hf : DifferentiableAt ℂ f u) (d : E) :
    fderiv ℝ f u (Complex.I • d) = Complex.I • fderiv ℝ f u d := by
  rw [DifferentiableAt.fderiv_restrictScalars ℝ hf, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

section

variable {f g : (ι → ℂ) → ℂ}

/-- `dWirtingerCoord` is local: functions agreeing on a neighbourhood of `u` have equal
holomorphic Wirtinger derivative at `u` (`f₁ =ᶠ[nhds u] f₂ ⟹ ∂_I f₁ u = ∂_I f₂ u`). -/
lemma dWirtingerCoord_congr_of_eventuallyEq_apply {f₁ f₂ : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (h : f₁ =ᶠ[nhds u] f₂) (I : ι) :
    dWirtingerCoord f₁ I u = dWirtingerCoord f₂ I u :=
  dWirtingerDir_congr_of_eventuallyEq h (Pi.single I 1)

/-- Constants have zero coordinate derivative: `∂_I c = 0`. -/
@[simp] lemma dWirtingerCoord_const (c : ℂ) (I : ι) :
    dWirtingerCoord (fun _ : (ι → ℂ) => c) I = 0 := by
  funext u; exact dWirtingerDir_const c (Pi.single I 1) u

/-- Pointwise negation rule for the holomorphic coordinate derivative at `u`:
`∂_I (−f) = −∂_I f`. Used with `dWirtingerCoord_add_apply` to assemble the
coordinate-difference rule `dWirtingerCoord_coordDiff` (§C). -/
lemma dWirtingerCoord_neg_apply {u : (ι → ℂ)} (I : ι) :
    dWirtingerCoord (fun v => -(f v)) I u = -(dWirtingerCoord f I u) :=
  dWirtingerDir_neg f (Pi.single I 1) u

omit [Fintype ι] [DecidableEq ι] in
/-- The real Fréchet derivative of the J-th coordinate projection `v ↦ v J`. Consumed by the
Kronecker coordinate-value lemmas `dWirtingerCoord_coordProj` / `dWirtingerAntiCoord_coordProj`,
which feed it the slot-I real and imaginary directions. -/
private lemma fderiv_coordProj (J : ι) (u d : (ι → ℂ)) :
    fderiv ℝ (fun v : (ι → ℂ) => v J) u d = d J := by
  rw [(hasFDerivAt_apply (𝕜 := ℝ) J u).fderiv, ContinuousLinearMap.proj_apply]

/-- `∂_I z^J = δ_IJ`. The holomorphic coordinate-independence value; also feeds the
coordinate-difference rule `dWirtingerCoord_coordDiff` and the conjugate-coordinate value
`dWirtingerAntiCoord_conjCoord` (§C). -/
@[simp] lemma dWirtingerCoord_coordProj (I J : ι) :
    dWirtingerCoord (fun u : (ι → ℂ) => u J) I =
      fun _ => if I = J then 1 else 0 := by
  funext u
  rw [dWirtingerCoord_apply I, fderiv_coordProj, fderiv_coordProj]
  by_cases h : I = J
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, ite_eq_left rfl, Complex.I_mul_I]; ring
  · simp [h]

/-- Pointwise additivity of the holomorphic coordinate derivative at `u`:
`∂_I (f + g) = ∂_I f + ∂_I g`. Used to assemble the coordinate-difference rule
`dWirtingerCoord_coordDiff` (§C). -/
lemma dWirtingerCoord_add_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerCoord (f + g) I u = dWirtingerCoord f I u + dWirtingerCoord g I u :=
  dWirtingerDir_add hf hg (Pi.single I 1)

/-- Pointwise compatibility with complex scalar multiplication at `u`:
`∂_I (c • f) = c • ∂_I f`. -/
lemma dWirtingerCoord_smul_apply {u : (ι → ℂ)}
    (c : ℂ) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerCoord (c • f) I u = c • dWirtingerCoord f I u :=
  dWirtingerDir_smul c hf (Pi.single I 1)

/-- Pointwise Leibniz rule for the holomorphic coordinate derivative at `u`:
`∂_I (f · g) = ∂_I f · g + f · ∂_I g`. -/
lemma dWirtingerCoord_mul_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerCoord (f * g) I u =
      dWirtingerCoord f I u * g u + f u * dWirtingerCoord g I u :=
  dWirtingerDir_mul hf hg (Pi.single I 1)

/-- Pointwise finite-sum rule for holomorphic coordinate derivatives at `u`:
`∂_I (∑ a ∈ s, F a) = ∑ a ∈ s, ∂_I (F a)`. -/
lemma dWirtingerCoord_fun_sum_apply {α : Type*} {s : Finset α}
    {F : α → (ι → ℂ) → ℂ} {u : (ι → ℂ)}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (I : ι) :
    dWirtingerCoord (fun v => ∑ a ∈ s, F a v) I u =
      ∑ a ∈ s, dWirtingerCoord (F a) I u :=
  dWirtingerDir_fun_sum hF (Pi.single I 1)

/-- For a holomorphic function, `dWirtingerCoord` is the complex Fréchet derivative in
the corresponding coordinate direction: `∂_I f = fderiv ℂ f u (Pi.single I 1)`. -/
lemma dWirtingerCoord_eq_complex_fderiv_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℂ f u) (I : ι) :
    dWirtingerCoord f I u = fderiv ℂ f u (Pi.single I 1) := by
  show dWirtingerDir f (Pi.single I 1) u = fderiv ℂ f u (Pi.single I 1)
  rw [dWirtingerDir_eq_of_clinear (clinear_of_holomorphic hf _),
    DifferentiableAt.fderiv_restrictScalars ℝ hf, ContinuousLinearMap.coe_restrictScalars']

/-- Pointwise conjugation bundled as an ℝ-linear CLM (conjugate-ℂ-linear): the I-th
component is conjugation of the I-th coordinate `Complex.conjCLE ∘ proj I`. Its underlying
function is the `star` of `ι → ℂ` (`conjCLM_apply`). Bundling `star` as a `→L[ℝ]` is what
lets the anti-holomorphic lemmas below feed it to the foundation `dWirtingerDir_comp_conjLinear`,
which requires its domain map as a continuous linear map. -/
private def conjCLM : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi
    (fun I => Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj (R := ℝ) I))

omit [Fintype ι] [DecidableEq ι] in
@[simp] private lemma conjCLM_apply (u : ι → ℂ) : conjCLM u = star u := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- `conjCLM` is conjugate-ℂ-linear: `conj (i·d) = -(i · conj d)`. The `hL` hypothesis the
foundation `dWirtingerDir_comp_conjLinear` / `dWirtingerAntiDir_comp_conjLinear` consume. -/
private lemma conjCLM_smul_I (d : ι → ℂ) :
    conjCLM (Complex.I • d) = -(Complex.I • conjCLM (ι := ι) d) := by
  funext I
  simp only [conjCLM_apply, Pi.star_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul, star_mul', Complex.star_def, Complex.conj_I]
  ring

/-- An *anti-holomorphic* function `v ↦ g (star v)` (a holomorphic `g` precomposed
with conjugation) depends on the coordinates only through their conjugates `z̄`. Its
holomorphic derivative therefore vanishes, `∂_I (g ∘ star) = 0`, since `∂_I`
differentiates w.r.t. `z` and treats `z̄` as constant. Dual to `∂̄_I f = 0` for
holomorphic `f`. -/
lemma dWirtingerCoord_eq_zero_of_antiHolomorphic_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (star u)) (I : ι) :
    dWirtingerCoord (fun v : (ι → ℂ) => g (star v)) I u = 0 := by
  have hgr : DifferentiableAt ℝ g (conjCLM u) := hg.restrictScalars ℝ
  change dWirtingerDir (fun v : (ι → ℂ) => g (conjCLM v)) (Pi.single I 1) u = 0
  rw [dWirtingerDir_comp_conjLinear conjCLM_smul_I hgr]
  exact dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic hg _)

end

/-!

## C. Properties of `dWirtingerAntiCoord`

This section is the `dWirtingerAntiCoord` mirror of §B: every rule with `z` and `z̄`
swapped (locality, constants, negation, additivity, scalar compatibility, Leibniz, the
finite-sum rule), together with the holomorphic collapse `∂̄_I f = 0`.

It also collects the two *conjugate-coordinate* values, one per operator:
`∂_I z̄^J = 0` (`dWirtingerCoord_conjCoord`) and `∂̄_I z̄^J = δ_IJ`
(`dWirtingerAntiCoord_conjCoord`). Since `z̄^J = star z^J`, each is the conjugate of the
corresponding value on the holomorphic coordinate `z^J`, read off through the foundation
conjugation lemmas `dWirtingerDir_star_comp` / `dWirtingerAntiDir_star_comp` rather than
recomputed.

-/

section

variable {f g : (ι → ℂ) → ℂ}

/-- `dWirtingerAntiCoord` is local (`f₁ =ᶠ[nhds u] f₂ ⟹ ∂̄_I f₁ u = ∂̄_I f₂ u`). -/
lemma dWirtingerAntiCoord_congr_of_eventuallyEq_apply {f₁ f₂ : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (h : f₁ =ᶠ[nhds u] f₂) (I : ι) :
    dWirtingerAntiCoord f₁ I u = dWirtingerAntiCoord f₂ I u :=
  dWirtingerAntiDir_congr_of_eventuallyEq h (Pi.single I 1)

/-- Constants have zero anti-holomorphic coordinate derivative: `∂̄_I c = 0`. -/
@[simp] lemma dWirtingerAntiCoord_const (c : ℂ) (I : ι) :
    dWirtingerAntiCoord (fun _ : (ι → ℂ) => c) I = 0 := by
  funext u; exact dWirtingerAntiDir_const c (Pi.single I 1) u

/-- Pointwise negation rule for the anti-holomorphic coordinate derivative at `u`:
`∂̄_I (−f) = −∂̄_I f`. Used with `dWirtingerAntiCoord_add_apply` to assemble the
coordinate-difference rule `dWirtingerAntiCoord_coordDiff` (§C). -/
lemma dWirtingerAntiCoord_neg_apply {u : (ι → ℂ)} (I : ι) :
    dWirtingerAntiCoord (fun v => -(f v)) I u = -(dWirtingerAntiCoord f I u) :=
  dWirtingerAntiDir_neg f (Pi.single I 1) u

/-- `∂̄_I z^J = 0`. The anti-holomorphic coordinate-independence value; also feeds the
coordinate-difference rule `dWirtingerAntiCoord_coordDiff` and the conjugate-coordinate
value `dWirtingerCoord_conjCoord` (§C). -/
@[simp] lemma dWirtingerAntiCoord_coordProj (I J : ι) :
    dWirtingerAntiCoord (fun u : (ι → ℂ) => u J) I = 0 := by
  funext u
  exact dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) J).differentiableAt _)

/-- `∂_I z̄^J = 0`. The conjugate of `dWirtingerAntiCoord_coordProj` (`z̄^J = star z^J`),
read off through `dWirtingerDir_star_comp` rather than recomputed. Used to assemble the
coordinate-difference rule `dWirtingerCoord_coordDiff` (§C). -/
lemma dWirtingerCoord_conjCoord (I J : ι) :
    dWirtingerCoord (fun u : (ι → ℂ) => star (u J)) I = 0 := by
  funext u
  exact dWirtingerCoord_eq_zero_of_antiHolomorphic_apply (g := fun w => w J)
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) J).differentiableAt I

/-- `∂̄_I z̄^J = δ_IJ`. The conjugate of `dWirtingerCoord_coordProj`, read off through
`dWirtingerAntiDir_star_comp` rather than recomputed. Used to assemble the
coordinate-difference rule `dWirtingerAntiCoord_coordDiff` (§C). -/
lemma dWirtingerAntiCoord_conjCoord (I J : ι) :
    dWirtingerAntiCoord (fun u : (ι → ℂ) => star (u J)) I =
      fun _ => if I = J then 1 else 0 := by
  funext u
  have hd : DifferentiableAt ℝ (fun w : (ι → ℂ) => w J) u :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) J).differentiableAt
  rw [show dWirtingerAntiCoord (fun u : (ι → ℂ) => star (u J)) I u
      = star (dWirtingerCoord (fun w : (ι → ℂ) => w J) I u)
      from dWirtingerAntiDir_star_comp hd (Pi.single I 1), dWirtingerCoord_coordProj]
  simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero]

/-- Pointwise additivity of the anti-holomorphic coordinate derivative at `u`:
`∂̄_I (f + g) = ∂̄_I f + ∂̄_I g`. Used to assemble the coordinate-difference rule
`dWirtingerAntiCoord_coordDiff` (§C). -/
lemma dWirtingerAntiCoord_add_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerAntiCoord (f + g) I u = dWirtingerAntiCoord f I u + dWirtingerAntiCoord g I u :=
  dWirtingerAntiDir_add hf hg (Pi.single I 1)

/-- Pointwise compatibility with complex scalar multiplication at `u`:
`∂̄_I (c • f) = c • ∂̄_I f`. -/
lemma dWirtingerAntiCoord_smul_apply {u : (ι → ℂ)}
    (c : ℂ) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (c • f) I u = c • dWirtingerAntiCoord f I u :=
  dWirtingerAntiDir_smul c hf (Pi.single I 1)

/-- Pointwise Leibniz rule for the anti-holomorphic coordinate derivative at `u`:
`∂̄_I (f · g) = ∂̄_I f · g + f · ∂̄_I g`. -/
lemma dWirtingerAntiCoord_mul_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (I : ι) :
    dWirtingerAntiCoord (f * g) I u =
      dWirtingerAntiCoord f I u * g u + f u * dWirtingerAntiCoord g I u :=
  dWirtingerAntiDir_mul hf hg (Pi.single I 1)

/-- Pointwise finite-sum rule for anti-holomorphic coordinate derivatives at `u`:
`∂̄_I (∑ a ∈ s, F a) = ∑ a ∈ s, ∂̄_I (F a)`. -/
lemma dWirtingerAntiCoord_fun_sum_apply {α : Type*} {s : Finset α}
    {F : α → (ι → ℂ) → ℂ} {u : (ι → ℂ)}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (I : ι) :
    dWirtingerAntiCoord (fun v => ∑ a ∈ s, F a v) I u =
      ∑ a ∈ s, dWirtingerAntiCoord (F a) I u :=
  dWirtingerAntiDir_fun_sum hF (Pi.single I 1)

/-- For an anti-holomorphic function the anti-holomorphic Wirtinger derivative equals
the complex Fréchet derivative of `g` at `star u` along the slot-I real
coordinate direction, `∂̄_I (g ∘ star) = fderiv ℂ g (star u) (Pi.single I 1)`.
Dual of `dWirtingerCoord_eq_complex_fderiv_apply`. -/
lemma dWirtingerAntiCoord_eq_complex_fderiv_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (star u)) (I : ι) :
    dWirtingerAntiCoord (fun v : (ι → ℂ) => g (star v)) I u =
      fderiv ℂ g (star u) (Pi.single I 1) := by
  have hgr : DifferentiableAt ℝ g (conjCLM u) := hg.restrictScalars ℝ
  change dWirtingerAntiDir (fun v : (ι → ℂ) => g (conjCLM v)) (Pi.single I 1) u
      = fderiv ℂ g (star u) (Pi.single I 1)
  rw [dWirtingerAntiDir_comp_conjLinear conjCLM_smul_I hgr]
  simp only [conjCLM_apply, Pi.star_single, star_one]
  rw [dWirtingerDir_eq_of_clinear (clinear_of_holomorphic hg _),
    DifferentiableAt.fderiv_restrictScalars ℝ hg, ContinuousLinearMap.coe_restrictScalars']

/-- Holomorphic functions have zero anti-holomorphic coordinate derivative: `∂̄_I f = 0`. -/
lemma dWirtingerAntiCoord_eq_zero_of_holomorphic_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℂ f u) (I : ι) :
    dWirtingerAntiCoord f I u = 0 :=
  dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic hf _)

/-!

### Coordinate-difference Wirtinger derivatives

The Wirtinger derivatives of the coordinate difference `z^J − z̄^J = 2 i Im(u^J)`, the
combination any function of the coordinates' imaginary parts differentiates against.
Collected here for reuse: `∂_I (z^J − z̄^J) = δ_IJ` and `∂̄_I (z^J − z̄^J) = −δ_IJ`.

-/

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinate difference `z^J − z̄^J` as a sum of the holomorphic coordinate
and the negated conjugate coordinate — the form on which the `dWirtingerCoord` /
`dWirtingerAntiCoord` additivity rules apply. -/
private lemma coordDiff_eq_add_neg (J : ι) :
    (fun v : (ι → ℂ) => v J - star (v J))
      = (fun v => v J) + (fun v => -(star (v J))) :=
  funext fun v => sub_eq_add_neg (v J) (star (v J))

/-- `∂_I (z^J − z̄^J) = δ_IJ`, from `∂_I z^J = δ_IJ` and
`∂_I z̄^J = 0`. -/
lemma dWirtingerCoord_coordDiff (I J : ι) :
    dWirtingerCoord (fun v : (ι → ℂ) => v J - star (v J)) I
      = fun _ => if I = J then 1 else 0 := by
  funext u
  rw [coordDiff_eq_add_neg, dWirtingerCoord_add_apply (by fun_prop) (by fun_prop) I,
    dWirtingerCoord_neg_apply I, dWirtingerCoord_coordProj, dWirtingerCoord_conjCoord]
  simp

/-- `∂̄_I (z^J − z̄^J) = −δ_IJ`, from `∂̄_I z^J = 0` and
`∂̄_I z̄^J = δ_IJ`. -/
lemma dWirtingerAntiCoord_coordDiff (I J : ι) :
    dWirtingerAntiCoord (fun v : (ι → ℂ) => v J - star (v J)) I
      = fun _ => if I = J then -1 else 0 := by
  funext u
  rw [coordDiff_eq_add_neg, dWirtingerAntiCoord_add_apply (by fun_prop) (by fun_prop) I,
    dWirtingerAntiCoord_neg_apply I, dWirtingerAntiCoord_coordProj, dWirtingerAntiCoord_conjCoord]
  by_cases h : I = J <;> simp [h]

end

/-!

## D. Wirtinger chain rules for an outer function

Composing with an outer `g : ℂ → ℂ` gives a **two-term** coordinate chain rule, the
`d = Pi.single I 1` case of the foundation `dWirtingerDir_comp`:

  `∂_I (g ∘ f) = (∂g/∂f) · ∂_I f + (∂g/∂f̄) · ∂_I f̄`.

A non-holomorphic `g` depends on both its argument and its conjugate, so both channels
contribute: the holomorphic coefficient `∂g/∂f` and the anti-holomorphic `∂g/∂f̄`, each
times the matching inner coordinate derivative — two terms where the complex-analytic rule
has one. The outer `g` enters only through these two coefficients, the directional
derivatives `dWirtingerDir g 1` and `dWirtingerAntiDir g 1` evaluated at `z = f u` (the
image of `u` under the inner function, where the chain rule reads off `g`). They are the
holomorphic and anti-holomorphic parts of `g`'s real Fréchet derivative: every `ℝ`-linear
map `ℂ → ℂ` splits uniquely as `h ↦ a · h + b · star h`, and on `L = fderiv ℝ g z` the
weights are `(a, b) = (∂g/∂f, ∂g/∂f̄)`.

For holomorphic `g` the anti-holomorphic coefficient `dWirtingerAntiDir g 1` vanishes and
`dWirtingerDir g 1` collapses to `deriv g z`, leaving the single-term rule
`∂_I (g ∘ f) = deriv g (f u) · ∂_I f` (`dWirtingerCoord_comp_holomorphic_apply`, with its
`∂̄_I` dual). Both collapses are the same `restrictScalars` step as §B — the real derivative
of a holomorphic `g : ℂ → ℂ` is `ℂ`-linear (`clinear_of_holomorphic` at `E = ℂ`).

-/

section

variable {g : ℂ → ℂ} {f : (ι → ℂ) → ℂ}

/-- The two-term coordinate chain rule for a real-differentiable outer `g`, pointwise at `u`:
`∂_I (g ∘ f) = (∂g/∂f) · ∂_I f + (∂g/∂f̄) · ∂_I f̄`,
with coefficients `∂g/∂f = dWirtingerDir g 1 (f u)` and `∂g/∂f̄ = dWirtingerAntiDir g 1 (f u)`.
The `d = Pi.single I 1` case of the foundation `dWirtingerDir_comp`. The single-term
holomorphic specialization `dWirtingerCoord_comp_holomorphic_apply` is proved from this. -/
lemma dWirtingerCoord_comp_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℝ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerCoord (fun v => g (f v)) I u =
      dWirtingerDir g 1 (f u) * dWirtingerCoord f I u
        + dWirtingerAntiDir g 1 (f u) *
          dWirtingerCoord (fun v : (ι → ℂ) => star (f v)) I u :=
  dWirtingerDir_comp hg hf (Pi.single I 1)

/-- The single-term coordinate chain rule for a holomorphic outer `g`, pointwise at `u`:
`∂_I (g ∘ f) = deriv g (f u) · ∂_I f`. From the two-term `dWirtingerCoord_comp_apply`: for
holomorphic `g` the anti-holomorphic coefficient `dWirtingerAntiDir g 1 (f u)` vanishes and
`dWirtingerDir g 1 (f u)` collapses to `deriv g (f u)`, both off the `ℂ`-linearity
`clinear_of_holomorphic` (§B). -/
lemma dWirtingerCoord_comp_holomorphic_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerCoord (fun v => g (f v)) I u =
      deriv g (f u) * dWirtingerCoord f I u := by
  rw [dWirtingerCoord_comp_apply (hg.restrictScalars ℝ) hf I,
    dWirtingerDir_eq_of_clinear (clinear_of_holomorphic hg 1),
    DifferentiableAt.fderiv_restrictScalars ℝ hg, ContinuousLinearMap.coe_restrictScalars',
    fderiv_apply_one_eq_deriv,
    dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic hg 1), zero_mul, add_zero]

/-- Conjugating the inner field swaps the two operators: `∂_I f̄ = conj (∂̄_I f)`. The
`d = Pi.single I 1` case of the foundation `dWirtingerDir_star_comp`. -/
lemma dWirtingerCoord_star_comp_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerCoord (fun v : (ι → ℂ) => star (f v)) I u =
      star (dWirtingerAntiCoord f I u) :=
  dWirtingerDir_star_comp hf (Pi.single I 1)

/-- The two-term coordinate chain rule for a real-differentiable outer `g`, anti-holomorphic
version, pointwise at `u`: `∂̄_I (g ∘ f) = (∂g/∂f) · ∂̄_I f + (∂g/∂f̄) · ∂̄_I f̄`. Same outer
coefficients as `dWirtingerCoord_comp_apply`, now multiplying the anti-holomorphic inner
derivatives. The `d = Pi.single I 1` case of the foundation `dWirtingerAntiDir_comp`. The
single-term holomorphic specialization `dWirtingerAntiCoord_comp_holomorphic_apply` is proved
from this. -/
lemma dWirtingerAntiCoord_comp_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℝ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (fun v => g (f v)) I u =
      dWirtingerDir g 1 (f u) * dWirtingerAntiCoord f I u
        + dWirtingerAntiDir g 1 (f u) *
          dWirtingerAntiCoord (fun v : (ι → ℂ) => star (f v)) I u :=
  dWirtingerAntiDir_comp hg hf (Pi.single I 1)

/-- The single-term coordinate chain rule for a holomorphic outer `g`, anti-holomorphic
version, pointwise at `u`: `∂̄_I (g ∘ f) = deriv g (f u) · ∂̄_I f`. As in
`dWirtingerCoord_comp_holomorphic_apply`, the `∂g/∂f̄` channel vanishes and `∂g/∂f`
collapses to `deriv g (f u)`. -/
lemma dWirtingerAntiCoord_comp_holomorphic_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (fun v => g (f v)) I u =
      deriv g (f u) * dWirtingerAntiCoord f I u := by
  rw [dWirtingerAntiCoord_comp_apply (hg.restrictScalars ℝ) hf I,
    dWirtingerDir_eq_of_clinear (clinear_of_holomorphic hg 1),
    DifferentiableAt.fderiv_restrictScalars ℝ hg, ContinuousLinearMap.coe_restrictScalars',
    fderiv_apply_one_eq_deriv,
    dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic hg 1), zero_mul, add_zero]

/-- Conjugating the inner field swaps the two operators: `∂̄_I f̄ = conj (∂_I f)`. Dual of
`dWirtingerCoord_star_comp_apply`, the `d = Pi.single I 1` case of the foundation
`dWirtingerAntiDir_star_comp`. -/
lemma dWirtingerAntiCoord_star_comp_apply {u : (ι → ℂ)}
    (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (fun v : (ι → ℂ) => star (f v)) I u =
      star (dWirtingerCoord f I u) :=
  dWirtingerAntiDir_star_comp hf (Pi.single I 1)

end

/-!

## E. Schwarz's theorem for the coordinate operators

Specialisations of the multivariable theory along `Pi.single I 1`: a first coordinate
Wirtinger derivative is again real-differentiable, and **Schwarz's theorem** for the mixed
second derivative on a `C²` function,

  `∂_I ∂̄_J f = ∂̄_J ∂_I f`     (`dWirtingerCoord_dWirtingerAntiCoord_comm`)

This commutation is Kähler-metric hermiticity: with `K` real, `g_{IJ̄} = ∂_I ∂̄_J K` and
`star (g_{JĪ}) = ∂̄_J ∂_I K`.

-/

section

variable {f : (ι → ℂ) → ℂ} {u : (ι → ℂ)}

/-- On a `C²` function the holomorphic coordinate Wirtinger derivative is itself
real-differentiable (`DifferentiableAt ℝ (∂_I f) u`) — the `d = Pi.single I 1` case of
`differentiableAt_dWirtingerDir`. -/
lemma differentiableAt_dWirtingerCoord (hf2 : ContDiffAt ℝ 2 f u) (I : ι) :
    DifferentiableAt ℝ (fun v => dWirtingerCoord f I v) u :=
  differentiableAt_dWirtingerDir hf2 (Pi.single I 1)

/-- On a `C²` function the anti-holomorphic coordinate Wirtinger derivative is itself
real-differentiable (`DifferentiableAt ℝ (∂̄_J f) u`) — the `d = Pi.single J 1` case of
`differentiableAt_dWirtingerAntiDir`. -/
lemma differentiableAt_dWirtingerAntiCoord (hf2 : ContDiffAt ℝ 2 f u) (J : ι) :
    DifferentiableAt ℝ (fun v => dWirtingerAntiCoord f J v) u :=
  differentiableAt_dWirtingerAntiDir hf2 (Pi.single J 1)

/-- **Schwarz's theorem** for the coordinate Wirtinger operators: on a `C²` function the
holomorphic and anti-holomorphic derivatives commute, `∂_I ∂̄_J f = ∂̄_J ∂_I f`. The
`d = Pi.single I 1`, `e = Pi.single J 1` case of the general
`dWirtingerDir_dWirtingerAntiDir_comm`. -/
theorem dWirtingerCoord_dWirtingerAntiCoord_comm (hf2 : ContDiffAt ℝ 2 f u) (I J : ι) :
    dWirtingerCoord (fun v => dWirtingerAntiCoord f J v) I u
      = dWirtingerAntiCoord (fun v => dWirtingerCoord f I v) J u :=
  dWirtingerDir_dWirtingerAntiDir_comm hf2 (Pi.single I 1) (Pi.single J 1)

end

end Physlib.Wirtinger
end
end
