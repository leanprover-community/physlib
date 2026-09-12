/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Zhi Kai Pong, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Physlib.SpaceAndTime.Time.InnerProductSpace
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!

# Time Derivatives

## i. Overview

In this module we define and prove basic lemmas about derivatives of functions on `Time`.

## ii. Key results

- `deriv` : The derivative of a function `Time → M` at a given time.
- `manifoldDeriv` : The derivative of a function from `Time` to a manifold.
- `derivVec` : The derivative of a function from `Time` into a torsor, such as `Space d`,
  valued in the vector space of displacements of that torsor.
- `hasDerivAt_comp_toRealCLE_symm` : The time derivative as a `HasDerivAt` on `ℝ`, for a curve
  reparametrised through the canonical equivalence `toRealCLE.symm : ℝ ≃L[ℝ] Time`.
- `deriv_comp_toRealCLE_of_hasDerivAt` : Its converse, a `HasDerivAt` on `ℝ` read as the time
  derivative of the curve pulled back to `Time` through `toRealCLE`.
- `deriv_comp_neg` and `deriv_deriv_comp_neg` : The first and second time derivatives under the
  reversal of time `t ↦ -t`.

## iii. Table of contents

- A. The definition of the derivative
  - A.1. Derivatives of functions into vector spaces
  - A.2. The derivative through the canonical equivalence with `ℝ`
  - A.3. Derivatives of functions into manifolds
  - A.4. Derivatives of functions into torsors
- B. Linearlity properties of the derivative
- C. Derivative of constant functions
- D. Smoothness properties and the reversal of time
- E. Derivatives of components
- F. Derivatives of trajectories into `Space`

## iv. References

* None.
-/

@[expose] public section

namespace Time

variable {M : Type} {d : ℕ} {t : Time}

/-!

## A. The definition of the derivative

-/

/-!

### A.1. Derivatives of functions into vector spaces

-/

/-- Given a function `f : Time → M` the derivative of `f`. -/
noncomputable def deriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) : Time → M :=
  (fun t => fderiv ℝ f t 1)

@[inherit_doc deriv]
scoped notation "∂ₜ" => deriv

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) (t : Time) : Time.deriv f t = fderiv ℝ f t 1 := rfl

/-!

### A.2. The derivative through the canonical equivalence with `ℝ`

`Time` is identified with `ℝ` by the continuous linear equivalence `toRealCLE`. Precomposing a
curve `w : Time → M` with `toRealCLE.symm : ℝ ≃L[ℝ] Time` gives a curve on `ℝ`, whose Mathlib
derivative (`HasDerivAt`) at `τ` is the time derivative `∂ₜ w` evaluated at `toRealCLE.symm τ`.
This is the bridge through which Mathlib's calculus and ODE theory on `ℝ` applies to curves on
`Time`. Conversely, a `HasDerivAt` on `ℝ` at `toRealCLE t` is the time derivative at `t` of the
curve pulled back to `Time` through `toRealCLE`.

-/

/-- The canonical equivalence `toRealCLE.symm : ℝ ≃L[ℝ] Time` sends `1 : ℝ` to `1 : Time`. -/
lemma toRealCLE_symm_one : toRealCLE.symm (1 : ℝ) = (1 : Time) := by
  simp [toRealCLE]

/-- Bridge from the time derivative to `HasDerivAt`: if `w : Time → M` is differentiable at
`toRealCLE.symm τ`, then the curve `τ ↦ w (toRealCLE.symm τ)` on `ℝ` has derivative
`∂ₜ w (toRealCLE.symm τ)` at `τ`. -/
lemma hasDerivAt_comp_toRealCLE_symm [NormedAddCommGroup M] [NormedSpace ℝ M]
    (w : Time → M) (τ : ℝ) (hw : DifferentiableAt ℝ w (toRealCLE.symm τ)) :
    HasDerivAt (fun τ : ℝ => w (toRealCLE.symm τ)) (∂ₜ w (toRealCLE.symm τ)) τ := by
  apply hw.hasFDerivAt.comp_hasDerivAt_of_eq τ _ rfl
  exact Time.toRealCLE_symm_one ▸ toRealCLE.symm.hasFDerivAt.hasDerivAt

/-- The converse of the bridge `hasDerivAt_comp_toRealCLE_symm`: if the curve `γ : ℝ → M` has
derivative `v` at `toRealCLE t`, then the curve `t ↦ γ (toRealCLE t)` on `Time` has time
derivative `v` at `t`. -/
lemma deriv_comp_toRealCLE_of_hasDerivAt [NormedAddCommGroup M] [NormedSpace ℝ M]
    (γ : ℝ → M) (t : Time) (v : M) (h : HasDerivAt γ v (toRealCLE t)) :
    ∂ₜ (fun s => γ (toRealCLE s)) t = v := by
  rw [Time.deriv_eq, fderiv_fun_comp _ h.differentiableAt toRealCLE.differentiableAt,
    toRealCLE.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    fderiv_eq_smul_deriv, h.deriv]
  exact Eq.trans (by rfl) (Time.one_val ▸ one_smul _ v)

/-- The time derivative of `t ↦ γ t.val` at `t` is the derivative of `γ` at `t.val`. -/
lemma deriv_comp_val {γ : ℝ → ℝ} {t : Time} {v : ℝ} (h : HasDerivAt γ v t.val) :
    ∂ₜ (fun s : Time => γ s.val) t = v :=
  deriv_comp_toRealCLE_of_hasDerivAt γ t v h

/-- The time derivative of any `f : Time → ℝ` at `t` is the derivative at `t.val` of the curve
  `τ ↦ f ⟨τ⟩` on `ℝ`. -/
lemma deriv_eq_of_hasDerivAt {f : Time → ℝ} {t : Time} {v : ℝ}
    (h : HasDerivAt (fun τ : ℝ => f ⟨τ⟩) v t.val) : ∂ₜ f t = v :=
  deriv_comp_toRealCLE_of_hasDerivAt (fun τ : ℝ => f ⟨τ⟩) t v h

/-- A curve `f : Time → ℝ` differentiable at `⟨τ⟩` gives the curve `σ ↦ f ⟨σ⟩` on `ℝ`,
  whose Mathlib derivative at `τ` is the time derivative `∂ₜ f ⟨τ⟩`. -/
lemma hasDerivAt_mk_of_differentiableAt {f : Time → ℝ} {τ : ℝ}
    (hf : DifferentiableAt ℝ f ⟨τ⟩) :
    HasDerivAt (fun σ : ℝ => f ⟨σ⟩) (∂ₜ f ⟨τ⟩) τ :=
  hasDerivAt_comp_toRealCLE_symm f τ hf

/-!

### A.3. Derivatives of functions into manifolds

-/

open Manifold in
/-- The time derivative of a function from `Time` to a manifold, as a tangent vector at
the value of the function. -/
noncomputable def manifoldDeriv {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] (f : Time → N) : (t : Time) → TangentSpace I (f t) :=
  fun t => mfderiv 𝓘(ℝ, Time) I f t ((1 : Time) : TangentSpace 𝓘(ℝ, Time) t)

open Manifold in
lemma manifoldDeriv_eq {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] (f : Time → N) (t : Time) :
    manifoldDeriv I f t =
      mfderiv 𝓘(ℝ, Time) I f t ((1 : Time) : TangentSpace 𝓘(ℝ, Time) t) := rfl

open Manifold in
/-- The time derivative is the manifold derivative for functions into normed spaces. -/
lemma deriv_eq_mfderiv [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → M) (t : Time) :
    deriv f t =
      mfderiv 𝓘(ℝ, Time) 𝓘(ℝ, M) f t
        ((1 : Time) : TangentSpace 𝓘(ℝ, Time) t) := by
  rw [deriv_eq, ← mfderiv_eq_fderiv]
  rfl

open Manifold in
lemma deriv_eq_manifoldDeriv [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → M) (t : Time) :
    deriv f t = manifoldDeriv 𝓘(ℝ, M) f t := by
  rw [deriv_eq_mfderiv, manifoldDeriv_eq]

set_option backward.isDefEq.respectTransparency false in
open Manifold in
@[simp]
lemma manifoldDeriv_const {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] (n : N) :
    manifoldDeriv I (fun _ : Time => n) t = 0 := by
  simp [manifoldDeriv]

/-!

### A.4. Derivatives of functions into torsors

A trajectory in physical space is a curve of points, and its velocity is a displacement per
unit time, that is a vector. For a torsor `P` over a vector space `V`, for example
`Space d` over `EuclideanSpace ℝ (Fin d)`, the derivative of a curve `f : Time → P` is
therefore valued in `V` rather than in `P`. It is defined by differentiating the displacement
curve `s ↦ f s -ᵥ f t`, which is `V`-valued, so that no origin of `P` is ever chosen. The
reference point used to form the displacement is irrelevant, see `derivVec_eq_fderiv_vsub`.

-/

/-- The time derivative of a trajectory into a torsor `P` over a vector space `V`,
valued in `V`. For a trajectory `f : Time → Space d` this is the velocity, a spatial vector in
`EuclideanSpace ℝ (Fin d)` rather than a point of `Space d`. -/
noncomputable def derivVec {V P : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddTorsor V P] (f : Time → P) : Time → V :=
  fun t => fderiv ℝ (fun s => f s -ᵥ f t) t 1

@[inherit_doc derivVec]
scoped notation "∂ₜᵥ" => derivVec

lemma derivVec_eq {V P : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddTorsor V P] (f : Time → P) (t : Time) :
    ∂ₜᵥ f t = fderiv ℝ (fun s => f s -ᵥ f t) t 1 := rfl

/-- The derivative of a trajectory into a torsor does not depend on the reference point used
to form the displacement: any base point `p` gives the same derivative. The normed hypotheses on
`V` here come from `fderiv_add_const`; the definition itself needs only a topological vector
space. -/
lemma derivVec_eq_fderiv_vsub {V P : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [AddTorsor V P] (f : Time → P) (p : P) (t : Time) :
    ∂ₜᵥ f t = fderiv ℝ (fun s => f s -ᵥ p) t 1 := by
  have h : (fun s => f s -ᵥ f t) = fun s => (f s -ᵥ p) + (p -ᵥ f t) := by
    funext s
    rw [vsub_add_vsub_cancel]
  rw [derivVec_eq, h, fderiv_add_const]

/-!

## B. Linearlity properties of the derivative

-/

lemma deriv_smul (f : Time → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂ₜ (fun t => k • f t) t = k • ∂ₜ (fun t => f t) t := by
  rw [deriv, fderiv_fun_const_smul]
  rfl
  fun_prop

lemma deriv_neg [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) :
    ∂ₜ (-f) t = -∂ₜ f t := by
  rw [deriv, fderiv_neg]
  rfl

lemma deriv_add [NormedAddCommGroup M] [NormedSpace ℝ M] (f g : Time → M)
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    ∂ₜ (fun s => f s + g s) t = ∂ₜ f t + ∂ₜ g t := by
  simp only [Time.deriv_eq]
  rw [fderiv_fun_add hf hg, _root_.add_apply]

lemma deriv_fun_sum {ι : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (s : Finset ι) (a : ι → Time → M) (ha : ∀ i ∈ s, DifferentiableAt ℝ (a i) t) :
    ∂ₜ (fun x => ∑ i ∈ s, a i x) t = ∑ i ∈ s, ∂ₜ (a i) t := by
  simp only [Time.deriv_eq]
  rw [fderiv_fun_sum ha, _root_.sum_apply]

lemma deriv_mul_const (f : Time → ℝ) (c : ℝ) (hf : DifferentiableAt ℝ f t) :
    ∂ₜ (fun s => f s * c) t = ∂ₜ f t * c := by
  simp only [Time.deriv_eq]
  rw [fderiv_mul_const hf c, _root_.smul_apply, smul_eq_mul, mul_comm]

/-- Quotient rule for `Time.deriv` on real-valued functions: if `c` and `g` are
  differentiable at `t` and `g t ≠ 0`, then
  `∂ₜ (c / g) t = (∂ₜ c t * g t - c t * ∂ₜ g t) / (g t)^2`. -/
lemma deriv_div {c g : Time → ℝ}
    (hc : DifferentiableAt ℝ c t) (hg : DifferentiableAt ℝ g t) (hgz : g t ≠ 0) :
    ∂ₜ (fun s => c s / g s) t =
      (∂ₜ c t * g t - c t * ∂ₜ g t) / (g t) ^ 2 := by
  repeat rw [Time.deriv_eq]
  ring_nf
  simp [fderiv_fun_mul hc (DifferentiableAt.fun_inv (by fun_prop) hgz),
    fderiv_fun_comp t (differentiableAt_inv hgz) hg]
  field_simp
  ring

/-!

## C. Derivative of constant functions

-/

@[simp]
lemma deriv_const [NormedAddCommGroup M] [NormedSpace ℝ M] (m : M) :
    ∂ₜ (fun _ => m) t = 0 := by
  rw [deriv]
  simp

/-- A trajectory constant at a point of a torsor has zero derivative. -/
@[simp]
lemma derivVec_const {V P : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddTorsor V P] (p : P) :
    ∂ₜᵥ (fun _ => p) t = (0 : V) := by
  simp [derivVec]

/-!

## D. Smoothness properties and the reversal of time

-/

open MeasureTheory ContDiff InnerProductSpace Time

@[fun_prop]
lemma val_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n Time.val := by
  change ContDiff ℝ n toRealCLM
  fun_prop

@[fun_prop]
lemma deriv_differentiable_of_contDiff {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (∂ₜ f) := by
  unfold deriv
  change Differentiable ℝ ((fun x => x 1) ∘ (fun t => fderiv ℝ f t))
  apply Differentiable.comp
  · fun_prop
  · rw [contDiff_infty_iff_fderiv, contDiff_infty_iff_fderiv] at hf
    exact hf.2.1

@[fun_prop]
lemma deriv_contDiff_of_contDiff {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (∂ₜ f) := by
  unfold deriv
  change ContDiff ℝ ∞ ((fun x => x 1) ∘ (fun t => fderiv ℝ f t))
  apply ContDiff.comp <;> fun_prop

/-- The time derivative of a `C^(n+1)` curve is `C^n`. -/
@[fun_prop]
lemma deriv_contDiff_of_contDiff_succ {M : Type} {n : WithTop ℕ∞}
    [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (∂ₜ f) := by
  unfold deriv
  change ContDiff ℝ n ((fun x => x 1) ∘ (fun t => fderiv ℝ f t))
  exact ContDiff.comp (by fun_prop) (contDiff_succ_iff_fderiv.mp hf).2.2

/-- The time derivative of a `C²` curve is differentiable. -/
@[fun_prop]
lemma deriv_differentiable_of_contDiff_two {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (∂ₜ f) :=
  (deriv_contDiff_of_contDiff_succ (n := 1) f (by rw [one_add_one_eq_two]; exact hf)).differentiable
    (by simp)

@[fun_prop]
lemma deriv_contDiff_of_space {n} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → Space d → M) (hf : ContDiff ℝ (n + 1) ↿f) :
    ContDiff ℝ n fun (x : Space d) => (∂ₜ fun t => f t x) t := by
  unfold deriv
  fun_prop

/-- The chain rule for the time derivative under the reversal of time: the derivative of
`t ↦ f (-t)` at `t` is minus the derivative of `f` at `-t`. -/
lemma deriv_comp_neg {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → M) (t : Time) (hf : DifferentiableAt ℝ f (-t)) :
    ∂ₜ (fun s => f (-s)) t = -∂ₜ f (-t) := by
  rw [Time.deriv_eq, Time.deriv_eq, fderiv_fun_comp _ hf (by fun_prop), fderiv_fun_neg]
  simp

/-- The second derivative is unchanged by the reversal of time: for a `C²` curve `f`, the second
derivative of `t ↦ f (-t)` at `t` is the second derivative of `f` at `-t`, the two changes of sign
cancelling. -/
lemma deriv_deriv_comp_neg {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → M) (hf : ContDiff ℝ 2 f) (t : Time) :
    ∂ₜ (∂ₜ (fun s => f (-s))) t = ∂ₜ (∂ₜ f) (-t) := by
  rw [← neg_neg (∂ₜ (∂ₜ f) (-t)),
    ← deriv_comp_neg _ _ ((deriv_differentiable_of_contDiff_two f hf) _), ← Time.deriv_neg]
  congr
  ext
  exact deriv_comp_neg f _ (hf.differentiable (by simp) _)

/-!

## E. Derivatives of components

-/

lemma differentiable_euclid {f : Time → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i, Differentiable ℝ (fun t => f t i)) :
    Differentiable ℝ f := by
  rw [differentiable_euclidean]
  fun_prop

/-- Chain rule for a real function of one coordinate of a curve in Euclidean space: the time
derivative of `t ↦ f (r t i)` is `f'` times the `i`-th component of the velocity, where `f'` is
the derivative of `f` at `r t i`. -/
lemma deriv_comp_coord {ι : Type} [Fintype ι] {f : ℝ → ℝ} {f' : ℝ}
    {r : Time → EuclideanSpace ℝ ι} {t : Time}
    (i : ι) (hr : DifferentiableAt ℝ r t) (hf : HasDerivAt f f' (r t i)) :
    ∂ₜ (fun s => f (r s i)) t = f' * ∂ₜ r t i := by
  have h1 : HasFDerivAt (fun s : Time => r s i)
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ r t)) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t hr.hasFDerivAt
  have h2 : HasFDerivAt (fun s : Time => f (r s i)) _ t := hf.comp_hasFDerivAt t h1
  rw [Time.deriv_eq, h2.fderiv, Time.deriv_eq]
  simp

lemma deriv_euclid { μ} {f : Time→ EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (t : Time) :
    deriv (fun t => f t μ) t = deriv (fun t => f t) t μ := by
  rw [deriv_eq]
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) t 1 = _
  rw [fderiv_comp]
  · simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    PiLp.proj_apply]
    rw [← deriv_eq]
  · fun_prop
  · fun_prop

lemma fderiv_euclid { μ} {f : Time→ EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (t dt : Time) :
    fderiv ℝ (fun t => f t μ) t dt = fderiv ℝ (fun t => f t) t dt μ := by
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) t dt = _
  rw [fderiv_comp]
  · simp [-EuclideanSpace.coe_proj]
  · fun_prop
  · fun_prop

lemma deriv_lorentzVector {d : ℕ} {f : Time → Lorentz.Vector d}
    (hf : Differentiable ℝ f) (t : Time) (i : Fin 1 ⊕ Fin d) :
    deriv (fun t => f t i) t = deriv (fun t => f t) t i := by
  rw [deriv_eq]
  change fderiv ℝ (Lorentz.Vector.coordCLM i ∘ fun x => f x) t 1 = _
  rw [fderiv_comp]
  · simp
    rw [← deriv_eq]
    rfl
  · fun_prop
  · fun_prop

lemma deriv_space {d : ℕ} {f : Time → Space d}
    (hf : Differentiable ℝ f) (t : Time) (i : Fin d) :
    deriv (fun s => f s i) t = deriv f t i :=
  (Space.fderiv_space_components i f hf t 1).symm

/-!

## F. Derivatives of trajectories into `Space`

For a trajectory `f : Time → Space d` of points in space, the torsor derivative `∂ₜᵥ f` is
valued in the displacement space `EuclideanSpace ℝ (Fin d)`. Componentwise it agrees with the
time derivatives of the coordinates, and under the identification of `Space d` with its
displacement space given by the (arbitrary) zero point it recovers the vector space derivative
`∂ₜ f`. The latter bridges `∂ₜᵥ` to the existing `∂ₜ` API.

Note that `Space d` carries two `AddTorsor` instances: the intended one over
`EuclideanSpace ℝ (Fin d)`, and one over itself coming from the module structure on `Space d`.
Instance resolution selects the former, so `∂ₜᵥ` of a trajectory in `Space d` is valued in
`EuclideanSpace ℝ (Fin d)` as intended.

-/

/-- The components of the torsor derivative of a trajectory in `Space d` are the time
derivatives of the coordinates of the trajectory. -/
lemma derivVec_space {f : Time → Space d} (hf : Differentiable ℝ f) (t : Time) (i : Fin d) :
    ∂ₜᵥ f t i = ∂ₜ (fun s => f s i) t := by
  have hv : Differentiable ℝ (fun s => (f s -ᵥ f t : EuclideanSpace ℝ (Fin d))) := by
    apply differentiable_euclid
    intro j
    simp only [Space.vsub_apply]
    exact ((Space.eval_differentiable j).comp hf).sub_const (f t j)
  rw [derivVec_eq, deriv_eq, ← fderiv_euclid hv t 1]
  simp only [Space.vsub_apply]
  rw [fderiv_sub_const]

/-- The torsor derivative of a trajectory in `Space d` agrees with the vector space derivative
`∂ₜ` under the identification of `Space d` with its displacement space given by the zero
point. -/
lemma derivVec_eq_deriv_vsub_zero {f : Time → Space d} (hf : Differentiable ℝ f) (t : Time) :
    ∂ₜᵥ f t = ∂ₜ f t -ᵥ (0 : Space d) := by
  ext i
  rw [derivVec_space hf t i, deriv_space hf t i, Space.vsub_apply]
  simp

end Time
