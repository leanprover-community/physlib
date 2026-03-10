/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import PhysLean.Mathematics.VariationalCalculus.HasVarAdjDeriv
/-!

# Variational gradient

Definition of variational gradient that allows for formal treatment of variational calculus
as used in physics textbooks.
-/

@[expose] public section

open MeasureTheory ContDiff InnerProductSpace

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasureSpace X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U]

/-- Function `grad` is variational gradient of functional `S` at point `u`.

This formalizes the notion of variational gradient `δS/δu` of a functional `S` at a point `u`.

However, it is not defined for a functional `S : (X → U) → ℝ` but rather for the function
`S' : (X → U) → (X → ℝ)` which is related to the usual functional as `S u = ∫ x, S' (u x) x ∂μ`.
For example for action integral, `S u = ∫ t, L (u t) (deriv u t)` we have
`S' u t = L (u t) (deriv u t)`. Working with `S'` rather than with `S` allows us to ignore certain
technicalities with integrability.

Examples:

Euler-Lagrange equations:
```
δ/δx ∫ L(x,ẋ) dt = ∂L/∂ x - d/dt (∂L/∂ẋ)
```
can be expressed as
```
HasVarGradientAt
  (fun u t => L (u t) (deriv u t))
  (fun t =>
    deriv (L · (deriv u t)) ((u t))
    -
    deriv (fun t' => deriv (L (u t') ·) (deriv u t')) t)
  u
```

Laplace equation is variational gradient of Dirichlet energy:
```
δ/δu ∫ 1/2*‖∇u‖² = - Δu
```
can be expressed as
```
HasVarGradientAt
  (fun u t => 1/2 * deriv u t^2)
  (fun t => - deriv (deriv u) t)
  u
```
-/
inductive HasVarGradientAt (F : (X → U) → (X → ℝ)) (grad : X → U) (u : X → U) : Prop
  | intro (F') (hF' : HasVarAdjDerivAt F F' u) (hgrad : grad = F' (fun _ => 1))

lemma HasVarGradientAt.add (F F' : (X → U) → (X → ℝ))
    {grad grad' : X → U} {u : X → U} [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts (@volume X _)]
    (h : HasVarGradientAt F grad u) (h' : HasVarGradientAt F' grad' u) :
    HasVarGradientAt (F + F') (grad + grad') u := by
  obtain ⟨F1,hF1,eq1⟩ := h
  obtain ⟨F2,hF2,eq2⟩ := h'
  apply HasVarGradientAt.intro (F1 + F2)
  · apply hF1.add (V := ℝ)
    exact hF2
  · simp
    rw [eq1, eq2]

lemma HasVarGradientAt.sum {ι : Type} [Fintype ι] (F : ι → (X → U) → (X → ℝ))
    {grad : ι → X → U} {u : X → U} (hu : ContDiff ℝ ∞ u) [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts (@volume X _)]
    (h : ∀ i, HasVarGradientAt (F i) (grad i) u) :
    HasVarGradientAt (fun v x => ∑ i, F i v x) (∑ i, grad i) u := by
  let P (ι : Type) [Fintype ι] : Prop :=
    ∀ (F : ι → (X → U) → (X → ℝ)), ∀ (F' : ι → X → U), ∀ u, ∀ (hu : ContDiff ℝ ∞ u),
    ∀ (hF : ∀ i, HasVarGradientAt (F i) (F' i) u),
    HasVarGradientAt (fun φ x => ∑ i, F i φ x) (∑ i, F' i) u
  have hp : P ι := by
    apply Fintype.induction_empty_option
    · intro ι ι' inst e hp F F' u hu ih
      convert hp (fun i => F (e i)) (fun i => F' (e i)) u hu (by
        intro i
        simpa using ih (e i))
      rw [← @e.sum_comp]
      rw [← @e.sum_comp]
    · intro i ι' u hu ih
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      refine intro (fun _ _ => 0) ?_ ?_
      apply HasVarAdjDerivAt.const
      fun_prop
      fun_prop
      simp
      rfl
    · intro i ι' hp F F' u hu ih
      simp only [Fintype.sum_option]
      apply HasVarGradientAt.add
      exact ih none
      exact hp (fun i_1 => F (some i_1)) (fun i_1 => F' (some i_1)) u hu fun i_1 => ih (some i_1)
  exact hp F grad u hu h

lemma HasVarGradientAt.neg {F : (X → U) → (X → ℝ)}
    {grad : X → U} {u : X → U}
    (h : HasVarGradientAt F grad u) :
    HasVarGradientAt (-F) (-grad) u := by
  obtain ⟨F',hF',eq⟩ := h
  apply HasVarGradientAt.intro (-F')
  · apply hF'.neg (V := ℝ)
  · simp
    rw [eq]

open Classical in

/--
The variational gradient of a function `F : (X → U) → (X → ℝ)` evaluated
at a function `u : X → U`.

This not defined defined for a functional `S : (X → U) → ℝ` but rather for the function
`F : (X → U) → (X → ℝ)` which is the integrand of the functional `S u = ∫ x, F (u x) x ∂μ`.
For example for action integral, `S u = ∫ t, L (u t) (deriv u t)` we have
`S' u t = L (u t) (deriv u t)`.

On functions `F : (X → U) → (X → ℝ)` which do not have a variational gradient,
this function is defined to give `0`.
-/
noncomputable def varGradient (F : (X → U) → (X → ℝ)) (u : X → U) : X → U :=
  if h : ∃ grad, HasVarGradientAt F grad u then
    choose h
  else
    0

@[inherit_doc varGradient]
macro "δ" u:term ", " "∫ " x:term ", " b:term : term =>
  `(varGradient (fun $u $x => $b))

@[inherit_doc varGradient]
macro "δ" "(" u:term " := " u':term ")" ", " "∫ " x:term ", " b:term : term =>
  `(varGradient (fun $u $x => $b) $u')

namespace HasVarGradientAt

variable
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasureSpace X] [OpensMeasurableSpace X]
    [IsFiniteMeasureOnCompacts (@volume X _)] [(@volume X _).IsOpenPosMeasure]

lemma unique
    {S' : (X → U) → (X → ℝ)} {grad grad' : X → U} {u : X → U}
    (h : HasVarGradientAt S' grad u) (h' : HasVarGradientAt S' grad' u) :
    grad = grad' := by
  obtain ⟨F,hF,eq⟩ := h
  obtain ⟨G,hG,eq'⟩ := h'
  rw[eq,eq',hF.unique hG (fun _ => 1) (by fun_prop)]

open Classical in
protected lemma varGradient
    (F : (X → U) → (X → ℝ)) (grad : X → U) (u : X → U)
    (hF : HasVarGradientAt F grad u) :
    varGradient F u = grad := by
  have h := Exists.intro grad hF (p:= fun grad' => HasVarGradientAt F grad' u)
  unfold varGradient;
  simp[h, hF.unique h.choose_spec]
