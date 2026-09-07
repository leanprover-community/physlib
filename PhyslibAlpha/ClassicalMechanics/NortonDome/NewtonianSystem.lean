/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Physlib.Mathematics.Calculus.Gradient
public import PhyslibAlpha.ClassicalMechanics.NortonDome.PeanoExistence
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# Conservative Newtonian systems and determinism

## i. Overview

A conservative Newtonian system is a point mass `m` in a configuration space `X` under a
potential `V`, with equation of motion `m r̈ = -∇V(r)`. Physics takes for granted that position
and velocity at one instant fix the motion at all instants. This file makes that a theorem and
states what it costs.

The main result is `NewtonianSystem.isDeterministic_of_hasLocallyLipschitzForce`: if the force
is locally Lipschitz, two solutions with the same position and velocity at one instant coincide
at every instant; in the form usually quoted,
`NewtonianSystem.isDeterministic_of_hasC2Potential`, a `C²` potential suffices. Continuity of
the force is not enough: the Norton dome has a continuous force and a `C¹` potential, and a
particle at rest on its apex may stay or leave at any time (see `NortonDome.Determinism`).

The `NewtonianSystem` defined here asks only for a differentiable potential, the least under
which the equation of motion makes sense. Newton's laws, as stated, are silent on how regular
the force must be, and the dome shows that without some regularity the equation does not
determine the motion. A definition that is to be deterministic must add something the laws do
not state, a regularity condition on the force or a restriction on the admissible motions;
whether that is part of the theory or a choice about it is debated. Each candidate condition is
a separate predicate, so that what it buys is a theorem, and the file takes no side. The
predicates are:

- `IsDeterministic`: position and velocity at one instant fix the solution.
- `SatisfiesFirstLaw`: a body at rest where the force vanishes stays at rest. It follows from
  determinism and is the form of the first law the dome violates. The interval reading follows
  from the second law for every system (`IsSolution.deriv_eq_of_force_eq_zero_on`, section B.3).
- `HasLocallyLipschitzForce`: the hypothesis of the ODE uniqueness theorem. `HasLipschitzForce`
  and `HasC2Potential` are the stronger conditions usually assumed; each implies it and neither
  implies the other.
- `HasLocalSolutions`: existence, kept separate. For a continuous force on a finite-dimensional
  configuration space it follows from Peano's theorem, whose proof is pending in Mathlib;
  section E derives it from the statement in `NortonDome.PeanoExistence`, marked `@[sorryful]`.

The proof of determinism turns the equation of motion into the first-order system
`(r, v)' = (v, F(r)/m)` on `X × X`, applies Mathlib's local uniqueness theorem for integral
curves, and extends to all time by connectedness of the real line. So continuity buys
existence and local Lipschitz continuity buys uniqueness; the file records what each condition
does, not which one is right.

## ii. Key results

- `NewtonianSystem.isDeterministic_of_hasLocallyLipschitzForce`: a locally Lipschitz force
  gives determinism, hence `NewtonianSystem.satisfiesFirstLaw_of_hasLocallyLipschitzForce`
  the first law. `NewtonianSystem.isDeterministic_of_hasC2Potential` and
  `NewtonianSystem.isDeterministic_of_hasLipschitzForce` are the forms usually quoted; the
  chain of implications is drawn in section D.3.
- `NewtonianSystem.ODE_solution_unique_of_locallyLipschitz`: integral curves of a locally
  Lipschitz vector field through a common point coincide for all time.
- `NewtonianSystem`, `NewtonianSystem.force`, `NewtonianSystem.EquationOfMotion` and
  `NewtonianSystem.IsSolution`: the system, the force `-∇V`, Newton's second law, and its
  twice differentiable solutions; `NewtonianSystem.isSolution_const` is rest at an
  equilibrium.
- `NewtonianSystem.IsSolution.deriv_eq_of_force_eq_zero_on`: the first law read on an
  interval, a consequence of the second law for every system.
- `NewtonianSystem.IsDeterministic`, `NewtonianSystem.SatisfiesFirstLaw`,
  `NewtonianSystem.HasLocallyLipschitzForce`, `NewtonianSystem.HasLipschitzForce` and
  `NewtonianSystem.HasC2Potential`: the predicates, with
  `NewtonianSystem.HasLipschitzForce.hasLocallyLipschitzForce` and
  `NewtonianSystem.HasC2Potential.hasLocallyLipschitzForce`.
- `NewtonianSystem.HasLocalSolutions` and `NewtonianSystem.hasLocalSolutions_of_continuous_force`:
  Peano's theorem for Newtonian systems, a continuous force on a finite-dimensional
  configuration space gives local solutions (pending the upstream proof).

## iii. Table of contents

- A. Conservative Newtonian systems
  - A.1. The structure
  - A.2. The force and the equation of motion
  - A.3. Solutions
- B. Determinism and the first law
  - B.1. The properties
  - B.2. Determinism implies the first law
  - B.3. The interval reading of the first law
- C. Regularity conditions
- D. A locally Lipschitz force gives determinism
  - D.1. The phase-space vector field
  - D.2. The phase curve of a solution
  - D.3. The uniqueness theorem
- E. A continuous force gives local solutions
  - E.1. Local existence
  - E.2. The hypotheses of Peano's theorem
  - E.3. The existence theorem

## iv. References

- Earman, J., *A Primer on Determinism*, Reidel (1986).
- Laplace, P.-S., *Essai philosophique sur les probabilités* (1814).
- Montague, R., *Deterministic theories*, in *Formal Philosophy*, Yale University Press (1974).
- Norton, J. D., *The dome: an unexpectedly simple failure of determinism*, Philosophy of
  Science 75 (2008), 786–798.
- `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Solution` (the same uniqueness argument
  for the pendulum).

-/

@[expose] public section

namespace ClassicalMechanics
open Time

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-!

## A. Conservative Newtonian systems

-/

/-!

### A.1. The structure

The potential is asked to be differentiable and no more, so that the force `-∇V` exists and the
equation of motion can be written pointwise; further regularity is added in section C. Physlib's
general notion is `ClassicalMechanics.PointParticle.NewtonianSystem`, finitely many particles
with explicit forces in a reference frame. The structure here is a single mass in a potential,
which is all the dome needs; the two live in different namespaces and no file opens both.

-/

/-- A conservative Newtonian system on the configuration space `X`: a point mass `m` in a
  differentiable potential `V`. Its equation of motion is Newton's second law `m r̈ = -∇V(r)`. -/
structure NewtonianSystem (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] where
  /-- The mass. -/
  m : ℝ
  /-- The potential. -/
  potential : X → ℝ
  m_pos : 0 < m
  potential_differentiable : Differentiable ℝ potential

namespace NewtonianSystem

variable (S : NewtonianSystem X)

/-- The mass of a Newtonian system is not equal to zero. -/
@[simp]
lemma m_ne_zero : S.m ≠ 0 := S.m_pos.ne'

/-!

### A.2. The force and the equation of motion

-/

/-- The force of a Newtonian system, minus the gradient of the potential. -/
noncomputable def force (x : X) : X := -gradient S.potential x

/-- Newton's second law for a Newtonian system: at every instant `m r̈` equals the force at
  the position. -/
def EquationOfMotion (r : Time → X) : Prop :=
  ∀ t, S.m • ∂ₜ (∂ₜ r) t = S.force (r t)

/-!

### A.3. Solutions

A solution is a twice differentiable curve, position and velocity both differentiable, satisfying
the equation of motion: the regularity of `ClassicalMechanics.ReferenceFrame.Particle` and the
least under which the acceleration exists. It is demanded because the pointwise equation, whose
derivatives are zero wherever they do not exist, admits rough accidental solutions. Continuity of
the acceleration is not demanded; for a continuous force it is automatic.

-/

/-- A solution of a Newtonian system is a twice differentiable curve, its position and velocity
  both differentiable, satisfying the equation of motion. -/
def IsSolution (r : Time → X) : Prop :=
  Differentiable ℝ r ∧ Differentiable ℝ (∂ₜ r) ∧ S.EquationOfMotion r

/-- The position along a solution is differentiable. -/
lemma IsSolution.differentiable {S : NewtonianSystem X} {r : Time → X} (h : S.IsSolution r) :
    Differentiable ℝ r := h.1

/-- The velocity along a solution is differentiable. -/
lemma IsSolution.deriv_differentiable {S : NewtonianSystem X} {r : Time → X}
    (h : S.IsSolution r) : Differentiable ℝ (∂ₜ r) := h.2.1

/-- A solution satisfies the equation of motion. -/
lemma IsSolution.equationOfMotion {S : NewtonianSystem X} {r : Time → X}
    (h : S.IsSolution r) : S.EquationOfMotion r := h.2.2

/-- The curve at rest at a point where the force vanishes is a solution. -/
lemma isSolution_const {x : X} (hx : S.force x = 0) : S.IsSolution (fun _ => x) := by
  have h : ∂ₜ (fun _ : Time => x) = fun _ => 0 := funext fun t => Time.deriv_const x
  refine ⟨differentiable_const x, by rw [h]; exact differentiable_const 0, fun t => ?_⟩
  rw [h, Time.deriv_const, hx, smul_zero]

/-!

## B. Determinism and the first law

-/

/-!

### B.1. The properties

Determinism is the statement that position and velocity at one instant fix the motion at all
instants. The first law, in the reading that says more than the second law, is the statement
that a body at rest where no force acts stays at rest; section B.3 compares the readings. Both
are properties of the system, not of a motion.

The definition of determinism is the naive one. Laplace's formulation is about knowledge; the
notion used since Montague and Earman is about models, a theory being deterministic if any two
models agreeing at one instant agree at every instant. `IsDeterministic` is that notion, with
the models taken to be the twice differentiable solutions of one system, defined for all time,
and the state taken to be position and velocity. Four things follow.

- It is a property of one system. That Newtonian mechanics is deterministic is a claim about
  every system in some class, and which class is what this folder is about.
- It is uniqueness only. A system with no solution from some initial datum, or with solutions
  not defined for all time, counts as deterministic here, whereas on Earman's account such
  failures of existence count against determinism. Existence is kept separate, as
  `HasLocalSolutions`.
- It is relative to the class of solutions. Demanding smooth or analytic solutions would
  exclude the departing motions of the dome, which vanish on a half-line and are not `C⁴`, and
  so restore uniqueness by fiat.
- It does not distinguish future from past. The time-reversed motions of the dome arrive at
  rest on the apex and stay, so the state there fixes neither past nor future; Earman's
  futuristic and historical determinism both fail.

-/

/-- A Newtonian system is deterministic if any two solutions with the same position and
  velocity at some instant coincide. This is uniqueness of twice differentiable solutions
  defined for all time, in both directions of time and without existence; see section B.1. -/
def IsDeterministic : Prop :=
  ∀ x y : Time → X, S.IsSolution x → S.IsSolution y →
    ∀ t₀, x t₀ = y t₀ → ∂ₜ x t₀ = ∂ₜ y t₀ → x = y

/-- A Newtonian system satisfies the first law if a solution at rest, at some instant, at a
  point where the force vanishes stays at that point at all instants. -/
def SatisfiesFirstLaw : Prop :=
  ∀ r : Time → X, S.IsSolution r → ∀ t₀, S.force (r t₀) = 0 → ∂ₜ r t₀ = 0 → ∀ t, r t = r t₀

/-!

### B.2. Determinism implies the first law

The curve staying at the equilibrium is a solution with the same position and velocity as the
given one at the given instant, so by determinism it is the given one.

-/

/-- A deterministic Newtonian system satisfies the first law. -/
lemma IsDeterministic.satisfiesFirstLaw {S : NewtonianSystem X} (h : S.IsDeterministic) :
    S.SatisfiesFirstLaw := by
  intro r hr t₀ hF hv t
  have hc := S.isSolution_const hF
  have heq := h r (fun _ => r t₀) hr hc t₀ rfl (by rw [hv, Time.deriv_const])
  exact congrFun heq t

/-!

### B.3. The interval reading of the first law

The first law can be read instantaneously (no force at an instant, no acceleration then), with
an interval in the hypothesis (no force on an interval, constant velocity on it), or with an
interval in the conclusion (at rest at an instant where no force acts, at rest forever). The
first two follow from the second law for every system, the second being the lemma below, and
both hold for the dome. The third, `SatisfiesFirstLaw`, is determinism at an equilibrium; it is
what the dome violates and what Norton's argument is about, so it is the reading taken here.

-/

/-- The first law read on an interval: if the force vanishes along a solution throughout the
  interval `[a, b]`, the velocity is constant on it. This is a consequence of the second law
  alone, and holds for every system. -/
lemma IsSolution.deriv_eq_of_force_eq_zero_on {S : NewtonianSystem X} {r : Time → X}
    (hr : S.IsSolution r) {a b : Time} (hF : ∀ t ∈ Set.Icc a b, S.force (r t) = 0) :
    ∀ t ∈ Set.Icc a b, ∂ₜ r t = ∂ₜ r a := by
  have hv : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => ∂ₜ r (toRealCLE.symm τ))
      (∂ₜ (∂ₜ r) (toRealCLE.symm τ)) τ := fun τ =>
    hasDerivAt_comp_toRealCLE_symm (∂ₜ r) τ (hr.deriv_differentiable _)
  have hconst := constant_of_has_deriv_right_zero (a := toRealCLE a) (b := toRealCLE b)
    (f := fun τ : ℝ => ∂ₜ r (toRealCLE.symm τ))
    (continuous_iff_continuousAt.mpr fun τ => (hv τ).continuousAt).continuousOn
    (fun τ hτ => by
      have hmem : toRealCLE.symm τ ∈ Set.Icc a b := ⟨hτ.1, hτ.2.le⟩
      have hacc : ∂ₜ (∂ₜ r) (toRealCLE.symm τ) = 0 := by
        have h := hr.equationOfMotion (toRealCLE.symm τ)
        rw [hF _ hmem] at h
        exact (smul_eq_zero.mp h).resolve_left S.m_ne_zero
      have h' := hv τ
      rw [hacc] at h'
      exact h'.hasDerivWithinAt)
  intro t ht
  simpa using hconst (toRealCLE t) ⟨ht.1, ht.2⟩

/-!

## C. Regularity conditions

The hypothesis of the ODE uniqueness theorem is a locally Lipschitz force,
`HasLocallyLipschitzForce`. The two stronger conditions usually stated are a globally Lipschitz
force, `HasLipschitzForce`, and a `C²` potential, `HasC2Potential`, whose force is `C¹`.
Neither implies the other: for example, `x ^ 4` has a `C¹` force of unbounded slope, and
`x * |x| / 2` has the Lipschitz force `-|x|` but is not `C²`. The structure `NewtonianSystem`
of section A assumes none of these conditions; they are separate predicates on it.

-/

/-- A Newtonian system has a locally Lipschitz force if its force is Lipschitz on a
  neighbourhood of every point. This is the hypothesis of the uniqueness theorem for ordinary
  differential equations. -/
def HasLocallyLipschitzForce : Prop := LocallyLipschitz S.force

/-- A Newtonian system has a Lipschitz force if its force is globally Lipschitz. -/
def HasLipschitzForce : Prop := ∃ K : NNReal, LipschitzWith K S.force

/-- A Newtonian system has a `C²` potential if its potential is twice continuously
  differentiable; two derivatives are what the uniqueness theory of ordinary differential
  equations uses. -/
def HasC2Potential : Prop := ContDiff ℝ 2 S.potential

/-- A Lipschitz force is locally Lipschitz. -/
lemma HasLipschitzForce.hasLocallyLipschitzForce (h : S.HasLipschitzForce) :
    S.HasLocallyLipschitzForce := by
  obtain ⟨K, hK⟩ := h
  exact hK.locallyLipschitz

/-- The gradient of a `C²` potential is `C¹`. -/
lemma HasC2Potential.contDiff_gradient (h : S.HasC2Potential) :
    ContDiff ℝ 1 (gradient S.potential) :=
  (InnerProductSpace.toDual ℝ X).symm.contDiff.comp
    ((contDiff_succ_iff_fderiv (n := 1)).mp (by rw [one_add_one_eq_two]; exact h)).2.2

/-- The force of a system with a `C²` potential is locally Lipschitz. -/
lemma HasC2Potential.hasLocallyLipschitzForce (h : S.HasC2Potential) :
    S.HasLocallyLipschitzForce :=
  h.contDiff_gradient.locallyLipschitz.neg

/-!

## D. A locally Lipschitz force gives determinism

The equation of motion becomes the first-order system `(r, v)' = (v, F(r)/m)` on `X × X`. If
the force is locally Lipschitz so is this vector field, and the local uniqueness theorem
`ODE_solution_unique_of_eventually` of Mathlib, with the connectedness of the real line, gives
determinism, as in `SimplePendulum.equationOfMotion_unique`.

-/

/-!

### D.1. The phase-space vector field

-/

/-- The phase-space vector field of a Newtonian system, sending `(r, v)` to `(v, F(r)/m)`. -/
noncomputable def phaseVectorField (p : X × X) : X × X :=
  (p.2, S.m⁻¹ • S.force p.1)

/-- If the force of a Newtonian system is locally Lipschitz, so is its phase-space vector
  field. -/
lemma phaseVectorField_locallyLipschitz (h : LocallyLipschitz S.force) :
    LocallyLipschitz S.phaseVectorField := by
  unfold phaseVectorField
  exact LipschitzWith.prod_snd.locallyLipschitz.prodMk
    ((lipschitzWith_smul S.m⁻¹).locallyLipschitz.comp
      (h.comp LipschitzWith.prod_fst.locallyLipschitz))

/-!

### D.2. The phase curve of a solution

-/

/-- The phase curve `τ ↦ (r t, ṙ t)` (with `t = toRealCLE.symm τ`) of a solution is an
  integral curve of the phase-space vector field. -/
lemma phaseCurve_hasDerivAt {r : Time → X} (hr : Differentiable ℝ r)
    (hr' : Differentiable ℝ (∂ₜ r)) (h : S.EquationOfMotion r) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => (r (toRealCLE.symm τ), ∂ₜ r (toRealCLE.symm τ)))
      (S.phaseVectorField (r (toRealCLE.symm τ), ∂ₜ r (toRealCLE.symm τ))) τ := by
  have hacc : ∂ₜ (∂ₜ r) (toRealCLE.symm τ) = S.m⁻¹ • S.force (r (toRealCLE.symm τ)) := by
    rw [← h, smul_smul, inv_mul_cancel₀ S.m_ne_zero, one_smul]
  rw [phaseVectorField, ← hacc]
  exact (hasDerivAt_comp_toRealCLE_symm r τ (hr _)).prodMk
    (hasDerivAt_comp_toRealCLE_symm (∂ₜ r) τ (hr' _))

/-!

### D.3. The uniqueness theorem

Local uniqueness makes the set of instants at which two integral curves through a common point
agree open, continuity makes it closed, and the real line is connected. Applied to the
phase-space vector field this gives the theorem of the file, and sections B, C and D form one
chain, each arrow a theorem:

```
HasC2Potential ────┐
                   ├──▶ HasLocallyLipschitzForce ──▶ IsDeterministic ──▶ SatisfiesFirstLaw
HasLipschitzForce ─┘
```

Naming follows Mathlib: `isDeterministic_of_hasC2Potential` is the arrow from
`HasC2Potential` to `IsDeterministic`.

-/

/-- Integral curves of a locally Lipschitz vector field, defined at all times, which pass
  through the same point at the same instant coincide. -/
lemma ODE_solution_unique_of_locallyLipschitz {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : E → E} (hv : LocallyLipschitz v) {f g : ℝ → E}
    (hf : ∀ τ, HasDerivAt f (v (f τ)) τ) (hg : ∀ τ, HasDerivAt g (v (g τ)) τ)
    {τ₀ : ℝ} (h0 : f τ₀ = g τ₀) : f = g := by
  have hclosed : IsClosed {τ | f τ = g τ} :=
    isClosed_eq (continuous_iff_continuousAt.mpr fun τ => (hf τ).continuousAt)
      (continuous_iff_continuousAt.mpr fun τ => (hg τ).continuousAt)
  have hopen : IsOpen {τ | f τ = g τ} := by
    rw [isOpen_iff_mem_nhds]
    intro τ₁ hτ₁
    obtain ⟨K, s, hs, hKs⟩ := hv (f τ₁)
    have hs' : s ∈ nhds (g τ₁) := by
      rw [← show f τ₁ = g τ₁ from hτ₁]
      exact hs
    refine ODE_solution_unique_of_eventually (v := fun _ => v) (s := fun _ => s)
      (Filter.Eventually.of_forall fun _ => hKs) ?_ ?_ hτ₁
    · filter_upwards [(hf τ₁).continuousAt.preimage_mem_nhds hs] with τ hτ
      exact ⟨hf τ, hτ⟩
    · filter_upwards [(hg τ₁).continuousAt.preimage_mem_nhds hs'] with τ hτ
      exact ⟨hg τ, hτ⟩
  have huniv : {τ | f τ = g τ} = Set.univ :=
    (isClopen_iff.mp ⟨hclosed, hopen⟩).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨τ₀, h0⟩)
  funext τ
  exact Set.eq_univ_iff_forall.mp huniv τ

/-- The uniqueness theorem for Newtonian systems: a Newtonian system with a locally Lipschitz
  force is deterministic. -/
lemma isDeterministic_of_hasLocallyLipschitzForce (h : S.HasLocallyLipschitzForce) :
    S.IsDeterministic := by
  intro x y hx hy t₀ h0 hv0
  have hEq := ODE_solution_unique_of_locallyLipschitz (S.phaseVectorField_locallyLipschitz h)
    (f := fun τ : ℝ => (x (toRealCLE.symm τ), ∂ₜ x (toRealCLE.symm τ)))
    (g := fun τ : ℝ => (y (toRealCLE.symm τ), ∂ₜ y (toRealCLE.symm τ)))
    (S.phaseCurve_hasDerivAt hx.differentiable hx.deriv_differentiable hx.equationOfMotion)
    (S.phaseCurve_hasDerivAt hy.differentiable hy.deriv_differentiable hy.equationOfMotion)
    (τ₀ := toRealCLE t₀)
    (by simp [h0, hv0])
  funext t
  exact (Prod.ext_iff.mp (congrFun hEq (toRealCLE t))).1

/-- Picard–Lindelöf for Newtonian systems: a Newtonian system with a Lipschitz force is
  deterministic. -/
lemma isDeterministic_of_hasLipschitzForce (h : S.HasLipschitzForce) : S.IsDeterministic :=
  S.isDeterministic_of_hasLocallyLipschitzForce h.hasLocallyLipschitzForce

/-- A Newtonian system with a `C²` potential is deterministic. -/
lemma isDeterministic_of_hasC2Potential (h : S.HasC2Potential) : S.IsDeterministic :=
  S.isDeterministic_of_hasLocallyLipschitzForce h.hasLocallyLipschitzForce

/-- A Newtonian system with a locally Lipschitz force satisfies the first law. -/
lemma satisfiesFirstLaw_of_hasLocallyLipschitzForce (h : S.HasLocallyLipschitzForce) :
    S.SatisfiesFirstLaw :=
  (S.isDeterministic_of_hasLocallyLipschitzForce h).satisfiesFirstLaw

/-!

## E. A continuous force gives local solutions

Determinism is uniqueness; the complementary existence property is that every initial position
and velocity is the initial datum of some solution for a short time. For a continuous force on
a finite-dimensional configuration space this is Peano's theorem applied to the phase-space
vector field, as Picard–Lindelöf gives it for the pendulum in
`SimplePendulum.exists_local_solution`. The statement of Peano's theorem is that of
`NortonDome.PeanoExistence`, pending in Mathlib, so the results here are marked `@[sorryful]`.

-/

/-!

### E.1. Local existence

-/

/-- A Newtonian system has local solutions if for every initial position `x₀` and velocity
  `v₀` there are `ε > 0` and a curve `r` with `r 0 = x₀` and `ṙ 0 = v₀` which, at every time
  within `ε` of the initial instant, is differentiable together with its velocity and satisfies
  the equation of motion. -/
def HasLocalSolutions : Prop :=
  ∀ x₀ v₀ : X, ∃ ε > (0 : ℝ), ∃ r : Time → X, r 0 = x₀ ∧ ∂ₜ r 0 = v₀ ∧
    ∀ t : Time, |t.val| ≤ ε → DifferentiableAt ℝ r t ∧ DifferentiableAt ℝ (∂ₜ r) t ∧
      S.m • ∂ₜ (∂ₜ r) t = S.force (r t)

/-!

### E.2. The hypotheses of Peano's theorem

The phase-space vector field is continuous if the force is, and is bounded on the closed unit
ball about the initial datum by compactness; a short enough time interval then gives the
hypotheses of Peano's theorem.

-/

/-- If the force of a Newtonian system is continuous, so is its phase-space vector field. -/
@[fun_prop]
lemma phaseVectorField_continuous (hF : Continuous S.force) :
    Continuous S.phaseVectorField := by
  unfold phaseVectorField
  fun_prop

/-- For a continuous force on a finite-dimensional configuration space, the time-independent
  phase-space vector field satisfies the hypotheses of Peano's theorem about any initial datum,
  on a short enough symmetric time interval and the closed unit ball. -/
lemma exists_isPeano_phaseVectorField [FiniteDimensional ℝ X] (hF : Continuous S.force)
    (p₀ : X × X) :
    ∃ δ > (0 : ℝ), ∃ L : NNReal,
      IsPeano (fun q : ℝ × (X × X) => S.phaseVectorField q.2) (-δ) δ 0 p₀ 1 L := by
  obtain ⟨C, hC⟩ := (ProperSpace.isCompact_closedBall p₀ 1).exists_bound_of_continuousOn
    (S.phaseVectorField_continuous hF).continuousOn
  have hL : (0 : ℝ) ≤ Real.toNNReal C := NNReal.coe_nonneg _
  have hδ : (0 : ℝ) < 1 / (Real.toNNReal C + 1) := by positivity
  refine ⟨1 / (Real.toNNReal C + 1), hδ, Real.toNNReal C, ⟨⟨by linarith, hδ.le⟩, ?_, ?_, ?_⟩⟩
  · exact ((S.phaseVectorField_continuous hF).comp continuous_snd).continuousOn
  · intro t _ x hx
    exact (hC x hx).trans (Real.le_coe_toNNReal C)
  · rw [NNReal.coe_one, sub_zero, zero_sub, neg_neg, max_self, mul_one_div]
    exact div_le_one_of_le₀ (by linarith) (by positivity)

/-!

### E.3. The existence theorem

Peano's theorem gives an integral curve through the initial datum, differentiable in the sense
of `HasDerivWithinAt` on the closed interval, hence with an honest derivative on the open one.
Its first component, pulled back to `Time` through `Time.toRealCLE`, is the required curve; its
derivatives are read off with `Time.deriv_comp_toRealCLE_of_hasDerivAt`.

-/

/-- Peano's theorem for Newtonian systems: a Newtonian system with a continuous force on a
  finite-dimensional configuration space has local solutions. Pending the proof of Peano's
  theorem in Mathlib. -/
@[sorryful]
lemma hasLocalSolutions_of_continuous_force [FiniteDimensional ℝ X]
    (hF : Continuous S.force) : S.HasLocalSolutions := by
  intro x₀ v₀
  obtain ⟨δ, hδ, L, hP⟩ := S.exists_isPeano_phaseVectorField hF (x₀, v₀)
  obtain ⟨α, hα0, hα'⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα : ∀ τ ∈ Set.Ioo (-δ) δ, HasDerivAt α (S.phaseVectorField (α τ)) τ := fun τ hτ =>
    (hα' τ (Set.Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
  have hmem : ∀ t : Time, |t.val| ≤ δ / 2 → Time.toRealCLE t ∈ Set.Ioo (-δ) δ := by
    intro t ht
    have := abs_le.mp ht
    change t.val ∈ Set.Ioo (-δ) δ
    constructor <;> linarith
  have hd1 : ∀ t : Time, Time.toRealCLE t ∈ Set.Ioo (-δ) δ →
      ∂ₜ (fun s => (α (Time.toRealCLE s)).1) t = (α (Time.toRealCLE t)).2 := by
    intro t ht
    have hfst := (ContinuousLinearMap.fst ℝ X X).hasFDerivAt.comp_hasDerivAt
      (Time.toRealCLE t) (hα _ ht)
    apply Time.deriv_comp_toRealCLE_of_hasDerivAt (fun τ => (α τ).1) t
    simpa [Function.comp_def, phaseVectorField] using hfst
  have hev : ∀ t : Time, Time.toRealCLE t ∈ Set.Ioo (-δ) δ →
      ∂ₜ (fun s => (α (Time.toRealCLE s)).1) =ᶠ[nhds t] fun s => (α (Time.toRealCLE s)).2 := by
    intro t ht
    have hU : IsOpen {s : Time | Time.toRealCLE s ∈ Set.Ioo (-δ) δ} :=
      isOpen_Ioo.preimage Time.toRealCLE.continuous
    exact Filter.eventuallyEq_of_mem (hU.mem_nhds ht) fun s hs => hd1 s hs
  have hd2 : ∀ t : Time, Time.toRealCLE t ∈ Set.Ioo (-δ) δ →
      ∂ₜ (∂ₜ (fun s => (α (Time.toRealCLE s)).1)) t =
        (S.phaseVectorField (α (Time.toRealCLE t))).2 := by
    intro t ht
    have hsnd := (ContinuousLinearMap.snd ℝ X X).hasFDerivAt.comp_hasDerivAt
      (Time.toRealCLE t) (hα _ ht)
    have h2 : ∂ₜ (fun s => (α (Time.toRealCLE s)).2) t =
        (S.phaseVectorField (α (Time.toRealCLE t))).2 := by
      apply Time.deriv_comp_toRealCLE_of_hasDerivAt (fun τ => (α τ).2) t
      simpa [Function.comp_def] using hsnd
    rw [Time.deriv_eq, (hev t ht).fderiv_eq, ← Time.deriv_eq, h2]
  have h0 : Time.toRealCLE (0 : Time) ∈ Set.Ioo (-δ) δ := by
    rw [map_zero]
    constructor <;> linarith
  refine ⟨δ / 2, half_pos hδ, fun t => (α (Time.toRealCLE t)).1, ?_, ?_, fun t ht => ?_⟩
  · show (α (Time.toRealCLE 0)).1 = x₀
    rw [map_zero, hα0]
  · rw [hd1 0 h0, map_zero, hα0]
  · have hαt := (hα _ (hmem t ht)).differentiableAt
    refine ⟨hαt.fst.comp t Time.toRealCLE.differentiableAt, ?_, ?_⟩
    · exact (hev t (hmem t ht)).differentiableAt_iff.mpr
        (hαt.snd.comp t Time.toRealCLE.differentiableAt)
    · rw [hd2 t (hmem t ht)]
      show S.m • (S.m⁻¹ • S.force _) = _
      rw [smul_smul, mul_inv_cancel₀ S.m_ne_zero, one_smul]

end NewtonianSystem

end ClassicalMechanics

end
