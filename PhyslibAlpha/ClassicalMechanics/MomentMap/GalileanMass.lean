/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
/-!

# The mass as a cohomology class of the Galilean Lie algebra (Souriau)

The total mass as a non-trivial cohomology class of the Galilean Lie algebra (Souriau).

## i. Overview

In chapter 12 of Structure des systèmes dynamiques (Dunod 1970), Souriau computes the moment of
the Galilean group acting on the evolution space of a system of material points. The moment is a
torsor `μ = {l, g, p, E}` (12.122)-(12.123): `l` is the angular momentum and `p` the momentum
(12.140), and `g = m R - p t` with `R` the centre of gravity (12.141). The Lagrange form `σ` of the
system satisfies (12.134), `σ(Z_V(y))(Z'_V(y)) = μ[Z, Z'] + m f₀(Z)(Z')`, where
`f₀(Z)(Z') = ⟨β, γ'⟩ - ⟨β', γ⟩` (12.130) and `m = Σ_j m_j` is the total mass (12.135). Souriau
remarks (12.136) that the total mass can be interpreted as characterising the corresponding
cohomology class of the Galilean group, and that this class is never zero.

This file proves these facts at the level of the Lie algebra for `N` free material points in
`ℝ³ = Fin 3 → ℝ` (no forces, `F_j = 0`; with the choice `B_j = 0` of (12.49), which (12.135)
imposes on an isolated system, (12.44) gives `E_j = 0` and (12.45) reduces to (12.40)). An element
`Z = (ω, β, γ, ε)` of the Galilean Lie algebra (12.74), (12.118) is a rotation `ω` (an axial
vector), a change of velocity `β`, a space translation `γ` and a time translation `ε`; it acts on
the evolution space, whose points are `y = (t, r_j, v_j)` (12.76), by the affine vector field
(12.119). The bracket is Souriau's (6.12 b), `[Z, Z']_V = [Z_V, Z'_V]`, where the bracket of two
vector fields is (2.45), here `DZ'_V(Z_V) - DZ_V(Z'_V)` (`EvolutionSpace.vectorField_bracket`);
this is the usual Lie bracket of vector fields (Mathlib's `VectorField.lieBracket`). The matrices
(12.74) are not formalised; on them this bracket reads `[Z, Z'] = Z'Z - ZZ'`, as in (11.22 a), the
opposite of the usual matrix commutator.

What is not formalised here:
- the Galilean group itself, its action (12.73), (12.76) and its cocycle `θ₀` (12.126)-(12.128),
  hence the statement of p. 151 that `θ₀` is not a coboundary of the group (definition (11.19)),
  used in (12.136). The algebra-level result of this file implies it, because the derivative of a
  group coboundary `Δ(μ₀)` is `μ₀[Z, Z']` (p. 116, note (1)); this implication is not formalised.
  Physlib has `GalileanGroup` in `Physlib.SpaceAndTime.GalileanGroup.Basic`, whose rotation part
  ranges over the full orthogonal group; Souriau's group (12.73) takes `A ∈ SO(3)` and is
  connected (p. 139). Both have the same Lie algebra, with which this file works in dimension `3`,
  in Souriau's parametrisation; the file links it to neither group;
- `GalileanAlgebra` has no vector space or `LieRing` structure here, only `Zero` and `Add`; the
  Jacobi identity is proved as an equation;
- that the vector field (12.119), taken as printed, is the derivative (6.11) of the action (12.76);
- the reading of (12.135) as the solution of the system (12.124), (12.134) for a general isolated
  system (`B_j = 0`, `Σ_j E_j = 0`, `Σ_j r_j × E_j = 0`): for free points the explicit moment and
  `m = Σ_j m_j` are verified, not derived; the uniqueness of `m` in (12.134) follows from
  `lagrangeForm_vectorField` and `smul_cocycle_isCoboundary_iff` but is not stated;
- the dimension `1` of (12.131), the second half of (12.136) (Hamilton's Lagrangian is not
  invariant), forces, the converse of (12.48), the invariance of `σ` (12.72), (12.76), and the
  uniqueness of the moment up to a constant (the constant in `E` is a choice);
- the evolution space is presymplectic, not symplectic (p. 148, (12.114));
  `EvolutionSpace.lagrangeForm_motion` shows that `σ` is degenerate, and `σ` depends on the point
  `y` through the velocities. The setting of `PhyslibAlpha.ClassicalMechanics.MomentMap.Basic`
  (a constant non-degenerate form on a vector space) therefore does not apply; the moment and the
  cocycle are computed explicitly.

## ii. Key results

- `GalileanAlgebra.bracket_jacobi`: the Jacobi identity for Souriau's bracket.
- `GalileanAlgebra.cocycle_cyclic`: (12.129), `f₀` satisfies the cyclic identity.
- `GalileanAlgebra.smul_cocycle_isCoboundary_iff`: `M f₀` is an algebra coboundary,
  `M f₀(Z)(Z') = μ₀[Z, Z']` for some torsor `μ₀`, if and only if `M = 0`.
- `EvolutionSpace.hasDerivAt_moment`: (12.124), the moment of the free points.
- `EvolutionSpace.moment_motion`: (12.121), the moment is constant along the free motions.
- `EvolutionSpace.lagrangeForm_vectorField`: (12.134) with `m = Σ_j m_j` (12.135).
- `EvolutionSpace.totalMass_cocycle_not_coboundary`: (12.136) at the level of the algebra, for a
  non-zero total mass the cocycle of the system is not a coboundary.
- `EvolutionSpace.moment_g`, `EvolutionSpace.centerOfMass_motion`: (12.141), `g = m R - p t`, and
  the uniform motion of the centre of gravity of free points.

## iii. Table of contents

- A. The Galilean Lie algebra
- B. Torsors
- C. The cocycle `f₀`
- D. The evolution space of free material points
- E. The moment
- F. The cocycle of the system and the mass

## iv. References

- J.-M. Souriau, Structure des systèmes dynamiques, Dunod, Paris, 1970: pp. 132-133
  (12.40)-(12.49), pp. 139-140 (12.72)-(12.76), p. 148 (12.114), pp. 150-153 (12.118)-(12.141);
  p. 27 (2.45), p. 50 (6.12 b) and p. 113 (11.22 a) for the bracket; p. 50 (6.13 b), p. 109
  (11.16), p. 114 (11.24) and p. 116, note (1), for the coboundaries of the algebra.

* J.-M. Souriau, *Structure des systèmes dynamiques*, Maîtrises de mathématiques, Dunod,
  Paris, 1970: chapter 12, pp. 132-153, and pp. 27, 50, 109, 113-116 for the conventions (2.45),
  (6.12), (6.13), (11.16), (11.22), (11.24). The equation numbers refer to this edition.
  [ref: Souriau1970]

-/

@[expose] public section

noncomputable section

namespace ClassicalMechanics

open Matrix

local notation "ℝ³" => Fin 3 → ℝ

/-!

## A. The Galilean Lie algebra

-/

/-- An element `Z = (ω, β, γ, ε)` of the Lie algebra of the Galilean group, in Souriau's
parametrisation (12.74), (12.118). -/
@[ext]
structure GalileanAlgebra where
  /-- The infinitesimal rotation, as an axial vector. -/
  ω : ℝ³
  /-- The change of velocity (infinitesimal boost). -/
  β : ℝ³
  /-- The space translation. -/
  γ : ℝ³
  /-- The time translation. -/
  ε : ℝ

namespace GalileanAlgebra

instance : Zero GalileanAlgebra := ⟨⟨0, 0, 0, 0⟩⟩

instance : Add GalileanAlgebra := ⟨fun Z Z' => ⟨Z.ω + Z'.ω, Z.β + Z'.β, Z.γ + Z'.γ, Z.ε + Z'.ε⟩⟩

/-- Souriau's bracket on the Galilean Lie algebra. It is the bracket of the vector fields (12.119)
in the convention (6.12 b), (2.45), see `EvolutionSpace.vectorField_bracket`. -/
def bracket (Z Z' : GalileanAlgebra) : GalileanAlgebra :=
  ⟨Z'.ω ⨯₃ Z.ω, Z'.ω ⨯₃ Z.β - Z.ω ⨯₃ Z'.β,
    Z'.ω ⨯₃ Z.γ - Z.ω ⨯₃ Z'.γ + Z.ε • Z'.β - Z'.ε • Z.β, 0⟩

/-- The bracket is antisymmetric. -/
lemma bracket_antisymm (Z Z' : GalileanAlgebra) : bracket Z Z' + bracket Z' Z = 0 := by
  apply GalileanAlgebra.ext
  · change Z'.ω ⨯₃ Z.ω + Z.ω ⨯₃ Z'.ω = 0
    simp
  · change (Z'.ω ⨯₃ Z.β - Z.ω ⨯₃ Z'.β) + (Z.ω ⨯₃ Z'.β - Z'.ω ⨯₃ Z.β) = 0
    abel
  · change (Z'.ω ⨯₃ Z.γ - Z.ω ⨯₃ Z'.γ + Z.ε • Z'.β - Z'.ε • Z.β) +
      (Z.ω ⨯₃ Z'.γ - Z'.ω ⨯₃ Z.γ + Z'.ε • Z.β - Z.ε • Z'.β) = 0
    abel
  · change (0 : ℝ) + 0 = 0
    simp

/-- The Jacobi identity for Souriau's bracket. -/
lemma bracket_jacobi (Z Z' Z'' : GalileanAlgebra) :
    bracket Z (bracket Z' Z'') + bracket Z' (bracket Z'' Z) + bracket Z'' (bracket Z Z') = 0 := by
  apply GalileanAlgebra.ext
  · change (bracket Z (bracket Z' Z'')).ω + (bracket Z' (bracket Z'' Z)).ω
      + (bracket Z'' (bracket Z Z')).ω = 0
    funext i
    fin_cases i <;> simp [bracket, cross_apply, vecHead, vecTail] <;> ring
  · change (bracket Z (bracket Z' Z'')).β + (bracket Z' (bracket Z'' Z)).β
      + (bracket Z'' (bracket Z Z')).β = 0
    funext i
    fin_cases i <;> simp [bracket, cross_apply, vecHead, vecTail] <;> ring
  · change (bracket Z (bracket Z' Z'')).γ + (bracket Z' (bracket Z'' Z)).γ
      + (bracket Z'' (bracket Z Z')).γ = 0
    funext i
    fin_cases i <;> simp [bracket, cross_apply, vecHead, vecTail] <;> ring
  · change (0 : ℝ) + 0 + 0 = 0
    simp

/-- A change of velocity and a space translation commute. -/
lemma bracket_boost_translation (β γ : ℝ³) : bracket ⟨0, β, 0, 0⟩ ⟨0, 0, γ, 0⟩ = 0 := by
  simp [bracket]
  rfl

end GalileanAlgebra

/-!

## B. Torsors

-/

/-- A torsor `μ = {l, g, p, E}`, an element of the dual of the Galilean Lie algebra (12.123). -/
@[ext]
structure GalileanTorsor where
  /-- The angular momentum part. -/
  l : ℝ³
  /-- The part paired with the changes of velocity. -/
  g : ℝ³
  /-- The momentum part. -/
  p : ℝ³
  /-- The energy part. -/
  E : ℝ

/-- The pairing (12.122) of a torsor with an element of the Lie algebra,
`μ(Z) = ⟨l, ω⟩ - ⟨g, β⟩ + ⟨p, γ⟩ - E ε`. -/
def GalileanTorsor.pair (μ : GalileanTorsor) (Z : GalileanAlgebra) : ℝ :=
  μ.l ⬝ᵥ Z.ω - μ.g ⬝ᵥ Z.β + μ.p ⬝ᵥ Z.γ - μ.E * Z.ε

/-!

## C. The cocycle `f₀`

-/

namespace GalileanAlgebra

/-- The 2-form `f₀(Z)(Z') = ⟨β, γ'⟩ - ⟨β', γ⟩` of (12.130). -/
def cocycle (Z Z' : GalileanAlgebra) : ℝ := Z.β ⬝ᵥ Z'.γ - Z'.β ⬝ᵥ Z.γ

/-- `f₀` is antisymmetric. -/
lemma cocycle_antisymm (Z Z' : GalileanAlgebra) : cocycle Z Z' = -cocycle Z' Z := by
  simp only [cocycle]
  ring

/-- (12.129): `f₀(Z)([Z', Z'']) + f₀(Z')([Z'', Z]) + f₀(Z'')([Z, Z']) = 0`. -/
lemma cocycle_cyclic (Z Z' Z'' : GalileanAlgebra) :
    cocycle Z (bracket Z' Z'') + cocycle Z' (bracket Z'' Z) + cocycle Z'' (bracket Z Z') = 0 := by
  rw [cocycle, cocycle, cocycle, add_assoc, bracket, bracket, bracket]
  simp only [cross_apply, vec3_dotProduct]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, sub_cons, head_cons, tail_cons,
    sub_self, zero_empty, cons_add, empty_add_empty, Pi.sub_apply, cons_val_zero, Pi.smul_apply,
    smul_eq_mul, cons_val_one, cons_val]
  ring_nf
  simp only [vecHead, vecTail]
  simp only [Fin.isValue, Pi.smul_apply, smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring_nf

/-- `f₀` is not zero: its value on a change of velocity and a space translation along the same
axis is `1`. -/
lemma cocycle_boost_translation :
    cocycle ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ = 1 := by
  rw [cocycle]
  simp

/-- `M f₀` is a coboundary of the algebra, `M f₀(Z)(Z') = μ₀[Z, Z']` for some torsor `μ₀` ((11.24)
with `Z_{g*}(μ) = μ ∘ Ad(Z)` (11.16) and `Ad(Z)(Z') = [Z, Z']` (6.13 b); by p. 116, note (1), this
is also the derivative of the group coboundary `Δ(μ₀)` of (11.19)), if and only if `M = 0`. -/
lemma smul_cocycle_isCoboundary_iff (M : ℝ) :
    (∃ μ₀ : GalileanTorsor, ∀ Z Z' : GalileanAlgebra, M * cocycle Z Z' = μ₀.pair (bracket Z Z'))
      ↔ M = 0 := by
  constructor
  · rintro ⟨μ₀, h⟩
    have h1 := h ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩
    rw [bracket_boost_translation ![1, 0, 0] ![1, 0, 0]] at h1
    change M * cocycle ⟨0, ![1, 0, 0], 0, 0⟩ ⟨0, 0, ![1, 0, 0], 0⟩ =
      μ₀.l ⬝ᵥ 0 - μ₀.g ⬝ᵥ 0 + μ₀.p ⬝ᵥ 0 - μ₀.E * 0 at h1
    simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero,
      add_zero] at h1
    rw [cocycle_boost_translation] at h1
    simpa using h1
  · intro hM
    refine ⟨⟨0, 0, 0, 0⟩, fun Z Z' => ?_⟩
    rw [hM, GalileanTorsor.pair]
    simp

/-- `f₀` is not a coboundary of the algebra: no torsor `μ₀` satisfies `f₀(Z)(Z') = μ₀[Z, Z']` for
all `Z`, `Z'`. -/
lemma cocycle_not_coboundary :
    ¬ ∃ μ₀ : GalileanTorsor, ∀ Z Z' : GalileanAlgebra, cocycle Z Z' = μ₀.pair (bracket Z Z') := by
  rintro ⟨μ₀, h⟩
  exact one_ne_zero <| (smul_cocycle_isCoboundary_iff 1).mp
    ⟨μ₀, fun Z Z' => by rw [one_mul]; exact h Z Z'⟩

end GalileanAlgebra

/-!

## D. The evolution space of free material points

-/

/-- A point, or a tangent vector, of the evolution space of `N` material points,
`y = (t, r_j, v_j)` (12.76). -/
@[ext]
structure EvolutionSpace (N : ℕ) where
  /-- The time. -/
  t : ℝ
  /-- The positions. -/
  r : Fin N → ℝ³
  /-- The velocities. -/
  v : Fin N → ℝ³

namespace EvolutionSpace

variable {N : ℕ}

instance : Sub (EvolutionSpace N) := ⟨fun y y' => ⟨y.t - y'.t, y.r - y'.r, y.v - y'.v⟩⟩

open GalileanAlgebra

/-- The vector field `Z_V` of `Z` on the evolution space (12.119): `δt = ε`,
`δr_j = ω × r_j + β t + γ`, `δv_j = ω × v_j + β`. -/
def vectorField (Z : GalileanAlgebra) (y : EvolutionSpace N) : EvolutionSpace N :=
  ⟨Z.ε, fun j => Z.ω ⨯₃ y.r j + y.t • Z.β + Z.γ, fun j => Z.ω ⨯₃ y.v j + Z.β⟩

/-- The differential of the affine vector field `Z_V` (its linear part), applied to a tangent vector
`w`. -/
def linearPart (Z : GalileanAlgebra) (w : EvolutionSpace N) : EvolutionSpace N :=
  ⟨0, fun j => Z.ω ⨯₃ w.r j + w.t • Z.β, fun j => Z.ω ⨯₃ w.v j⟩

/-- Souriau's bracket is the bracket of the vector fields in the convention (6.12 b), (2.45):
`[Z, Z']_V = DZ'_V(Z_V) - DZ_V(Z'_V)`. -/
lemma vectorField_bracket (Z Z' : GalileanAlgebra) (y : EvolutionSpace N) :
    vectorField (bracket Z Z') y
      = linearPart Z' (vectorField Z y) - linearPart Z (vectorField Z' y) := by
  apply EvolutionSpace.ext
  · change (0 : ℝ) = 0 - 0
    simp
  · funext j
    change (bracket Z Z').ω ⨯₃ y.r j + y.t • (bracket Z Z').β + (bracket Z Z').γ =
      (linearPart Z' (vectorField Z y)).r j - (linearPart Z (vectorField Z' y)).r j
    funext i
    fin_cases i <;> simp [bracket, linearPart, vectorField, cross_apply, vecHead, vecTail] <;> ring
  · funext j
    change (bracket Z Z').ω ⨯₃ y.v j + (bracket Z Z').β =
      (linearPart Z' (vectorField Z y)).v j - (linearPart Z (vectorField Z' y)).v j
    funext i
    fin_cases i <;> simp [bracket, linearPart, vectorField, cross_apply, vecHead, vecTail] <;> ring

/-- The Lagrange form of `N` free material points of masses `m j` at `y`, (12.40) with `F_j = 0`:
`σ(dy)(δy) = Σ_j ⟨m_j dv_j, δr_j - v_j δt⟩ - ⟨m_j δv_j, dr_j - v_j dt⟩`. -/
def lagrangeForm (m : Fin N → ℝ) (y dy δy : EvolutionSpace N) : ℝ :=
  ∑ j, (m j * (dy.v j ⬝ᵥ (δy.r j - δy.t • y.v j)) - m j * (δy.v j ⬝ᵥ (dy.r j - dy.t • y.v j)))

/-- `σ` is antisymmetric. -/
lemma lagrangeForm_antisymm (m : Fin N → ℝ) (y dy δy : EvolutionSpace N) :
    lagrangeForm m y dy δy = -lagrangeForm m y δy dy := by
  simp [lagrangeForm]

/-- (12.41)-(12.43): the velocity `(1, v_j, 0)` of the free motion through `y` lies in the kernel
of `σ` (one direction of (12.48)). -/
lemma lagrangeForm_motion (m : Fin N → ℝ) (y δy : EvolutionSpace N) :
    lagrangeForm m y ⟨1, y.v, 0⟩ δy = 0 := by
  simp [lagrangeForm]

/-!

## E. The moment

-/

/-- The moment of `N` free material points ((12.125) for one point of unit mass; (12.135) for `N`
points, with `E_j = 0` in its last line and the additive constant of `E` chosen to be `0`):
`l = Σ m_j r_j × v_j`, `g = Σ m_j (r_j - v_j t)`, `p = Σ m_j v_j`, `E = ½ Σ m_j ‖v_j‖²`. -/
def moment (m : Fin N → ℝ) (y : EvolutionSpace N) : GalileanTorsor :=
  ⟨∑ j, m j • (y.r j ⨯₃ y.v j), ∑ j, m j • (y.r j - y.t • y.v j), ∑ j, m j • y.v j,
    (1 / 2 : ℝ) * ∑ j, m j * (y.v j ⬝ᵥ y.v j)⟩

/-- The line `s ↦ y + s dy` of the evolution space. -/
def line (y dy : EvolutionSpace N) (s : ℝ) : EvolutionSpace N :=
  ⟨y.t + s * dy.t, fun j => y.r j + s • dy.r j, fun j => y.v j + s • dy.v j⟩

/-- The free motion through `y`: `t + s`, `r_j + s v_j`, `v_j`. -/
def motion (y : EvolutionSpace N) (s : ℝ) : EvolutionSpace N :=
  ⟨y.t + s, fun j => y.r j + s • y.v j, y.v⟩

/-- `μ(Z)` as a sum over the material points. -/
lemma pair_moment (m : Fin N → ℝ) (y : EvolutionSpace N) (Z : GalileanAlgebra) :
    (moment m y).pair Z = ∑ j, m j * ((y.r j ⨯₃ y.v j) ⬝ᵥ Z.ω - (y.r j - y.t • y.v j) ⬝ᵥ Z.β
      + y.v j ⬝ᵥ Z.γ - (1 / 2 : ℝ) * Z.ε * (y.v j ⬝ᵥ y.v j)) := by
  simp only [GalileanTorsor.pair, moment, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The `j`th term of `μ(Z)` along `y + s dy`, as a polynomial of degree two in `s`. -/
private lemma pair_term_line (m t dt s : ℝ) (r v dr dv : ℝ³) (Z : GalileanAlgebra) :
    m * (((r + s • dr) ⨯₃ (v + s • dv)) ⬝ᵥ Z.ω - ((r + s • dr) - (t + s * dt) • (v + s • dv)) ⬝ᵥ Z.β
        + (v + s • dv) ⬝ᵥ Z.γ - (1 / 2 : ℝ) * Z.ε * ((v + s • dv) ⬝ᵥ (v + s • dv)))
    = m * ((r ⨯₃ v) ⬝ᵥ Z.ω - (r - t • v) ⬝ᵥ Z.β + v ⬝ᵥ Z.γ - (1 / 2 : ℝ) * Z.ε * (v ⬝ᵥ v))
      + s * (m * (dv ⬝ᵥ ((Z.ω ⨯₃ r + t • Z.β + Z.γ) - Z.ε • v))
             - m * ((Z.ω ⨯₃ v + Z.β) ⬝ᵥ (dr - dt • v)))
      + s ^ 2 * (m * ((dr ⨯₃ dv) ⬝ᵥ Z.ω + dt * (dv ⬝ᵥ Z.β) - (1 / 2 : ℝ) * Z.ε * (dv ⬝ᵥ dv))) := by
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The derivative at `0` of a polynomial of degree two. -/
private lemma hasDerivAt_quadratic (a b c : ℝ) :
    HasDerivAt (fun s : ℝ => a + s * b + s ^ 2 * c) b 0 := by
  have h := (((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add a).fun_add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c)
  simpa using h

/-- (12.124): `σ(dy)(Z_V(y)) = dμ(Z)(dy)`, stated as the derivative at `s = 0` of
`s ↦ μ(y + s dy)(Z)`; `μ` is a moment of the action (12.120). -/
lemma hasDerivAt_moment (m : Fin N → ℝ) (y dy : EvolutionSpace N) (Z : GalileanAlgebra) :
    HasDerivAt (fun s => (moment m (line y dy s)).pair Z) (lagrangeForm m y dy (vectorField Z y))
      0 := by
  have hfun : (fun s => (moment m (line y dy s)).pair Z) = fun s => ∑ j,
      (m j * ((y.r j ⨯₃ y.v j) ⬝ᵥ Z.ω - (y.r j - y.t • y.v j) ⬝ᵥ Z.β + y.v j ⬝ᵥ Z.γ
          - (1 / 2 : ℝ) * Z.ε * (y.v j ⬝ᵥ y.v j))
        + s * (m j * (dy.v j ⬝ᵥ ((Z.ω ⨯₃ y.r j + y.t • Z.β + Z.γ) - Z.ε • y.v j))
               - m j * ((Z.ω ⨯₃ y.v j + Z.β) ⬝ᵥ (dy.r j - dy.t • y.v j)))
        + s ^ 2 * (m j * ((dy.r j ⨯₃ dy.v j) ⬝ᵥ Z.ω + dy.t * (dy.v j ⬝ᵥ Z.β)
          - (1 / 2 : ℝ) * Z.ε * (dy.v j ⬝ᵥ dy.v j)))) := by
    funext s
    rw [pair_moment]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact pair_term_line (m j) y.t dy.t s (y.r j) (y.v j) (dy.r j) (dy.v j) Z
  rw [hfun]
  have hL : lagrangeForm m y dy (vectorField Z y) = ∑ j,
      (m j * (dy.v j ⬝ᵥ ((Z.ω ⨯₃ y.r j + y.t • Z.β + Z.γ) - Z.ε • y.v j))
        - m j * ((Z.ω ⨯₃ y.v j + Z.β) ⬝ᵥ (dy.r j - dy.t • y.v j))) := rfl
  rw [hL]
  exact HasDerivAt.fun_sum (fun j _ => hasDerivAt_quadratic _ _ _)

/-- (12.121): the moment is constant along every free motion. -/
lemma moment_motion (m : Fin N → ℝ) (y : EvolutionSpace N) (s : ℝ) :
    moment m (motion y s) = moment m y := by
  simp [moment, motion]
  congr
  ext j
  simp [add_smul]

/-!

## F. The cocycle of the system and the mass

-/

/-- The total mass `m = Σ_j m_j` (12.135). -/
def totalMass (m : Fin N → ℝ) : ℝ := ∑ j, m j

/-- The centre of gravity `R = (Σ_j m_j r_j) / m`, named in (12.141) (the formula is the usual one,
not printed there); for `m = 0` the value is `0`, by the convention `0⁻¹ = 0`. -/
def centerOfMass (m : Fin N → ℝ) (y : EvolutionSpace N) : ℝ³ :=
  (totalMass m)⁻¹ • ∑ j, m j • y.r j

/-- (12.134) with `m = Σ_j m_j` (12.135): `σ(Z_V(y))(Z'_V(y)) = μ[Z, Z'] + m f₀(Z)(Z')`. -/
lemma lagrangeForm_vectorField (m : Fin N → ℝ) (y : EvolutionSpace N) (Z Z' : GalileanAlgebra) :
    lagrangeForm m y (vectorField Z y) (vectorField Z' y)
      = (moment m y).pair (bracket Z Z') + totalMass m * cocycle Z Z' := by
  simp [lagrangeForm, GalileanTorsor.pair, moment, cocycle, totalMass, bracket, vectorField,
    sum_dotProduct, smul_dotProduct, vec3_dotProduct, cross_apply, vecHead, vecTail,
    Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- (12.136) at the level of the algebra: for a non-zero total mass, the cocycle `m f₀` of the
system is not a coboundary of the algebra. -/
lemma totalMass_cocycle_not_coboundary (m : Fin N → ℝ) (hM : totalMass m ≠ 0) :
    ¬ ∃ μ₀ : GalileanTorsor, ∀ Z Z' : GalileanAlgebra,
      totalMass m * cocycle Z Z' = μ₀.pair (bracket Z Z') :=
  fun h => hM ((smul_cocycle_isCoboundary_iff (totalMass m)).mp h)

/-- (12.141): `g = m R - p t`, with `R` the centre of gravity, for a non-zero total mass. -/
lemma moment_g (m : Fin N → ℝ) (hM : totalMass m ≠ 0) (y : EvolutionSpace N) :
    (moment m y).g = totalMass m • centerOfMass m y - y.t • (moment m y).p := by
  simp [moment, smul_sub]
  simp only [centerOfMass, Finset.smul_sum]
  congr 1
  all_goals simp [← mul_smul, mul_comm]
  congr! with i
  field_simp [hM]

/-- Along a free motion the centre of gravity moves uniformly with velocity `p / m` (p. 153, after
(12.141)). Souriau deduces this for any isolated system from the constancy of `g` and `p`; here it
is proved directly from the free motion. For `m = 0` both sides are `0`. -/
lemma centerOfMass_motion (m : Fin N → ℝ) (y : EvolutionSpace N) (s : ℝ) :
    centerOfMass m (motion y s) = centerOfMass m y + s • ((totalMass m)⁻¹ • (moment m y).p) := by
  simp [centerOfMass, motion, smul_smul]
  simp [moment, mul_smul, Finset.smul_sum, Finset.sum_add_distrib, smul_add]
  congr
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm s]

end EvolutionSpace

end ClassicalMechanics
