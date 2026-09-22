/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Quadratic.Triple
public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Power.Quadratic

/-!

# The fundamental formula for quadratic Jordan representations

The target of this module is the purely algebraic identity

`U (U a b) = U a * U b * U a`.

It is the central composition law for quadratic representations.  This module is kept separate
from the elementary definition of `U` and from ordered/JB positivity, because its proof uses the
Jordan identity but no order or norm.

-/

@[expose] public section

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E] [SMulCommClass ℝ E E]
  [IsCommJordan E]

open scoped JordanAlgebra

/-! ## Fundamental composition identity -/

omit [SMulCommClass ℝ E E] in
/-- The fully polarised Jordan identity, evaluated at a third element.  Mathlib states this as
an equality of additive endomorphisms annihilated by `2`; over a real Jordan algebra the scalar
action is torsion-free, so the actual cyclic commutator vanishes.  Keeping this pointwise form is
useful when expanding identities for `U`, while avoiding a second, parallel multiplication
operator API. -/
theorem cyclic_mulLeft_commutator (a b c x : E) :
    (a * ((b * c) * x) - (b * c) * (a * x)) +
        (b * ((c * a) * x) - (c * a) * (b * x)) +
          (c * ((a * b) * x) - (a * b) * (c * x)) = 0 := by
  have h := two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c
  have hx := DFunLike.congr_fun h x
  have hx' : (2 : ℕ) •
      ((a * ((b * c) * x) - (b * c) * (a * x)) +
        (b * ((c * a) * x) - (c * a) * (b * x)) +
          (c * ((a * b) * x) - (a * b) * (c * x))) = 0 := by
    exact hx
  have htwo : (2 : ℝ) •
      ((a * ((b * c) * x) - (b * c) * (a * x)) +
        (b * ((c * a) * x) - (c * a) * (b * x)) +
          (c * ((a * b) * x) - (a * b) * (c * x))) = 0 := by
    simpa [two_smul] using hx'
  calc
    _ = (1 / 2 : ℝ) • ((2 : ℝ) •
        ((a * ((b * c) * x) - (b * c) * (a * x)) +
          (b * ((c * a) * x) - (c * a) * (b * x)) +
            (c * ((a * b) * x) - (a * b) * (c * x)))) := by module
    _ = 0 := by rw [htwo]; module

omit [SMulCommClass ℝ E E] in
/-- The cyclic commutator identity, with its three commutators collected.  This is the fully
polarized degree-four Jordan relation in the form used by the operator normalization argument. -/
theorem cyclic_mulLeft_assoc_sum (a b c x : E) :
    a * ((b * c) * x) + b * ((c * a) * x) + c * ((a * b) * x) =
      (b * c) * (a * x) + (c * a) * (b * x) + (a * b) * (c * x) := by
  have h := cyclic_mulLeft_commutator a b c x
  apply sub_eq_zero.mp
  calc
    _ = (a * ((b * c) * x) - (b * c) * (a * x)) +
          (b * ((c * a) * x) - (c * a) * (b * x)) +
            (c * ((a * b) * x) - (a * b) * (c * x)) := by abel
    _ = 0 := h

/-- The multiplication operator of a triple product can be normalized to a polynomial in
multiplication operators of single and double products.  This is equation (2.2) in the
self-contained algebraic proof of the quadratic fundamental formula: it is obtained by applying
the cyclic relation, then exploiting the symmetry of its right-hand side under interchange of
the first and evaluation variables. -/
theorem mulLeft_triple_normalize (a b c : E) :
    L (a * (b * c)) =
      ((L a).comp (L (b * c)) + (L b).comp (L (a * c)) + (L c).comp (L (a * b))) -
        (((L b).comp (L a)).comp (L c) + ((L c).comp (L a)).comp (L b)) := by
  ext x
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, mulLeft_apply]
  have habc := cyclic_mulLeft_assoc_sum a b c x
  have hxbc := cyclic_mulLeft_assoc_sum x b c a
  have hright :
      (b * c) * (a * x) + (c * a) * (b * x) + (a * b) * (c * x) =
        (b * c) * (x * a) + (c * x) * (b * a) + (x * b) * (c * a) := by
    rw [mul_comm x a, mul_comm b a, mul_comm x b]
    rw [mul_comm (c * a) (b * x), mul_comm (a * b) (c * x)]
    abel
  have hswap :
      a * ((b * c) * x) + b * ((c * a) * x) + c * ((a * b) * x) =
        x * ((b * c) * a) + b * ((c * x) * a) + c * ((x * b) * a) := by
    calc
      _ = (b * c) * (a * x) + (c * a) * (b * x) + (a * b) * (c * x) := habc
      _ = (b * c) * (x * a) + (c * x) * (b * a) + (x * b) * (c * a) := hright
      _ = _ := hxbc.symm
  rw [mul_comm (a * (b * c)) x, mul_comm a (b * c), mul_comm a c,
    mul_comm a (c * x), mul_comm a (b * x), mul_comm b x]
  calc
    x * (b * c * a) =
        (x * (b * c * a) + b * (c * x * a) + c * (x * b * a)) -
          (b * (c * x * a) + c * (x * b * a)) := by abel
    _ = _ := by rw [← hswap]

/-- First specialization of `mulLeft_triple_normalize`: the multiplication operator of the third
Jordan power is a polynomial in `L_a` and `L_(a²)`. -/
theorem mulLeft_cube_normalize (a : E) :
    L (a * (a * a)) =
      (3 : ℝ) • ((L a).comp (L (a * a))) -
        (2 : ℝ) • (((L a).comp (L a)).comp (L a)) := by
  rw [mulLeft_triple_normalize]
  module

/-- Second normalization step, evaluated at `x`: multiplication by `(a²)²` is reduced to the
commuting operators `L_a` and `L_(a²)`. -/
theorem mul_self_mul_self_mulLeft_normalize (a x : E) :
    ((a * a) * (a * a)) * x =
      (a * a) * ((a * a) * x) +
        (4 : ℝ) • (a * (a * ((a * a) * x))) -
          (4 : ℝ) • (a * (a * (a * (a * x)))) := by
  have hpow : (a * a) * (a * a) = a * (a * (a * a)) := by
    calc
      (a * a) * (a * a) = a ^[2] * a ^[2] := by rw [jpow_two]
      _ = a ^[4] := pow_add a 2 2
      _ = a * a ^[3] := (jpow_succ a 3).symm
      _ = a * (a * (a * a)) := by rw [jpow_succ a 2, jpow_two]
  have hnorm := DFunLike.congr_fun (mulLeft_triple_normalize a a (a * a)) x
  rw [← hpow] at hnorm
  rw [mulLeft_cube_normalize] at hnorm
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, mulLeft_apply, mul_smul_comm, mul_sub] at hnorm
  have hcomm (y : E) : a * ((a * a) * y) = (a * a) * (a * y) :=
    by simpa only [jpow_two] using commute_mulLeft_apply (commute_mulLeft_sq a) y
  have hYX2 : (a * a) * (a * (a * x)) = a * (a * ((a * a) * x)) := by
    calc
      (a * a) * (a * (a * x)) = a * ((a * a) * (a * x)) := (hcomm (a * x)).symm
      _ = a * (a * ((a * a) * x)) := by rw [hcomm x]
  rw [hYX2] at hnorm
  calc
    _ = (3 : ℝ) • (a * (a * ((a * a) * x))) - (2 : ℝ) • (a * (a * (a * (a * x)))) +
          ((3 : ℝ) • (a * (a * ((a * a) * x))) - (2 : ℝ) • (a * (a * (a * (a * x))))) +
            (a * a) * ((a * a) * x) -
              (a * (a * ((a * a) * x)) + a * (a * ((a * a) * x))) := hnorm
    _ = _ := by module

/-- The quadratic representation of a Jordan square is the square of its quadratic
representation. This is the first nontrivial quadratic fundamental identity; its proof uses only
the finite operator normalization certificate and the Jordan commutation law. -/
theorem quadRep_mul_self_eq_comp (a : E) :
    U (a * a) = (U a).comp (U a) := by
  ext x
  simp only [LinearMap.comp_apply]
  rw [quadRep_apply, quadRep_apply, quadRep_apply]
  simp only [jpow_two, mul_smul_comm, mul_sub]
  rw [mul_self_mul_self_mulLeft_normalize]
  have hcomm (y : E) : a * ((a * a) * y) = (a * a) * (a * y) :=
    by simpa only [jpow_two] using commute_mulLeft_apply (commute_mulLeft_sq a) y
  have hYX2 : (a * a) * (a * (a * x)) = a * (a * ((a * a) * x)) := by
    calc
      (a * a) * (a * (a * x)) = a * ((a * a) * (a * x)) := (hcomm (a * x)).symm
      _ = a * (a * ((a * a) * x)) := by rw [hcomm x]
  rw [hYX2]
  module

/-- The square identity evaluated on a sum.  This keeps the polarizing source equation in a
canonical bilinear form: the remaining coefficient extraction is purely a finite calculation in
the noncommutative ring of linear endomorphisms. -/
theorem quadRep_add_mul_self_eq_comp (a b : E) :
    U ((a + b) * (a + b)) =
      (U a + (2 : ℝ) • quadRepBilin a b + U b).comp
        (U a + (2 : ℝ) • quadRepBilin a b + U b) := by
  rw [quadRep_mul_self_eq_comp, quadRep_add_eq]

set_option maxHeartbeats 500000 in
/-- The positive polarization of the square identity, fully expanded in the canonical bilinear
quadratic operator.  Pairing this equation with its signed counterpart isolates the standard
mixed quadratic coefficient. -/
theorem quadRep_add_square_polarized (a b : E) :
    (U a).comp (U a) + (4 : ℝ) • U (a * b) + (U b).comp (U b) +
          (4 : ℝ) • quadRepBilin (a * a) (a * b) +
            (2 : ℝ) • quadRepBilin (a * a) (b * b) +
              (4 : ℝ) • quadRepBilin (a * b) (b * b) =
      (U a).comp (U a) + (4 : ℝ) • (quadRepBilin a b).comp (quadRepBilin a b) +
          (U b).comp (U b) + (U a).comp (U b) + (U b).comp (U a) +
            (2 : ℝ) • ((U a).comp (quadRepBilin a b) +
              (quadRepBilin a b).comp (U a) + (U b).comp (quadRepBilin a b) +
                (quadRepBilin a b).comp (U b)) := by
  have h := quadRep_add_mul_self_eq_comp a b
  rw [add_mul_self, quadRep_add_add_eq, quadRep_mul_self_eq_comp,
    quadRep_smul_eq, quadRep_mul_self_eq_comp, quadRepBilin_smul_right,
    quadRepBilin_smul_left] at h
  simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp,
    LinearMap.comp_smul] at h
  norm_num at h
  convert h using 1 <;> module

/-- The signed companion to `quadRep_add_square_polarized`.  Adding the two equations cancels
the cubic terms and leaves precisely the mixed quadratic coefficient. -/
theorem quadRep_sub_square_polarized (a b : E) :
    (U a).comp (U a) + (4 : ℝ) • U (a * b) + (U b).comp (U b) -
          (4 : ℝ) • quadRepBilin (a * a) (a * b) +
            (2 : ℝ) • quadRepBilin (a * a) (b * b) -
              (4 : ℝ) • quadRepBilin (a * b) (b * b) =
      (U a).comp (U a) + (4 : ℝ) • (quadRepBilin a b).comp (quadRepBilin a b) +
          (U b).comp (U b) + (U a).comp (U b) + (U b).comp (U a) -
            (2 : ℝ) • ((U a).comp (quadRepBilin a b) +
              (quadRepBilin a b).comp (U a) + (U b).comp (quadRepBilin a b) +
                (quadRepBilin a b).comp (U b)) := by
  have h := quadRep_add_square_polarized a (-b)
  simp only [mul_neg, neg_mul, quadRep_neg, quadRepBilin_neg_right,
    quadRepBilin_neg_left, LinearMap.neg_comp, LinearMap.comp_neg, neg_neg, smul_neg] at h
  convert h using 1 <;> module

/-- The standard mixed quadratic polarization identity.  This is the exact coefficient obtained
by adding the positive and signed square identities: all cubic terms cancel, leaving a relation
between the square of the bilinear quadratic operator, `U_(a*b)`, and the square cross-effect.
It is the finite algebraic entry point for the unrestricted quadratic fundamental formula. -/
theorem quadRepBilin_comp_self_polarization (a b : E) :
    (4 : ℝ) • (quadRepBilin a b).comp (quadRepBilin a b) =
      (4 : ℝ) • U (a * b) + (2 : ℝ) • quadRepBilin (a * a) (b * b) -
        (U a).comp (U b) - (U b).comp (U a) := by
  let S := (U a).comp (quadRepBilin a b) + (quadRepBilin a b).comp (U a) +
    (U b).comp (quadRepBilin a b) + (quadRepBilin a b).comp (U b)
  calc
    _ = (1 / 2 : ℝ) •
          ((U a).comp (U a) + (4 : ℝ) • (quadRepBilin a b).comp (quadRepBilin a b) +
              (U b).comp (U b) + (U a).comp (U b) + (U b).comp (U a) + (2 : ℝ) • S +
            ((U a).comp (U a) + (4 : ℝ) • (quadRepBilin a b).comp (quadRepBilin a b) +
              (U b).comp (U b) + (U a).comp (U b) + (U b).comp (U a) - (2 : ℝ) • S)) -
          (U a).comp (U a) - (U b).comp (U b) - (U a).comp (U b) - (U b).comp (U a) := by
      dsimp [S]
      module
    _ = (1 / 2 : ℝ) •
          ((U a).comp (U a) + (4 : ℝ) • U (a * b) + (U b).comp (U b) +
              (4 : ℝ) • quadRepBilin (a * a) (a * b) +
                (2 : ℝ) • quadRepBilin (a * a) (b * b) +
                  (4 : ℝ) • quadRepBilin (a * b) (b * b) +
            ((U a).comp (U a) + (4 : ℝ) • U (a * b) + (U b).comp (U b) -
              (4 : ℝ) • quadRepBilin (a * a) (a * b) +
                (2 : ℝ) • quadRepBilin (a * a) (b * b) -
                  (4 : ℝ) • quadRepBilin (a * b) (b * b))) -
          (U a).comp (U a) - (U b).comp (U b) - (U a).comp (U b) - (U b).comp (U a) := by
      dsimp [S]
      rw [← quadRep_add_square_polarized a b, ← quadRep_sub_square_polarized a b]
    _ = _ := by module

/-! ## Polarizing the cubic commutation law: the triple commutator identity -/

omit [IsCommJordan E] in
/-- Pointwise expansion of `U (a + b)` at an arbitrary argument, the elementary consequence of
`quadRep_add_eq` used repeatedly below to unfold both sides of the polarized cubic law. -/
theorem quadRep_add_apply' (a b y : E) :
    U (a + b) y = U a y + (2 : ℝ) • quadRepBilin a b y + U b y := by
  rw [quadRep_add_eq]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]

omit [IsCommJordan E] in
/-- Pointwise expansion of `U (a - b)` at an arbitrary argument. -/
theorem quadRep_sub_apply' (a b y : E) :
    U (a - b) y = U a y - (2 : ℝ) • quadRepBilin a b y + U b y := by
  rw [quadRep_sub_eq]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]

/-- The `(2,1)`-bidegree polarization of the cubic commutation law `quadRep_mulLeft`.  This is the
standard triple commutator identity obtained by substituting `a + b` and `a - b` into
`quadRep_mulLeft` and isolating the pure mixed-bidegree term via the two resulting equations, the
same finite-certificate technique used for the quadratic case in
`quadRepBilin_comp_self_polarization`.  It is the next concrete step in the multivariable
polarization program (Stage A item 1 of `JB_ROADMAP.md`): a genuine three-generator trilinear
relation between `U_a`, the bilinear cross-effect `quadRepBilin a b`, and plain multiplication. -/
theorem quadRepBilin_mulLeft_polarization (a b x : E) :
    U a (b * x) + (2 : ℝ) • quadRepBilin a b (a * x) =
      b * U a x + (2 : ℝ) • (a * quadRepBilin a b x) := by
  have hplus := quadRep_mulLeft (a + b) x
  have hminus := quadRep_mulLeft (a - b) x
  simp only [add_mul, sub_mul, quadRep_add_apply', quadRep_sub_apply', map_add, map_sub,
    mul_add, mul_sub, mul_smul_comm] at hplus hminus
  have ha := quadRep_mulLeft a x
  have hb := quadRep_mulLeft b x
  rw [ha, hb] at hplus hminus
  linear_combination (norm := module) (1 / 2 : ℝ) • hplus - (1 / 2 : ℝ) • hminus

/-- The symmetric companion of `quadRepBilin_mulLeft_polarization`, obtained by exchanging the
roles of `a` and `b` (using symmetry of `quadRepBilin`).  Together the pair is the full standard
triple commutator identity: it records the same trilinear relation for both mixed bidegree
components `(2,1)` and `(1,2)` that appear when the cubic law `quadRep_mulLeft` is evaluated at
`a + b`. -/
theorem quadRepBilin_mulLeft_polarization' (a b x : E) :
    U b (a * x) + (2 : ℝ) • quadRepBilin a b (b * x) =
      a * U b x + (2 : ℝ) • (b * quadRepBilin a b x) := by
  have h := quadRepBilin_mulLeft_polarization b a x
  rwa [quadRepBilin_comm] at h

/-! ## Normalizing the multiplication operator of a quadratic image -/

/-- The multiplication operator of the compound element `U a b` normalizes to a polynomial in
`L_a`, `L_b`, `L_(a*a)`, and `L_(a*b)`, with no remaining atom of the same bidegree as `U a b`
itself.  This is the concrete outcome of pushing `mulLeft_triple_normalize` further (Stage A item
1 of `JB_ROADMAP.md`, the second candidate route): apply it once to `a * (a * b)` and once to
`b * (a * a)` (using commutativity to identify `(a * a) * b` with `b * (a * a)`), then take the
exact integer combination `2 • (first) - (second)` matching `quadRep_apply`'s expansion of
`U a b = 2 • (a * (a * b)) - jpow a 2 * b`.  Unlike the compound element `U a b` itself, this
operator formula uses only single- and double-product multiplication operators, so it is a genuine
new normalization certificate, not a restatement of anything already on hand. -/
theorem mulLeft_quadRep_normalize (a b : E) :
    L (U a b) =
      (2 : ℝ) • ((L a).comp (L (a * b))) + (L b).comp (L (a * a)) -
        (2 : ℝ) • (((L a).comp (L a)).comp (L b)) -
          (2 : ℝ) • (((L b).comp (L a)).comp (L a)) +
            (2 : ℝ) • (((L a).comp (L b)).comp (L a)) := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, mulLeft_apply]
  rw [quadRep_apply]
  have hsmul_mul (y : E) : (2 : ℝ) • (a * (a * b)) * y = (2 : ℝ) • ((a * (a * b)) * y) := by
    calc
      (2 : ℝ) • (a * (a * b)) * y = y * ((2 : ℝ) • (a * (a * b))) := mul_comm _ _
      _ = (2 : ℝ) • (y * (a * (a * b))) := mul_smul_comm _ _ _
      _ = (2 : ℝ) • ((a * (a * b)) * y) := by rw [mul_comm y (a * (a * b))]
  rw [sub_mul, hsmul_mul, jpow_two]
  have h1 := DFunLike.congr_fun (mulLeft_triple_normalize a a b) x
  have h2 := DFunLike.congr_fun (mulLeft_triple_normalize b a a) x
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    mulLeft_apply] at h1 h2
  rw [mul_comm (a * a) b]
  rw [mul_comm b a] at h2
  linear_combination (norm := module) (2 : ℝ) • h1 - h2

omit [IsCommJordan E] in
/-- The quadratic representation of the compound element `U a b` reduces, by bare bilinearity of
`quadRepBilin` (no Jordan identity needed for this step), to the quadratic representations of the
two elementary constituents of `quadRep_apply`'s expansion
`U a b = 2 • (a * (a * b)) - jpow a 2 * b` and their cross-effect.  This is the precise sense in
which pushing the operator-normalization route (`mulLeft_quadRep_normalize`) a second level does
*not* terminate the fundamental-formula computation: `a * (a * b)` and `jpow a 2 * b` are
themselves elements of the same bidegree `(2,1)` in `(a, b)` as `U a b`, so `U (a * (a * b))` and
`U (jpow a 2 * b)` are exactly as hard as the original
target `U (U a b)` — this identity trades one degree-`(4,2)` problem for three of the same
difficulty, not for something simpler — this lemma documents precisely why that route does not
close by itself beyond its first level. (`quadRep_fundamental` below is in fact proved by a
different route entirely: the inner-derivation/triple-operator toolkit, `tripleOperator_comm`.) -/
theorem quadRep_quadRep_eq (a b : E) :
    U (U a b) =
      (4 : ℝ) • U (a * (a * b)) - (4 : ℝ) • quadRepBilin (a * (a * b)) (jpow a 2 * b) +
        U (jpow a 2 * b) := by
  rw [← quadRepBilin_self (U a b), quadRep_apply]
  set p := a * (a * b)
  set q := jpow a 2 * b
  have hXX : quadRepBilin ((2 : ℝ) • p - q) ((2 : ℝ) • p - q) =
      quadRepBilin ((2 : ℝ) • p) ((2 : ℝ) • p) - quadRepBilin ((2 : ℝ) • p) q -
        (quadRepBilin q ((2 : ℝ) • p) - quadRepBilin q q) := by
    rw [quadRepBilin_sub_right, quadRepBilin_comm ((2 : ℝ) • p - q) ((2 : ℝ) • p),
      quadRepBilin_comm ((2 : ℝ) • p - q) q, quadRepBilin_sub_right, quadRepBilin_sub_right]
  rw [hXX]
  simp only [quadRepBilin_smul_left, quadRepBilin_smul_right, quadRepBilin_self,
    quadRepBilin_comm q p, quadRep_smul_eq]
  norm_num
  module

/-! ## The inner derivation and the Jordan-triple-system fundamental identity

This section formalizes the standard Jordan-triple-system operator toolkit
(`D_{a,b} := [L_a, L_b]`, `V_{a,b} := L_{a*b} + D_{a,b}`) and uses it to prove the linearized
triple-product fundamental identity that direct polarization of `cyclic_mulLeft_commutator` cannot
reach on its own (see `JB_ROADMAP.md` §7): a rank computation shows every *linear* substitution
combination of `cyclic_mulLeft_commutator` spans too small a space; the missing ingredient is the
*nonlinear* operator fact that `innerDerivation a b` is a genuine derivation of the Jordan
product, from which the whole triple identity follows by mechanical (associative) operator
algebra. -/

omit [IsCommJordan E] in
/-- Additivity of the inner derivation in its first defining argument. -/
theorem innerDerivation_add_left (a b c : E) :
    innerDerivation (a + b) c = innerDerivation a c + innerDerivation b c := by
  ext x
  simp only [innerDerivation_apply, LinearMap.add_apply]
  simp only [add_mul, mul_add]
  module

omit [IsCommJordan E] in
/-- Real linearity of the inner derivation in its first defining argument. -/
theorem innerDerivation_smul_left (r : ℝ) (a b : E) :
    innerDerivation (r • a) b = r • innerDerivation a b := by
  ext x
  simp only [innerDerivation_apply, LinearMap.smul_apply]
  have hsmul_mul (z y : E) : (r • z) * y = r • (z * y) := by
    calc
      (r • z) * y = y * (r • z) := mul_comm _ _
      _ = r • (y * z) := mul_smul_comm r y z
      _ = r • (z * y) := by rw [mul_comm y z]
  rw [hsmul_mul a (b * x), hsmul_mul a x, mul_smul_comm]
  simp only [smul_sub]

omit [IsCommJordan E] in
/-- Additivity of the inner derivation in its second defining argument. -/
theorem innerDerivation_add_right (a b c : E) :
    innerDerivation a (b + c) = innerDerivation a b + innerDerivation a c := by
  rw [innerDerivation_swap, innerDerivation_add_left, innerDerivation_swap a b,
    innerDerivation_swap a c]
  ext x
  simp only [LinearMap.neg_apply, LinearMap.add_apply]
  abel

omit [IsCommJordan E] in
/-- Real linearity of the inner derivation in its second defining argument. -/
theorem innerDerivation_smul_right (r : ℝ) (a b : E) :
    innerDerivation a (r • b) = r • innerDerivation a b := by
  rw [innerDerivation_swap, innerDerivation_smul_left, innerDerivation_swap a b, smul_neg]

omit [IsCommJordan E] in
/-- Difference expansion of the inner derivation in its first defining argument. -/
theorem innerDerivation_sub_left (a b c : E) :
    innerDerivation (a - b) c = innerDerivation a c - innerDerivation b c := by
  ext x
  simp only [innerDerivation_apply, LinearMap.sub_apply]
  simp only [sub_mul, mul_sub]
  module


omit [Module ℝ E] [SMulCommClass ℝ E E] [IsCommJordan E] in
/-- The diagonal fact for the triple product at `(a, a, x)`: telescoping cancellation collapses
it to the plain associative square multiplication `a² x`.  This is the base case used in the
final specialization of the fundamental identity. -/
theorem jordanTriple_diag_left (a x : E) : jordanTriple a a x = a ^[2] * x := by
  rw [jordanTriple, jpow_two]
  rw [mul_comm a (a * x), mul_comm x (a * a)]
  abel

/-- **The key nonlinear fact.**  The inner derivation `D_{a,b}` is a genuine derivation of the
Jordan product.  Unlike every identity in this file so far, this is *not* reachable by linear
(`a ± b`-style) substitution into `cyclic_mulLeft_commutator`: it is exactly the two atomic
substitution instances `cyclic_mulLeft_commutator a x y b` and `cyclic_mulLeft_commutator b x y a`,
combined and then normalized by commutativity — the same base relation used everywhere else in
this file, but composed at two independent points rather than linearly polarized at one. This was
verified offline before being formalized: representing the free commutative (non-associative)
algebra on four generators and checking that the derivation defect
`D_{a,b}(xy) - (D_{a,b}x)y - x(D_{a,b}y)` equals exactly
`cyclic(a,x,y,b) - cyclic(b,x,y,a)` (both sides expanded to raw monomials), confirmed the two
atomic instances suffice with unit coefficients. -/
theorem innerDerivation_mul (a b x y : E) :
    innerDerivation a b (x * y) = (innerDerivation a b x) * y + x * (innerDerivation a b y) := by
  have h1 := cyclic_mulLeft_commutator a x y b
  have h2 := cyclic_mulLeft_commutator b x y a
  simp only [innerDerivation_apply, sub_mul, mul_sub]
  simp only [mul_comm] at h1 h2 ⊢
  linear_combination (norm := module) h1 - h2

/-- The derivation property restated as an operator commutator: `[D_{a,b}, L_x] = L_{D_{a,b} x}`.
This is `innerDerivation_mul` read as a statement about composed multiplication operators; it is
the operator-level form used to build the double commutator `innerDerivation_comm` below. -/
theorem innerDerivation_mulLeft_comm (a b x : E) :
    (innerDerivation a b).comp (L x) - (L x).comp (innerDerivation a b) =
      L (innerDerivation a b x) := by
  ext z
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, mulLeft_apply]
  rw [innerDerivation_mul]
  abel

/-- The double commutator of two inner derivations:
`[D_{a,b}, D_{c,d}] = D_{D_{a,b}c, d} + D_{c, D_{a,b}d}`. This is pure associative operator
algebra built from `innerDerivation_mulLeft_comm` (applied once at `c` and once at `d`) plus the
elementary telescoping cancellation exhibited by expanding both composite arguments — no further
appeal to `cyclic_mulLeft_commutator` is needed beyond what is already packaged in
`innerDerivation_mul`. -/
theorem innerDerivation_comm (a b c d : E) :
    (innerDerivation a b).comp (innerDerivation c d) -
        (innerDerivation c d).comp (innerDerivation a b) =
      innerDerivation (innerDerivation a b c) d + innerDerivation c (innerDerivation a b d) := by
  ext z
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply]
  rw [innerDerivation_apply c d z, map_sub (innerDerivation a b),
    innerDerivation_apply c d (innerDerivation a b z)]
  rw [innerDerivation_mul a b c (d * z), innerDerivation_mul a b d (c * z),
    innerDerivation_mul a b d z, innerDerivation_mul a b c z]
  rw [innerDerivation_apply (innerDerivation a b c) d z,
    innerDerivation_apply c (innerDerivation a b d) z]
  simp only [mul_add]
  module

/-- The Jordan triple operator `V_{a,b} := L_{a*b} + D_{a,b}`.  Its action on any `x` is exactly
the Jordan triple product `{a,b,x}` (`triple_eq_V_apply`), so it packages `jordanTriple`'s middle
slot as a bundled linear operator, mirroring how `quadRepBilin a c` already packages `{a,·,c}`. -/
def tripleOperator (a b : E) : E →ₗ[ℝ] E := L (a * b) + innerDerivation a b

@[inherit_doc] scoped notation "V" => tripleOperator

omit [IsCommJordan E] in
/-- The Jordan triple operator `V_{a,b}` computes the Jordan triple product in its middle slot. -/
theorem triple_eq_V_apply (a b x : E) : V a b x = jordanTriple a b x := by
  simp only [tripleOperator, LinearMap.add_apply, innerDerivation_apply, mulLeft_apply,
    jordanTriple]
  rw [mul_comm x (b * a), mul_comm b a, mul_comm (a * x) b]
  abel

omit [IsCommJordan E] in
/-- Difference expansion of the inner derivation in its second defining argument. -/
theorem innerDerivation_sub_right (a b c : E) :
    innerDerivation a (b - c) = innerDerivation a b - innerDerivation a c := by
  ext x
  simp only [innerDerivation_apply, LinearMap.sub_apply]
  simp only [sub_mul, mul_sub]
  module

/-- **A second nonlinear derivation fact**: a "product rule" for the inner derivation's own first
(outer) argument, distinct from `innerDerivation_mul` (which is a product rule for `D`'s
*evaluation* argument). Obtained from a *single* atomic instance of `cyclic_mulLeft_commutator`
(no composition of two instances is needed here, unlike `innerDerivation_mul`), by rearranging
`cyclic_mulLeft_commutator a b q e = 0` into
`D (a*b) q e = D a (b*q) e + D b (a*q) e` and simplifying the resulting third bracket via
`innerDerivation_swap`. This is a genuine new building block toward the still-open Jordan-triple
fundamental identity: see `JB_ROADMAP.md` §7 for the precise remaining gap and the concrete leads
it opens (recursively applying this rule to reduce `D (a*b) (c*d)`, or the independently verified
15-term raw cyclic-instance certificate). -/
theorem innerDerivation_mul_left (a b q e : E) :
    innerDerivation (a * b) q e = innerDerivation a (b * q) e + innerDerivation b (a * q) e := by
  have h := cyclic_mulLeft_commutator a b q e
  rw [mul_comm q a] at h
  simp only [innerDerivation_apply]
  linear_combination (norm := module) -h

/-- The commutator law for Jordan triple operators:
`[V_{a,b}, V_{c,d}] = V_{{a,b,c},d} - V_{c,{b,a,d}}`.

This is the operator form of the Jordan-triple-system fundamental identity. -/
theorem tripleOperator_comm (a b c d : E) :
    (V a b).comp (V c d) - (V c d).comp (V a b) =
      V (jordanTriple a b c) d - V c (jordanTriple b a d) := by
  ext e

  simp only [
    tripleOperator,
    LinearMap.sub_apply,
    LinearMap.comp_apply,
    LinearMap.add_apply,
    mulLeft_apply,
    map_add
  ]

  /-
  Expand the two inner derivations acting on products.
  -/
  have e1 :
      innerDerivation a b ((c * d) * e) =
        (innerDerivation a b c) * d * e +
          c * (innerDerivation a b d) * e +
            (c * d) * (innerDerivation a b e) := by
    rw [innerDerivation_mul a b (c * d) e]
    rw [innerDerivation_mul a b c d]
    rw [add_mul]

  have e2 :
      innerDerivation c d ((a * b) * e) =
        (innerDerivation c d a) * b * e +
          a * (innerDerivation c d b) * e +
            (a * b) * (innerDerivation c d e) := by
    rw [innerDerivation_mul c d (a * b) e]
    rw [innerDerivation_mul c d a b]
    rw [add_mul]

  /-
  Commutator of inner derivations.
  -/
  have e3 :
      innerDerivation a b (innerDerivation c d e) -
          innerDerivation c d (innerDerivation a b e) =
        innerDerivation (innerDerivation a b c) d e +
          innerDerivation c (innerDerivation a b d) e := by
    have h := DFunLike.congr_fun (innerDerivation_comm a b c d) e
    simpa only [
      LinearMap.sub_apply,
      LinearMap.comp_apply,
      LinearMap.add_apply
    ] using h

  /-
  Jordan cyclic identity for the product pair.
  -/
  have e4 :
      innerDerivation (a * b) (c * d) e =
        innerDerivation ((a * b) * c) d e -
          innerDerivation c ((a * b) * d) e := by
    have h := innerDerivation_mul_left (a * b) c d e
    rw [h]
    module

  /-
  Express the triple products in L_{ab} + D_{a,b} form.
  -/
  have hJ1 :
      jordanTriple a b c =
        (a * b) * c + innerDerivation a b c := by
    rw [← triple_eq_V_apply]
    rfl

  have hJ2 :
      jordanTriple b a d =
        (a * b) * d - innerDerivation a b d := by
    rw [← triple_eq_V_apply]
    simp only [
      tripleOperator,
      LinearMap.add_apply,
      mulLeft_apply
    ]
    rw [
      mul_comm b a,
      innerDerivation_swap b a,
      LinearMap.neg_apply
    ]
    module

  rw [hJ1, hJ2]

  simp only [
    add_mul,
    sub_mul,
    mul_sub,
    innerDerivation_add_left,
    LinearMap.add_apply
  ]

  /-
  Convert the raw left-multiplication commutator into an inner derivation.
  -/
  have e4' :
      a * b * (c * d * e) - c * d * (a * b * e) =
        innerDerivation (a * b * c) d e -
          innerDerivation c (a * b * d) e := by
    rw [← innerDerivation_apply, e4]

  /-
  Remaining product/derivation relation.
  -/
  have hQ :
      c * (a * b * d) * e - a * b * c * d * e -
          (innerDerivation c d a * b * e +
            a * (innerDerivation c d b) * e) = 0 := by
    have step1 :
        c * (a * b * d) * e =
          c * (d * (a * b)) * e := by
      rw [mul_comm (a * b) d]

    have step2 :
        a * b * c * d * e =
          d * (c * (a * b)) * e := by
      rw [
        mul_comm d (c * (a * b)),
        mul_comm c (a * b)
      ]

    have step3 :
        innerDerivation c d a * b * e +
            a * (innerDerivation c d b) * e =
          c * (d * (a * b)) * e -
            d * (c * (a * b)) * e := by
      have h6 :
          (innerDerivation c d a * b +
              a * innerDerivation c d b) * e =
            innerDerivation c d (a * b) * e := by
        rw [innerDerivation_mul c d a b]

      rw [add_mul] at h6
      rwa [
        innerDerivation_apply c d (a * b),
        sub_mul
      ] at h6

    rw [step1, step2, step3]
    module

  /-
  Expand the product derivations first.
  -/
  rw [e1, e2]

  simp only [
    innerDerivation_sub_right,
    LinearMap.sub_apply
  ]

  have e3' :
      innerDerivation a b (innerDerivation c d e) =
        innerDerivation c d (innerDerivation a b e) +
          innerDerivation (innerDerivation a b c) d e +
          innerDerivation c (innerDerivation a b d) e := by
    have h :=
      (sub_eq_iff_eq_add).mp e3
    calc
      innerDerivation a b (innerDerivation c d e) =
          (innerDerivation (innerDerivation a b c) d e +
            innerDerivation c (innerDerivation a b d) e) +
            innerDerivation c d (innerDerivation a b e) := h
      _ =
          innerDerivation c d (innerDerivation a b e) +
            innerDerivation (innerDerivation a b c) d e +
            innerDerivation c (innerDerivation a b d) e := by
        abel

  have e4'' :
      a * b * (c * d * e) =
        c * d * (a * b * e) +
          innerDerivation (a * b * c) d e -
          innerDerivation c (a * b * d) e := by
    have h :=
      (sub_eq_iff_eq_add).mp e4'
    calc
      a * b * (c * d * e) =
          (innerDerivation (a * b * c) d e -
            innerDerivation c (a * b * d) e) +
            c * d * (a * b * e) := h
      _ =
          c * d * (a * b * e) +
            innerDerivation (a * b * c) d e -
            innerDerivation c (a * b * d) e := by
        abel

  have hQ' :
      c * (a * b * d) * e =
        a * b * c * d * e +
          innerDerivation c d a * b * e +
          a * innerDerivation c d b * e := by
    have h :
        c * (a * b * d) * e - a * b * c * d * e =
          innerDerivation c d a * b * e +
            a * innerDerivation c d b * e := by
      have h0 := hQ
      -- hQ is `(X - Y) - Z = 0`, hence `X - Y = Z`.
      exact sub_eq_zero.mp h0

    have h' := (sub_eq_iff_eq_add).mp h
    calc
      c * (a * b * d) * e =
          (innerDerivation c d a * b * e +
            a * innerDerivation c d b * e) +
            a * b * c * d * e := h'
      _ =
          a * b * c * d * e +
            innerDerivation c d a * b * e +
            a * innerDerivation c d b * e := by
        abel

  rw [e3', e4'', hQ']

  abel

/-- A first genuine consequence of `tripleOperator_comm` toward the Stage A item 1 target
`U (U a b) = U a * U b * U a`: specializing `(a, b, c, d) := (x, y, x, z)` and evaluating at `x`
collapses every diagonal slot (`{x, ·, x}`) to a `U_x` evaluation, via `jordanTriple_diag` and
`jordanTriple_outer_comm`. Not yet the fundamental formula itself: `V_quadRep_eq_quadRep_triple`
below reaches it by combining this identity with its `y ↔ z` companion. -/
theorem tripleOperator_quadRep_step (x y z : E) :
    V x y (U x z) =
      (2 : ℝ) • V x z (U x y) - U x (jordanTriple y x z) := by
  have h := DFunLike.congr_fun (tripleOperator_comm x y x z) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
  have hVxzx : V x z x = U x z := (triple_eq_V_apply x z x).trans (jordanTriple_diag x z)
  have hVxyx : V x y x = U x y := (triple_eq_V_apply x y x).trans (jordanTriple_diag x y)
  have hdiagxyx : jordanTriple x y x = U x y := jordanTriple_diag x y
  rw [hVxzx, hVxyx, hdiagxyx] at h
  have hswap : V (U x y) z x = V x z (U x y) := by
    rw [triple_eq_V_apply, triple_eq_V_apply, jordanTriple_outer_comm]
  have hdiag2 : V x (jordanTriple y x z) x = U x (jordanTriple y x z) :=
    (triple_eq_V_apply x (jordanTriple y x z) x).trans
      (jordanTriple_diag x (jordanTriple y x z))
  rw [hswap, hdiag2] at h
  linear_combination (norm := module) h

/-- Combining `tripleOperator_quadRep_step` with its own `y ↔ z` companion (and
`jordanTriple_outer_comm`, which identifies `jordanTriple z x y` with `jordanTriple y x z`)
eliminates the `V x z (U x y)` cross-term entirely. -/
theorem V_quadRep_eq_quadRep_triple (x y z : E) :
    V x y (U x z) = U x (jordanTriple y x z) := by
  have h1 := tripleOperator_quadRep_step x y z
  have h2 := tripleOperator_quadRep_step x z y
  have hswap :
      jordanTriple z x y = jordanTriple y x z := by
    rw [jordanTriple_outer_comm]
  rw [hswap] at h2
  linear_combination (norm := module)
    (-1 / 3 : ℝ) • h1 + (-2 / 3 : ℝ) • h2

/-- Pointwise form of the fundamental formula for the quadratic representation:
`U_{U_x y} z = U_x U_y U_x z`. -/
theorem quadRep_fundamental_apply (x y z : E) :
    U (U x y) z = U x (U y (U x z)) := by

  /-
  Step 1.

  Specialize the triple-operator commutator at
      (a,b,c,d,e) = (z,x,y,x,y).

  This gives an identity from which we solve for `U y (U x z)`.
  -/
  have hinner0 :=
    DFunLike.congr_fun (tripleOperator_comm z x y x) y

  simp only [
    LinearMap.sub_apply,
    LinearMap.comp_apply
  ] at hinner0

  have hxzx :
      jordanTriple x z x = U x z :=
    jordanTriple_diag x z

  have hright :
      V (jordanTriple y x z) x y =
        V y x (jordanTriple y x z) := by
    rw [
      triple_eq_V_apply,
      triple_eq_V_apply,
      jordanTriple_outer_comm
    ]

  have hdiag :
      V y (U x z) y = U y (U x z) :=
    (triple_eq_V_apply y (U x z) y).trans
      (jordanTriple_diag y (U x z))

  have houter :
      jordanTriple z x y = jordanTriple y x z := by
    exact jordanTriple_outer_comm z x y

  have hyxy :
      V y x y = U y x :=
    (triple_eq_V_apply y x y).trans
      (jordanTriple_diag y x)

  have hzxy :
      V z x y = jordanTriple y x z := by
    rw [
      triple_eq_V_apply,
      jordanTriple_outer_comm
    ]

  rw [
    houter,
    hxzx,
    hright,
    hdiag,
    hyxy,
    hzxy
  ] at hinner0

  /-
  Now:

      hinner0 :
        V z x (U y x) - V y x {y,x,z}
          =
        V y x {y,x,z} - U y (U x z).

  Solve additively for `U y (U x z)`.
  -/
  have hinner :
      U y (U x z) =
        V y x (jordanTriple y x z) +
          V y x (jordanTriple y x z) -
          V z x (U y x) := by
    calc
      U y (U x z) =
          V y x (jordanTriple y x z) -
            (V y x (jordanTriple y x z) -
              U y (U x z)) := by
        abel
      _ =
          V y x (jordanTriple y x z) -
            (V z x (U y x) -
              V y x (jordanTriple y x z)) := by
        rw [← hinner0]
      _ =
          V y x (jordanTriple y x z) +
            V y x (jordanTriple y x z) -
            V z x (U y x) := by
        abel

  /-
  Apply `U x` to the preceding identity.
  -/
  have hinnerUx0 :=
    congrArg (fun w => U x w) hinner

  have hinnerUx :
      U x (U y (U x z)) =
        U x (V y x (jordanTriple y x z)) +
          U x (V y x (jordanTriple y x z)) -
          U x (V z x (U y x)) := by
    simpa only [
      map_add,
      map_sub
    ] using hinnerUx0

  /-
  Step 2.

  Specialize the triple-operator commutator at
      (a,b,c,d,e) = (x,y,x,z,U_x y).
  -/
  have hmain :=
    DFunLike.congr_fun
      (tripleOperator_comm x y x z)
      (U x y)

  simp only [
    LinearMap.sub_apply,
    LinearMap.comp_apply
  ] at hmain

  have hdiagxy :
      jordanTriple x y x = U x y :=
    jordanTriple_diag x y

  rw [hdiagxy] at hmain

  /-
  Diagonal term:
      V_{U_x y,z}(U_x y) = U_{U_x y} z.
  -/
  have hUU :
      V (U x y) z (U x y) =
        U (U x y) z :=
    (triple_eq_V_apply (U x y) z (U x y)).trans
      (jordanTriple_diag (U x y) z)

  /-
  V_{x,z}(U_x y) = U_x {y,x,z}.
  -/
  have h1 :
      V x z (U x y) =
        U x (jordanTriple y x z) := by
    have h :=
      V_quadRep_eq_quadRep_triple x z y
    rwa [jordanTriple_outer_comm z x y] at h

  /-
  V_{x,y}(U_x {y,x,z})
    =
  U_x V_{y,x}({y,x,z}).
  -/
  have h2 :
      V x y (U x (jordanTriple y x z)) =
        U x (V y x (jordanTriple y x z)) := by
    have h :=
      V_quadRep_eq_quadRep_triple
        x y (jordanTriple y x z)
    simpa only [triple_eq_V_apply] using h

  /-
  V_{x,y}(U_x y) = U_x(U_y x).
  -/
  have h3 :
      V x y (U x y) =
        U x (U y x) := by
    have h :=
      V_quadRep_eq_quadRep_triple x y y
    have hyxy' :
        jordanTriple y x y = U y x :=
      jordanTriple_diag y x
    rwa [hyxy'] at h

  /-
  V_{x,z}(U_x(U_y x))
    =
  U_x V_{z,x}(U_y x).
  -/
  have h4 :
      V x z (U x (U y x)) =
        U x (V z x (U y x)) := by
    have h :=
      V_quadRep_eq_quadRep_triple
        x z (U y x)
    simpa only [triple_eq_V_apply] using h

  /-
  V_{x,{y,x,z}}(U_x y)
    =
  U_x V_{{y,x,z},x}(y).
  -/
  have h5 :
      V x (jordanTriple y x z) (U x y) =
        U x (V (jordanTriple y x z) x y) := by
    have h :=
      V_quadRep_eq_quadRep_triple
        x (jordanTriple y x z) y
    simpa only [triple_eq_V_apply] using h

  /-
  Outer symmetry:
      V_{{y,x,z},x}(y)
        =
      V_{y,x}({y,x,z}).
  -/
  have h6 :
      V (jordanTriple y x z) x y =
        V y x (jordanTriple y x z) := by
    rw [
      triple_eq_V_apply,
      triple_eq_V_apply,
      jordanTriple_outer_comm
    ]

  rw [
    h1,
    h2,
    h3,
    h4,
    hUU,
    h5,
    h6
  ] at hmain

  /-
  After the rewrites, hmain has the additive form

      P - Q = R - P,

  where

      P = U_x(V_{y,x}{y,x,z}),
      Q = U_x(V_{z,x}(U_y x)),
      R = U_{U_x y} z.

  Solve for R using only additive-group normalization.
  -/
  have hmain' :
      U (U x y) z =
        U x (V y x (jordanTriple y x z)) +
          U x (V y x (jordanTriple y x z)) -
          U x (V z x (U y x)) := by
    calc
      U (U x y) z =
          (U (U x y) z -
            U x (V y x (jordanTriple y x z))) +
            U x (V y x (jordanTriple y x z)) := by
        abel
      _ =
          (U x (V y x (jordanTriple y x z)) -
            U x (V z x (U y x))) +
            U x (V y x (jordanTriple y x z)) := by
        rw [← hmain]
      _ =
          U x (V y x (jordanTriple y x z)) +
            U x (V y x (jordanTriple y x z)) -
            U x (V z x (U y x)) := by
        abel

  exact hmain'.trans hinnerUx.symm


/-- The fundamental formula for the quadratic representation:
`U_{U_x y} = U_x ∘ U_y ∘ U_x`. -/
theorem quadRep_fundamental (x y : E) :
    U (U x y) = (U x).comp ((U y).comp (U x)) := by
  ext z
  exact quadRep_fundamental_apply x y z

/-- The fundamental formula holds on the associative algebra generated by one element.  This
is the fully proved common-generator sector of the general identity: both sides send `a^[k]` to
`a^[4*m + 2*n + k]`.

The unrestricted formula additionally needs a three-variable polarization argument, since its
middle element need not lie in the one-generated algebra. -/
theorem quadRep_fundamental_jpow (a : E) (m n k : ℕ) :
    U (U ((a ^[m]) : E) ((a ^[n]) : E)) ((a ^[k]) : E) =
      U ((a ^[m]) : E) (U ((a ^[n]) : E) (U ((a ^[m]) : E) ((a ^[k]) : E))) := by
  rw [quadRep_jpow_jpow a m n]
  rw [quadRep_jpow_jpow a (2 * m + n) k]
  rw [quadRep_jpow_jpow a m k]
  rw [quadRep_jpow_jpow a n (2 * m + k)]
  rw [quadRep_jpow_jpow a m (2 * n + (2 * m + k))]
  congr 1
  omega

end JordanAlgebra
