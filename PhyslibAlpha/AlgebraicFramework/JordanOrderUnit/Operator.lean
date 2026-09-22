/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Basic

/-!

# Powers, multiplication operators, and the quadratic representation

## i. Overview

Three pieces of observable API sit directly on top of the bare Jordan product:

- **Powers** `a ^[n]`, defined by the obvious recursion `a^[0] = 1`, `a^[n+1] = a ∘ a^[n]`. This
  is a fixed bracketing (always multiply by `a` on the left), so it needs no power-associativity
  theorem to be well defined — it is simply iterated application of `L_a`.
- **The multiplication operator** `L a`, `L a b = a ∘ b`, linear in `b` because the Jordan product
  is real-bilinear.
- **The quadratic representation** `U a := 2 L_a² - L_{a²}`. In the special (associative) case this
  is exactly `U_a(b) = a b a`, the two-sided operator-conjugation map —
  `CStarAlgebra/Jordan.lean` proves this
  identity for the canonical C⋆-algebra realization. Abstractly, `U_a` is the Jordan-algebraic
  substitute for "conjugate by `a`", available even though the raw associative product `aba` does
  not typecheck at this level of generality.

## ii. Key definitions and results

- `IsJordanOrderUnit.jpow`, notation `a ^[n]`
- `IsJordanOrderUnit.mulLeft`, notation `L`
- `IsJordanOrderUnit.quadRep`, notation `U`
- `IsJordanOrderUnit.quadRep_apply`

## iii. Table of contents

- A. Powers
- B. The multiplication operator `L_a`
- C. The quadratic representation `U_a`

-/

@[expose] public section

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E]

/-! ## A. Powers -/

/-- The `n`-th Jordan power of `a`, defined by the fixed left-bracketing recursion
`a^[0] = 1`, `a^[n+1] = a ∘ a^[n]`. -/
def jpow (a : E) : ℕ → E
  | 0 => 1
  | n + 1 => a * jpow a n

@[inherit_doc] scoped notation:max a " ^[" n "]" => jpow a n

@[simp] theorem jpow_zero (a : E) : a ^[0] = 1 := rfl

theorem jpow_succ (a : E) (n : ℕ) : a ^[n + 1] = a * a ^[n] := rfl

@[simp] theorem jpow_one (a : E) : a ^[1] = a := by
  rw [jpow_succ, jpow_zero, mul_one]

/-- The second Jordan power is the Jordan square, `a ∘ a`. -/
theorem jpow_two (a : E) : a ^[2] = a * a := by
  rw [jpow_succ, jpow_one]

/-! ## B. The multiplication operator `L_a` -/

section Linear

variable [Module ℝ E] [SMulCommClass ℝ E E]

/-- The Jordan multiplication operator `L a : E →ₗ[ℝ] E`, `L a b = a ∘ b`. Linear in `b` since the
Jordan product distributes over `+` (`NonUnitalNonAssocCommRing`) and commutes with real scalars
(`SMulCommClass ℝ E E`). -/
def mulLeft (a : E) : E →ₗ[ℝ] E where
  toFun b := a * b
  map_add' := mul_add a
  map_smul' c b := by simp [mul_smul_comm]

@[inherit_doc] scoped notation "L" => mulLeft

@[simp] theorem mulLeft_apply (a b : E) : L a b = a * b := rfl

theorem mulLeft_one (a : E) : L a 1 = a := _root_.mul_one a

theorem mulLeft_one_apply (a : E) : L 1 a = a := _root_.one_mul a

/-! ## C. The quadratic representation `U_a` -/

/-- The quadratic representation `U a := 2 • L_a ∘ L_a - L_{a ^[2]}`, the Jordan-algebraic
substitute for two-sided conjugation `b ↦ a b a`. See `CStarAlgebra/Jordan.lean` for the theorem
that this is
*literally* `aba` in the canonical C⋆-algebra realization. -/
def quadRep (a : E) : E →ₗ[ℝ] E :=
  (2 : ℝ) • ((mulLeft a).comp (mulLeft a)) - mulLeft (a ^[2])

@[inherit_doc] scoped notation "U" => quadRep

theorem quadRep_apply (a b : E) : U a b = (2 : ℝ) • (a * (a * b)) - a ^[2] * b := by
  simp [quadRep, jpow_two]

@[simp] theorem quadRep_zero_apply (b : E) : U (0 : E) b = 0 := by
  rw [quadRep_apply]
  simp [jpow_two]

@[simp] theorem quadRep_add_right (a b c : E) : U a (b + c) = U a b + U a c := by
  exact (U a).map_add b c

theorem quadRep_smul_right (r : ℝ) (a b : E) : U a (r • b) = r • U a b := by
  exact (U a).map_smul r b

/-- The bilinear polarization of the quadratic representation.  It is the cross-effect of
`a ↦ U a`: in a special Jordan algebra it is the symmetrized two-sided action
`x ↦ axb + bxa`.  Defining it at the operator level, rather than repeatedly expanding
`U (a + b)`, is the natural interface for multivariable identities. -/
def quadRepPolar (a b : E) : E →ₗ[ℝ] E :=
  (2 : ℝ) • (((L a).comp (L b)) + ((L b).comp (L a)) - L (a * b))

/-- The standard bilinear quadratic operator.  `quadRepPolar` is its literal cross-effect
and therefore equals twice this operator.  Keeping this undivided normalization is essential for
the finite polarization identities used in the algebraic proof of the fundamental formula. -/
def quadRepBilin (a b : E) : E →ₗ[ℝ] E :=
  ((L a).comp (L b)) + ((L b).comp (L a)) - L (a * b)

/-- Pointwise form of the standard bilinear quadratic operator. -/
theorem quadRepBilin_apply (a b x : E) :
    quadRepBilin a b x = a * (b * x) + b * (a * x) - (a * b) * x := by
  simp only [quadRepBilin, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    mulLeft_apply]

/-- The standard bilinear quadratic operator is symmetric. -/
theorem quadRepBilin_comm (a b : E) : quadRepBilin a b = quadRepBilin b a := by
  ext x
  rw [quadRepBilin_apply, quadRepBilin_apply, mul_comm b a]
  abel

/-- Additivity in the first variable of the standard quadratic polarization. -/
theorem quadRepBilin_add_left (a b c : E) :
    quadRepBilin (a + b) c = quadRepBilin a c + quadRepBilin b c := by
  ext x
  rw [quadRepBilin_apply]
  change (a + b) * (c * x) + c * ((a + b) * x) - ((a + b) * c) * x =
    quadRepBilin a c x + quadRepBilin b c x
  rw [quadRepBilin_apply, quadRepBilin_apply]
  simp only [add_mul, mul_add]
  module

/-- Real linearity in the first variable of the standard quadratic polarization. -/
theorem quadRepBilin_smul_left (r : ℝ) (a b : E) :
    quadRepBilin (r • a) b = r • quadRepBilin a b := by
  ext x
  rw [quadRepBilin_apply]
  change (r • a) * (b * x) + b * ((r • a) * x) - ((r • a) * b) * x =
    r • quadRepBilin a b x
  rw [quadRepBilin_apply]
  have hsmul_mul (z y : E) : (r • z) * y = r • (z * y) := by
    calc
      (r • z) * y = y * (r • z) := mul_comm _ _
      _ = r • (y * z) := mul_smul_comm r y z
      _ = r • (z * y) := by rw [mul_comm y z]
  rw [hsmul_mul a (b * x), hsmul_mul a x, mul_smul_comm,
    hsmul_mul a b, hsmul_mul (a * b) x]
  simp only [smul_add, smul_sub]

/-- Additivity in the second variable of the standard quadratic polarization. -/
theorem quadRepBilin_add_right (a b c : E) :
    quadRepBilin a (b + c) = quadRepBilin a b + quadRepBilin a c := by
  rw [quadRepBilin_comm, quadRepBilin_comm a b, quadRepBilin_comm a c,
    quadRepBilin_add_left]

/-- Real linearity in the second variable of the standard quadratic polarization. -/
theorem quadRepBilin_smul_right (r : ℝ) (a b : E) :
    quadRepBilin a (r • b) = r • quadRepBilin a b := by
  calc
    quadRepBilin a (r • b) = quadRepBilin (r • b) a := quadRepBilin_comm _ _
    _ = r • quadRepBilin b a := quadRepBilin_smul_left r b a
    _ = r • quadRepBilin a b := by rw [quadRepBilin_comm]

/-- Signed second-variable specialization of the bilinear quadratic operator. -/
theorem quadRepBilin_neg_right (a b : E) :
    quadRepBilin a (-b) = -quadRepBilin a b := by
  simpa using quadRepBilin_smul_right (-1 : ℝ) a b

/-- Signed first-variable specialization of the bilinear quadratic operator. -/
theorem quadRepBilin_neg_left (a b : E) :
    quadRepBilin (-a) b = -quadRepBilin a b := by
  calc
    quadRepBilin (-a) b = quadRepBilin b (-a) := quadRepBilin_comm _ _
    _ = -quadRepBilin b a := quadRepBilin_neg_right _ _
    _ = -quadRepBilin a b := by rw [quadRepBilin_comm]

/-- Difference expansion in the second variable of the bilinear quadratic operator. -/
theorem quadRepBilin_sub_right (a b c : E) :
    quadRepBilin a (b - c) = quadRepBilin a b - quadRepBilin a c := by
  rw [sub_eq_add_neg, quadRepBilin_add_right, quadRepBilin_neg_right]
  abel

/-- The cross-effect normalization is twice the standard bilinear quadratic operator. -/
theorem quadRepPolar_eq_two_smul_quadRepBilin (a b : E) :
    quadRepPolar a b = (2 : ℝ) • quadRepBilin a b := by
  rw [quadRepPolar, quadRepBilin]

/-- The diagonal of the standard bilinear quadratic operator is the quadratic representation. -/
theorem quadRepBilin_self (a : E) : quadRepBilin a a = U a := by
  ext x
  simp only [quadRepBilin, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    mulLeft_apply]
  rw [quadRep_apply]
  simp only [jpow_two]
  module

/-- Pointwise form of the polarized quadratic representation. -/
theorem quadRepPolar_apply (a b x : E) :
    quadRepPolar a b x =
      (2 : ℝ) • (a * (b * x) + b * (a * x) - (a * b) * x) := by
  simp only [quadRepPolar, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, mulLeft_apply]

/-- Polarization is symmetric in its two outer variables. -/
theorem quadRepPolar_comm (a b : E) : quadRepPolar a b = quadRepPolar b a := by
  ext x
  rw [quadRepPolar_apply, quadRepPolar_apply, mul_comm b a]
  abel

/-- The polarization is additive in its first outer variable. -/
theorem quadRepPolar_add_left (a b c : E) :
    quadRepPolar (a + b) c = quadRepPolar a c + quadRepPolar b c := by
  ext x
  rw [quadRepPolar_apply]
  change (2 : ℝ) • ((a + b) * (c * x) + c * ((a + b) * x) - ((a + b) * c) * x) =
    quadRepPolar a c x + quadRepPolar b c x
  rw [quadRepPolar_apply, quadRepPolar_apply]
  simp only [add_mul, mul_add]
  module

/-- The polarization is real-linear in its first outer variable. -/
theorem quadRepPolar_smul_left (r : ℝ) (a b : E) :
    quadRepPolar (r • a) b = r • quadRepPolar a b := by
  ext x
  rw [quadRepPolar_apply]
  change (2 : ℝ) • ((r • a) * (b * x) + b * ((r • a) * x) - ((r • a) * b) * x) =
    r • quadRepPolar a b x
  rw [quadRepPolar_apply]
  have hsmul_mul (z y : E) : (r • z) * y = r • (z * y) := by
    calc
      (r • z) * y = y * (r • z) := mul_comm _ _
      _ = r • (y * z) := mul_smul_comm r y z
      _ = r • (z * y) := by rw [mul_comm y z]
  rw [hsmul_mul a (b * x), hsmul_mul a x, mul_smul_comm,
    hsmul_mul a b, hsmul_mul (a * b) x]
  simp only [smul_add, smul_sub]
  module

/-- The polarization is additive in its second outer variable. -/
theorem quadRepPolar_add_right (a b c : E) :
    quadRepPolar a (b + c) = quadRepPolar a b + quadRepPolar a c := by
  rw [quadRepPolar_comm, quadRepPolar_comm a b, quadRepPolar_comm a c,
    quadRepPolar_add_left]

/-- The polarization is real-linear in its second outer variable. -/
theorem quadRepPolar_smul_right (r : ℝ) (a b : E) :
    quadRepPolar a (r • b) = r • quadRepPolar a b := by
  calc
    quadRepPolar a (r • b) = quadRepPolar (r • b) a := quadRepPolar_comm _ _
    _ = r • quadRepPolar b a := quadRepPolar_smul_left r b a
    _ = r • quadRepPolar a b := by rw [quadRepPolar_comm b a]

/-- The diagonal of the polarization is twice the original quadratic representation. -/
theorem quadRepPolar_self (a : E) : quadRepPolar a a = (2 : ℝ) • U a := by
  ext x
  rw [quadRepPolar_apply]
  change (2 : ℝ) • (a * (a * x) + a * (a * x) - (a * a) * x) =
    (2 : ℝ) • U a x
  rw [quadRep_apply]
  simp only [jpow_two]
  module

/-- The quadratic representation splits into its two diagonal pieces and its polarized
cross-effect. -/
theorem quadRep_add_apply (a b x : E) :
    U (a + b) x = U a x + quadRepPolar a b x + U b x := by
  rw [quadRepPolar_apply]
  repeat' rw [quadRep_apply]
  simp only [jpow_two, add_mul, mul_add]
  rw [mul_comm b a]
  module

/-- Exact additive polarization of the quadratic representation in standard normalization. -/
theorem quadRep_add_eq (a b : E) :
    U (a + b) = U a + (2 : ℝ) • quadRepBilin a b + U b := by
  ext x
  rw [quadRep_add_apply, quadRepPolar_eq_two_smul_quadRepBilin]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]

/-- Signed additive polarization, obtained from the same quadratic cross-effect.  Together with
`quadRep_add_eq`, this gives the two exact evaluations used to isolate a quadratic coefficient. -/
theorem quadRep_sub_eq (a b : E) :
    U (a - b) = U a - (2 : ℝ) • quadRepBilin a b + U b := by
  have hneg : U (-b) = U b := by
    ext x
    rw [quadRep_apply, quadRep_apply]
    simp only [jpow_two, neg_mul, mul_neg]
    module
  rw [sub_eq_add_neg, quadRep_add_eq, quadRepBilin_neg_right, hneg]
  module

/-- The quadratic representation of a three-term sum, expressed through the canonical symmetric
bilinear cross-effect.  This is the coefficient-expansion interface for polarizing identities in
quadratic representations; it keeps all mixed terms in the single `quadRepBilin` API. -/
theorem quadRep_add_add_eq (a b c : E) :
    U (a + b + c) =
      U a + U b + U c +
        (2 : ℝ) • quadRepBilin a b +
          (2 : ℝ) • quadRepBilin a c +
            (2 : ℝ) • quadRepBilin b c := by
  rw [quadRep_add_eq, quadRep_add_eq, quadRepBilin_add_left]
  module

omit [SMulCommClass ℝ E E] in
/-- Exact square expansion for the positive polarization evaluation. -/
theorem add_mul_self (a b : E) :
    (a + b) * (a + b) = a * a + (2 : ℝ) • (a * b) + b * b := by
  simp only [add_mul, mul_add]
  rw [mul_comm b a]
  module

omit [SMulCommClass ℝ E E] in
/-- Exact square expansion for the signed polarization evaluation. -/
theorem sub_mul_self (a b : E) :
    (a - b) * (a - b) = a * a - (2 : ℝ) • (a * b) + b * b := by
  simp only [sub_mul, mul_sub]
  rw [mul_comm b a]
  module

/-- Quadratic representations are homogeneous of degree two in their outer argument. -/
theorem quadRep_smul_apply (r : ℝ) (a b : E) :
    U (r • a) b = r ^ 2 • U a b := by
  rw [quadRep_apply, quadRep_apply]
  simp [jpow_two, mul_smul_comm, smul_smul, smul_sub, pow_two, mul_comm, mul_assoc]

/-- Quadratic homogeneity of the representation, as an equality of operators. -/
theorem quadRep_smul_eq (r : ℝ) (a : E) :
    U (r • a) = r ^ 2 • U a := by
  ext b
  rw [quadRep_smul_apply]
  simp only [LinearMap.smul_apply]

theorem quadRep_neg_apply (a b : E) : U (-a) b = U a b := by
  simpa using (quadRep_smul_apply (-1 : ℝ) a b)

/-- Sign invariance of the quadratic representation, as an equality of operators. -/
theorem quadRep_neg (a : E) : U (-a) = U a := by
  ext b
  exact quadRep_neg_apply a b

/-- The quadratic representation of the order unit is the identity: `U_1 = id`. The Jordan
identity element acts as "conjugate by the identity", i.e. does nothing. -/
@[simp] theorem quadRep_one_apply (b : E) : U (1 : E) b = b := by
  have h1 : (1 : E) * ((1 : E) * b) = b := by
    rw [_root_.one_mul, _root_.one_mul]
  have h2 : (1 : E) ^[2] * b = b := by
    rw [jpow_two, _root_.one_mul, _root_.one_mul]
  rw [quadRep_apply, h1, h2]
  module

@[simp] theorem quadRep_one_comp (a : E) : (U (1 : E)).comp (U a) = U a := by
  ext b
  simp

@[simp] theorem quadRep_comp_one (a : E) : (U a).comp (U (1 : E)) = U a := by
  ext b
  simp

/-- The quadratic representation of `a`, evaluated at the order unit, recovers the Jordan square:
`U_a(1) = a²`. Conjugating the identity by `a` gives back `a²`, matching the associative picture
`a \cdot 1 \cdot a = a^2`. -/
@[simp] theorem quadRep_apply_one (a : E) : U a (1 : E) = a ^[2] := by
  have h1 : a * (a * (1 : E)) = a * a := by rw [_root_.mul_one]
  have h2 : a ^[2] * (1 : E) = a ^[2] := _root_.mul_one _
  rw [quadRep_apply, h1, h2, ← jpow_two]
  module

/-! ## D. The Jordan commutation law -/

/-- Quadratic representation by `a` commutes with multiplication by `a`.

This is the operator form of the Jordan identity used at its weakest level: the only nontrivial
interchange is `a² ∘ (a ∘ x) = a ∘ (a² ∘ x)`.  It is the basic invariant-subalgebra fact behind
the one-generator and Peirce developments. -/
theorem quadRep_mulLeft [IsCommJordan E] (a x : E) : U a (a * x) = a * U a x := by
  rw [quadRep_apply, quadRep_apply]
  have hJordan : a ^[2] * (a * x) = a * (a ^[2] * x) := by
    rw [jpow_two]
    exact IsJordan.lmul_lmul_comm_lmul a x
  rw [hJordan]
  rw [mul_sub, mul_smul_comm]

/-- Quadratic representation by `a` also commutes with multiplication by the square `a²`.
Together with `quadRep_mulLeft`, this says that `U_a` preserves the associative algebra generated
by `a` at the operator level, without appealing to an ambient associative realization. -/
theorem quadRep_mulLeft_sq [IsCommJordan E] (a x : E) :
    U a (a ^[2] * x) = a ^[2] * U a x := by
  rw [quadRep_apply, quadRep_apply, mul_sub, mul_smul_comm]
  have hJordan (y : E) : a ^[2] * (a * y) = a * (a ^[2] * y) := by
    rw [jpow_two]
    exact IsJordan.lmul_lmul_comm_lmul a y
  rw [← hJordan x, ← hJordan (a * x)]

/-- Bundled form of `quadRep_mulLeft`: the quadratic representation commutes with `L_a`. -/
theorem commute_quadRep_mulLeft [IsCommJordan E] (a : E) : Commute (U a) (L a) := by
  ext x
  exact quadRep_mulLeft a x

/-- Bundled form of `quadRep_mulLeft_sq`: the quadratic representation commutes with `L_(a²)`. -/
theorem commute_quadRep_mulLeft_sq [IsCommJordan E] (a : E) : Commute (U a) (L (a ^[2])) := by
  ext x
  exact quadRep_mulLeft_sq a x

/-! ## E. The inner derivation `D_{a,b}` -/

/-- The inner derivation associated to a pair `(a, b)`: `D_{a,b} := L_a ∘ L_b - L_b ∘ L_a`.  This
is well defined with no Jordan hypothesis (it only needs the bare bilinear product), but it
becomes a genuine derivation of the Jordan product exactly when the Jordan identity holds
(`innerDerivation_mul` in `Quadratic/Fundamental.lean`).  It is kept here, at the weakest level
alongside `L` and `U`, because it is reusable infrastructure beyond the fundamental-formula proof
(automorphisms, generators, Peirce theory, symmetry actions, dynamics), not a throwaway auxiliary
of a single theorem. -/
def innerDerivation (a b : E) : E →ₗ[ℝ] E := (L a).comp (L b) - (L b).comp (L a)

/-- Pointwise form of the inner derivation. -/
theorem innerDerivation_apply (a b x : E) : innerDerivation a b x = a * (b * x) - b * (a * x) := by
  simp only [innerDerivation, LinearMap.sub_apply, LinearMap.comp_apply, mulLeft_apply]

/-- The inner derivation is antisymmetric in its two defining arguments. -/
theorem innerDerivation_swap (a b : E) : innerDerivation a b = -innerDerivation b a := by
  ext x
  simp only [innerDerivation_apply, LinearMap.neg_apply]
  abel

@[simp] theorem innerDerivation_self (a : E) : innerDerivation a a = 0 := by
  ext x
  simp [innerDerivation_apply]

end Linear

end JordanAlgebra
