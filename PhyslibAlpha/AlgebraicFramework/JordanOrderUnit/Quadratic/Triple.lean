/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Operator

/-!

# The Jordan triple product

The symmetric polarization of the quadratic representation has a more structural form: the
Jordan triple product

`{a, b, c} = a * (b * c) + c * (b * a) - (a * c) * b`.

It is symmetric and bilinear in the outer variables and linear in the middle variable. Its
diagonal is precisely the quadratic representation, `{a, b, a} = U_a b`. Thus it is the right
language for the multivariable (Macdonald) proof of the quadratic fundamental formula.

-/

@[expose] public section

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E] [SMulCommClass ℝ E E]

open scoped JordanAlgebra

/-- The Jordan triple product, written directly to retain a computable algebraic definition. -/
def jordanTriple (a b c : E) : E := a * (b * c) + c * (b * a) - (a * c) * b

/-- The triple product is precisely the action of the canonical bilinear quadratic operator on
its middle variable.  Thus no second bundled triple-operator API is needed: `quadRepBilin a c`
is already the operator `b ↦ {a,b,c}`. -/
theorem jordanTriple_eq_quadRepBilin_apply (a b c : E) :
    jordanTriple a b c = quadRepBilin a c b := by
  rw [jordanTriple, quadRepBilin_apply]
  rw [mul_comm b c, mul_comm b a]

/-- The existing quadratic polarization is exactly twice the Jordan triple product. -/
theorem quadRepPolar_eq_two_smul_jordanTriple (a b c : E) :
    quadRepPolar a c b = (2 : ℝ) • jordanTriple a b c := by
  rw [quadRepPolar_apply, jordanTriple, mul_comm c b, mul_comm a b]

omit [Module ℝ E] [SMulCommClass ℝ E E] in
/-- The Jordan triple product is symmetric in its outer variables. -/
theorem jordanTriple_outer_comm (a b c : E) : jordanTriple a b c = jordanTriple c b a := by
  rw [jordanTriple, jordanTriple, mul_comm a c]
  abel

/-- The diagonal of the triple product is the quadratic representation. -/
theorem jordanTriple_diag (a b : E) : jordanTriple a b a = U a b := by
  rw [jordanTriple, quadRep_apply, mul_comm b a]
  simp only [jpow_two]
  module

omit [Module ℝ E] [SMulCommClass ℝ E E] in
/-- Additivity in the first outer variable. -/
theorem jordanTriple_add_left (a b c d : E) :
    jordanTriple (a + b) c d = jordanTriple a c d + jordanTriple b c d := by
  rw [jordanTriple, jordanTriple, jordanTriple]
  simp only [add_mul, mul_add]
  module

/-- Real linearity in the first outer variable. -/
theorem jordanTriple_smul_left (r : ℝ) (a b c : E) :
    jordanTriple (r • a) b c = r • jordanTriple a b c := by
  rw [jordanTriple, jordanTriple]
  have hsmul_mul (z y : E) : (r • z) * y = r • (z * y) := by
    calc
      (r • z) * y = y * (r • z) := mul_comm _ _
      _ = r • (y * z) := mul_smul_comm r y z
      _ = r • (z * y) := by rw [mul_comm y z]
  rw [hsmul_mul a (b * c), mul_comm b (r • a), hsmul_mul a b, mul_smul_comm,
    hsmul_mul a c, hsmul_mul (a * c) b, mul_comm a b]
  simp only [smul_add, smul_sub]

omit [Module ℝ E] [SMulCommClass ℝ E E] in
/-- Additivity in the third outer variable. -/
theorem jordanTriple_add_right (a b c d : E) :
    jordanTriple a b (c + d) = jordanTriple a b c + jordanTriple a b d := by
  rw [jordanTriple_outer_comm, jordanTriple_outer_comm a b c,
    jordanTriple_outer_comm a b d, jordanTriple_add_left]

/-- Real linearity in the third outer variable. -/
theorem jordanTriple_smul_right (r : ℝ) (a b c : E) :
    jordanTriple a b (r • c) = r • jordanTriple a b c := by
  calc
    jordanTriple a b (r • c) = jordanTriple (r • c) b a := jordanTriple_outer_comm _ _ _
    _ = r • jordanTriple c b a := jordanTriple_smul_left r c b a
    _ = r • jordanTriple a b c := by rw [jordanTriple_outer_comm]

omit [Module ℝ E] [SMulCommClass ℝ E E] in
/-- Additivity in the middle variable. -/
theorem jordanTriple_add_middle (a b c d : E) :
    jordanTriple a (b + c) d = jordanTriple a b d + jordanTriple a c d := by
  rw [jordanTriple, jordanTriple, jordanTriple]
  simp only [mul_add, add_mul]
  module

/-- Real linearity in the middle variable. -/
theorem jordanTriple_smul_middle (r : ℝ) (a b c : E) :
    jordanTriple a (r • b) c = r • jordanTriple a b c := by
  rw [jordanTriple, jordanTriple]
  have hsmul_mul (z y : E) : (r • z) * y = r • (z * y) := by
    calc
      (r • z) * y = y * (r • z) := mul_comm _ _
      _ = r • (y * z) := mul_smul_comm r y z
      _ = r • (z * y) := by rw [mul_comm y z]
  rw [hsmul_mul b c, mul_smul_comm, hsmul_mul b a, mul_smul_comm, mul_smul_comm]
  simp only [smul_add, smul_sub]

end JordanAlgebra
