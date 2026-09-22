/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license and described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.FreeNonUnitalNonAssocAlgebra
public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Hom

/-!
# The free unital real Jordan algebra on two generators

The construction follows Mathlib's free-Lie-algebra pattern: start with the free non-unital,
non-associative real algebra on a formal unit and two letters, then quotient by precisely the
relations for a unital commutative Jordan algebra.  This is the abstract source of the canonical
map to `FreeSpecialJordanTwo`; it must not be confused with the latter special target.
-/

@[expose] public section

namespace JordanAlgebra

noncomputable section

local notation "RawTwo" => FreeNonUnitalNonAssocAlgebra ℝ (Option (Fin 2))

/-- The congruence-generating relations for the free unital real Jordan algebra on two letters. -/
inductive FreeJordanTwoRel : RawTwo → RawTwo → Prop
  | comm (a b : RawTwo) : FreeJordanTwoRel (a * b) (b * a)
  | jordan (a b : RawTwo) :
      FreeJordanTwoRel (a * b * (a * a)) (a * (b * (a * a)))
  | one_left (a : RawTwo) :
      FreeJordanTwoRel (FreeNonUnitalNonAssocAlgebra.of ℝ none * a) a
  | one_right (a : RawTwo) :
      FreeJordanTwoRel (a * FreeNonUnitalNonAssocAlgebra.of ℝ none) a
  | smul (r : ℝ) {a b : RawTwo} : FreeJordanTwoRel a b → FreeJordanTwoRel (r • a) (r • b)
  | add_right (c : RawTwo) {a b : RawTwo} :
      FreeJordanTwoRel a b → FreeJordanTwoRel (a + c) (b + c)
  | mul_left (c : RawTwo) {a b : RawTwo} :
      FreeJordanTwoRel a b → FreeJordanTwoRel (c * a) (c * b)
  | mul_right (c : RawTwo) {a b : RawTwo} :
      FreeJordanTwoRel a b → FreeJordanTwoRel (a * c) (b * c)

namespace FreeJordanTwoRel

theorem add_left (a : RawTwo) {b c : RawTwo} (h : FreeJordanTwoRel b c) :
    FreeJordanTwoRel (a + b) (a + c) := by
  rw [add_comm a b, add_comm a c]
  exact h.add_right a

theorem neg {a b : RawTwo} (h : FreeJordanTwoRel a b) : FreeJordanTwoRel (-a) (-b) := by
  simpa only [neg_one_smul] using h.smul (-1)

theorem sub_left (a : RawTwo) {b c : RawTwo} (h : FreeJordanTwoRel b c) :
    FreeJordanTwoRel (a - b) (a - c) := by
  simpa only [sub_eq_add_neg] using h.neg.add_left a

theorem sub_right (c : RawTwo) {a b : RawTwo} (h : FreeJordanTwoRel a b) :
    FreeJordanTwoRel (a - c) (b - c) := by
  simpa only [sub_eq_add_neg] using h.add_right (-c)

theorem nsmul (n : ℕ) {a b : RawTwo} (h : FreeJordanTwoRel a b) :
    FreeJordanTwoRel (n • a) (n • b) := by
  simpa only [← Nat.cast_smul_eq_nsmul ℝ] using h.smul (n : ℝ)

theorem zsmul (n : ℤ) {a b : RawTwo} (h : FreeJordanTwoRel a b) :
    FreeJordanTwoRel (n • a) (n • b) := by
  simpa only [← Int.cast_smul_eq_zsmul ℝ] using h.smul (n : ℝ)

end FreeJordanTwoRel

/-- The free unital real Jordan algebra on two generators. -/
def FreeJordanTwo : Type := Quot FreeJordanTwoRel

namespace FreeJordanTwo

instance : Zero FreeJordanTwo where zero := Quot.mk _ 0

instance : One FreeJordanTwo where one := Quot.mk _ (FreeNonUnitalNonAssocAlgebra.of ℝ none)

instance : Add FreeJordanTwo where
  add := Quot.map₂ (· + ·) (fun _ _ _ => FreeJordanTwoRel.add_left _) fun _ _ _ =>
    FreeJordanTwoRel.add_right _

instance : Neg FreeJordanTwo where neg := Quot.map Neg.neg fun _ _ => FreeJordanTwoRel.neg

instance : Sub FreeJordanTwo where
  sub := Quot.map₂ Sub.sub (fun _ _ _ => FreeJordanTwoRel.sub_left _) fun _ _ _ =>
    FreeJordanTwoRel.sub_right _

instance : Mul FreeJordanTwo where
  mul := Quot.map₂ (· * ·) (fun _ _ _ => FreeJordanTwoRel.mul_left _) fun _ _ _ =>
    FreeJordanTwoRel.mul_right _

instance : SMul ℕ FreeJordanTwo where
  smul n := Quot.map (n • ·) fun _ _ h => FreeJordanTwoRel.nsmul n h

instance : SMul ℤ FreeJordanTwo where
  smul n := Quot.map (n • ·) fun _ _ h => FreeJordanTwoRel.zsmul n h

instance : SMul ℝ FreeJordanTwo where
  smul r := Quot.map (r • ·) fun _ _ h => h.smul r

instance : AddCommGroup FreeJordanTwo :=
  Function.Surjective.addCommGroup (Quot.mk _) Quot.mk_surjective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance : Module ℝ FreeJordanTwo :=
  Function.Surjective.module ℝ ⟨⟨Quot.mk _, rfl⟩, fun _ _ => rfl⟩ Quot.mk_surjective
    (fun _ _ => rfl)

instance : NonAssocCommRing FreeJordanTwo where
  __ := (inferInstance : AddCommGroup FreeJordanTwo)
  mul := (· * ·)
  one := 1
  mul_comm x y := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    exact Quot.sound (FreeJordanTwoRel.comm x y)
  one_mul x := by
    rcases x with ⟨x⟩
    exact Quot.sound (FreeJordanTwoRel.one_left x)
  mul_one x := by
    rcases x with ⟨x⟩
    exact Quot.sound (FreeJordanTwoRel.one_right x)
  left_distrib x y z := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases z with ⟨z⟩
    change Quot.mk _ (x * (y + z)) = Quot.mk _ (x * y + x * z)
    exact congrArg (Quot.mk _) (mul_add x y z)
  right_distrib x y z := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    rcases z with ⟨z⟩
    change Quot.mk _ ((x + y) * z) = Quot.mk _ (x * z + y * z)
    exact congrArg (Quot.mk _) (add_mul x y z)
  zero_mul x := by
    rcases x with ⟨x⟩
    change Quot.mk _ (0 * x) = Quot.mk _ 0
    exact congrArg (Quot.mk _) (zero_mul x)
  mul_zero x := by
    rcases x with ⟨x⟩
    change Quot.mk _ (x * 0) = Quot.mk _ 0
    exact congrArg (Quot.mk _) (mul_zero x)

instance : IsCommJordan FreeJordanTwo where
  lmul_comm_rmul_rmul x y := by
    rcases x with ⟨x⟩
    rcases y with ⟨y⟩
    change Quot.mk _ (x * y * (x * x)) = Quot.mk _ (x * (y * (x * x)))
    exact Quot.sound (FreeJordanTwoRel.jordan x y)

/-- The first free abstract Jordan generator. -/
def x : FreeJordanTwo := Quot.mk _ (FreeNonUnitalNonAssocAlgebra.of ℝ (some 0))

/-- The second free abstract Jordan generator. -/
def y : FreeJordanTwo := Quot.mk _ (FreeNonUnitalNonAssocAlgebra.of ℝ (some 1))

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E]
  [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] [IsCommJordan E]

/-- Raw evaluation of formal unit-and-two-letter expressions in a unital real Jordan algebra. -/
def liftAux (f : Fin 2 → E) : RawTwo →ₙₐ[ℝ] E :=
  FreeNonUnitalNonAssocAlgebra.lift ℝ (fun o => Option.elim o 1 f)

omit [IsCommJordan E] in
theorem liftAux_map_smul (f : Fin 2 → E) (r : ℝ) (a : RawTwo) :
    liftAux f (r • a) = r • liftAux f a :=
  map_smul _ r a

omit [IsCommJordan E] in
theorem liftAux_map_add (f : Fin 2 → E) (a b : RawTwo) :
    liftAux f (a + b) = liftAux f a + liftAux f b :=
  map_add _ a b

omit [IsCommJordan E] in
theorem liftAux_map_mul (f : Fin 2 → E) (a b : RawTwo) :
    liftAux f (a * b) = liftAux f a * liftAux f b :=
  map_mul _ a b

omit [IsCommJordan E] in
theorem liftAux_of_none (f : Fin 2 → E) :
    liftAux f (FreeNonUnitalNonAssocAlgebra.of ℝ none) = 1 := by
  simp [liftAux]

theorem liftAux_spec (f : Fin 2 → E) (a b : RawTwo) (h : FreeJordanTwoRel a b) :
    liftAux f a = liftAux f b := by
  induction h with
  | comm a b => simp only [liftAux_map_mul, mul_comm]
  | jordan a b =>
    simp only [liftAux_map_mul, IsCommJordan.lmul_comm_rmul_rmul]
  | one_left a =>
    rw [liftAux_map_mul]
    rw [liftAux_of_none, one_mul]
  | one_right a =>
    rw [liftAux_map_mul]
    rw [liftAux_of_none, mul_one]
  | smul r h ih => simp only [liftAux_map_smul, ih]
  | add_right c h ih => simp only [liftAux_map_add, ih]
  | mul_left c h ih => simp only [liftAux_map_mul, ih]
  | mul_right c h ih => simp only [liftAux_map_mul, ih]

/-- The canonical unital Jordan homomorphism evaluating the two free generators at `f`. -/
def lift (f : Fin 2 → E) : JordanHom FreeJordanTwo E where
  toLinearMap :=
    { toFun := fun q => Quot.liftOn q (liftAux f) (liftAux_spec f)
      map_add' := by
        rintro ⟨a⟩ ⟨b⟩
        exact liftAux_map_add f a b
      map_smul' := by
        rintro r ⟨a⟩
        exact liftAux_map_smul f r a }
  map_one' := by
    change liftAux f (FreeNonUnitalNonAssocAlgebra.of ℝ none) = 1
    simp [liftAux]
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    exact liftAux_map_mul f a b

@[simp]
theorem lift_x (f : Fin 2 → E) : lift f x = f 0 := by
  change liftAux f (FreeNonUnitalNonAssocAlgebra.of ℝ (some 0)) = f 0
  simp [liftAux]

@[simp]
theorem lift_y (f : Fin 2 → E) : lift f y = f 1 := by
  change liftAux f (FreeNonUnitalNonAssocAlgebra.of ℝ (some 1)) = f 1
  simp [liftAux]

end FreeJordanTwo

end

end JordanAlgebra
