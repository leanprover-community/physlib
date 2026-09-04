module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public meta import Lean.Elab.Command

@[expose] public section

open NNReal
open Lean Elab Command

/-- Common representation API for unit types whose magnitude is a positive real. -/
class PositiveRealUnitCore (U : Type) where
  val : U → ℝ
  pos : ∀ x, 0 < val x
  ofVal : (r : ℝ) → 0 < r → U
  val_ofVal : ∀ r hr, val (ofVal r hr) = r
  ofVal_val : ∀ x, ofVal (val x) (pos x) = x

namespace PositiveRealUnitCore

variable {U : Type} [PositiveRealUnitCore U]

@[simp] lemma val_ne_zero (x : U) : val x ≠ 0 :=
  Ne.symm (ne_of_lt (pos x))

noncomputable def ratio (x y : U) : NNReal :=
  ⟨val x / val y, div_nonneg (pos x).le (pos y).le⟩

lemma ratio_pos (x y : U) : 0 < ratio x y := by
  apply NNReal.coe_pos.mp
  change 0 < val x / val y
  exact div_pos (pos x) (pos y)

@[simp] lemma ratio_ne_zero (x y : U) : ratio x y ≠ 0 :=
  ne_of_gt (ratio_pos x y)

@[simp] lemma ratio_self (x : U) : ratio x x = 1 := by
  apply NNReal.eq
  change val x / val x = 1
  exact div_self (val_ne_zero x)

lemma ratio_symm (x y : U) : ratio x y = (ratio y x)⁻¹ := by
  apply NNReal.eq
  change val x / val y = (val y / val x)⁻¹
  rw [inv_div]

lemma ratio_mul_ratio (x y z : U) :
    ratio x y * ratio y z = ratio x z := by
  apply NNReal.eq
  change val x / val y * (val y / val z) = val x / val z
  rw [div_mul_div_comm, mul_comm (val x) (val y),
    mul_div_mul_left _ _ (val_ne_zero y)]

@[simp] lemma ratio_mul_ratio_coe (x y z : U) :
    (ratio x y : ℝ) * (ratio y z : ℝ) = ratio x z := by
  change val x / val y * (val y / val z) = val x / val z
  field_simp [val_ne_zero]

def scale (r : ℝ) (x : U) (hr : 0 < r := by norm_num) : U :=
  ofVal (r * val x) (mul_pos hr (pos x))

@[simp] lemma scale_val (r : ℝ) (x : U) (hr : 0 < r) :
    val (scale r x hr) = r * val x :=
  val_ofVal _ _

theorem ext {x y : U} (h : val x = val y) : x = y := by
  rw [← ofVal_val x, ← ofVal_val y]
  congr

@[simp] lemma scale_ratio_self (x : U) (r : ℝ) (hr : 0 < r) :
    ratio (scale r x hr) x = (⟨r, le_of_lt hr⟩ : NNReal) := by
  apply NNReal.eq
  change val (scale r x hr) / val x = r
  rw [scale_val]
  field_simp [val_ne_zero]

@[simp] lemma self_ratio_scale (x : U) (r : ℝ) (hr : 0 < r) :
    ratio x (scale r x hr) =
      (⟨1 / r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : NNReal) := by
  apply NNReal.eq
  simp [ratio, scale, val_ofVal]
  field_simp [val_ne_zero, ne_of_gt hr]

@[simp] lemma scale_one (x : U) : scale 1 x = x := by
  apply ext
  simp

@[simp] lemma scale_ratio_scale
    (x1 x2 : U) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    ratio (scale r1 x1 hr1) (scale r2 x2 hr2) =
      (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * ratio x1 x2 := by
  apply NNReal.eq
  change val (scale r1 x1 hr1) / val (scale r2 x2 hr2) =
    (r1 / r2) * (val x1 / val x2)
  rw [scale_val, scale_val]
  rw [div_mul_div_comm]

@[simp] lemma scale_scale
    (x : U) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 =
      scale (r1 * r2) x (mul_pos hr1 hr2) := by
  apply ext
  simp
  ring

end PositiveRealUnitCore

syntax (name := derivePositiveRealUnit)
  "derive_positive_real_unit " ident : command

@[command_elab derivePositiveRealUnit]
meta def elabDerivePositiveRealUnit : CommandElab := fun stx =>
  match stx with
  | `(derive_positive_real_unit $name:ident) => do
    let base := name.getId
    let q (n : Name) := mkIdentFrom name (base ++ n) (canonical := true)
    let valProj := q `val
    let propertyProj := q `property
    let valNeZero := q `val_ne_zero
    let valPos := q `val_pos
    let divEqVal := q `div_eq_val
    let divNeZero := q `div_ne_zero
    let divPos := q `div_pos
    let divSelf := q `div_self
    let divSymm := q `div_symm
    let divMulDiv := q `div_mul_div
    let divMulDivCoe := q `div_mul_div_coe
    let scale := q `scale
    let scaleDivSelf := q `scale_div_self
    let selfDivScale := q `self_div_scale
    let scaleOne := q `scale_one
    let scaleDivScale := q `scale_div_scale
    let scaleScale := q `scale_scale

    elabCommand (← `(command|
      instance : PositiveRealUnitCore $name where
        val := $valProj
        pos := $propertyProj
        ofVal := fun r hr => ⟨r, hr⟩
        val_ofVal := by intros; rfl
        ofVal_val := by intro x; cases x; rfl))

    elabCommand (← `(command|
      instance : Inhabited $name where default := ⟨1, by norm_num⟩))

    elabCommand (← `(command|
      noncomputable instance : HDiv $name $name NNReal where
        hDiv x y := PositiveRealUnitCore.ratio x y))

    elabCommand (← `(command|
      @[simp] lemma $valNeZero (x : $name) : x.val ≠ 0 := by
        change PositiveRealUnitCore.val x ≠ 0
        exact PositiveRealUnitCore.val_ne_zero x))

    elabCommand (← `(command|
      lemma $valPos (x : $name) : 0 < x.val := x.property))

    elabCommand (← `(command|
      lemma $divEqVal (x y : $name) :
          x / y = (⟨x.val / y.val,
            div_nonneg x.property.le y.property.le⟩ : NNReal) := rfl))

    elabCommand (← `(command|
      @[simp] lemma $divNeZero (x y : $name) :
          ¬ x / y = (0 : NNReal) := by
        change PositiveRealUnitCore.ratio x y ≠ 0
        exact PositiveRealUnitCore.ratio_ne_zero x y))

    elabCommand (← `(command|
      @[simp] lemma $divPos (x y : $name) :
          (0 : NNReal) < x / y := by
        change 0 < PositiveRealUnitCore.ratio x y
        exact PositiveRealUnitCore.ratio_pos x y))

    elabCommand (← `(command|
      @[simp] lemma $divSelf (x : $name) :
          x / x = (1 : NNReal) := by
        change PositiveRealUnitCore.ratio x x = 1
        exact PositiveRealUnitCore.ratio_self x))

    elabCommand (← `(command|
      lemma $divSymm (x y : $name) :
          x / y = (y / x)⁻¹ := by
        change PositiveRealUnitCore.ratio x y =
          (PositiveRealUnitCore.ratio y x)⁻¹
        exact PositiveRealUnitCore.ratio_symm x y))

    elabCommand (← `(command|
      lemma $divMulDiv (x y z : $name) :
          (x / y) * (y / z) = x / z := by
        change PositiveRealUnitCore.ratio x y *
          PositiveRealUnitCore.ratio y z =
          PositiveRealUnitCore.ratio x z
        exact PositiveRealUnitCore.ratio_mul_ratio x y z))

    elabCommand (← `(command|
      @[simp] lemma $divMulDivCoe (x y z : $name) :
          (x / y : ℝ) * (y / z : ℝ) = x / z := by
        change (PositiveRealUnitCore.ratio x y : ℝ) *
          (PositiveRealUnitCore.ratio y z : ℝ) =
          PositiveRealUnitCore.ratio x z
        exact PositiveRealUnitCore.ratio_mul_ratio_coe x y z))

    elabCommand (← `(command|
      def $scale (r : ℝ) (x : $name)
          (hr : 0 < r := by norm_num) : $name :=
        PositiveRealUnitCore.scale r x hr))

    elabCommand (← `(command|
      @[simp] lemma $scaleDivSelf (x : $name) (r : ℝ) (hr : 0 < r) :
          $scale r x hr / x = (⟨r, le_of_lt hr⟩ : NNReal) := by
        change PositiveRealUnitCore.ratio
          (PositiveRealUnitCore.scale r x hr) x =
          (⟨r, le_of_lt hr⟩ : NNReal)
        exact PositiveRealUnitCore.scale_ratio_self x r hr))

    elabCommand (← `(command|
      @[simp] lemma $selfDivScale (x : $name) (r : ℝ) (hr : 0 < r) :
          x / $scale r x hr =
            (⟨1 / r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : NNReal) := by
        change PositiveRealUnitCore.ratio x
          (PositiveRealUnitCore.scale r x hr) =
          (⟨1 / r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : NNReal)
        exact PositiveRealUnitCore.self_ratio_scale x r hr))

    elabCommand (← `(command|
      @[simp] lemma $scaleOne (x : $name) : $scale 1 x = x := by
        change PositiveRealUnitCore.scale 1 x = x
        exact PositiveRealUnitCore.scale_one x))

    elabCommand (← `(command|
      @[simp] lemma $scaleDivScale
          (x1 x2 : $name) {r1 r2 : ℝ}
          (hr1 : 0 < r1) (hr2 : 0 < r2) :
          $scale r1 x1 hr1 / $scale r2 x2 hr2 =
            (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
        change PositiveRealUnitCore.ratio
          (PositiveRealUnitCore.scale r1 x1 hr1)
          (PositiveRealUnitCore.scale r2 x2 hr2) =
          (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) *
            PositiveRealUnitCore.ratio x1 x2
        exact PositiveRealUnitCore.scale_ratio_scale x1 x2 hr1 hr2))

    elabCommand (← `(command|
      @[simp] lemma $scaleScale
          (x : $name) (r1 r2 : ℝ)
          (hr1 : 0 < r1) (hr2 : 0 < r2) :
          $scale r1 ($scale r2 x hr2) hr1 =
            $scale (r1 * r2) x (mul_pos hr1 hr2) := by
        change PositiveRealUnitCore.scale r1
          (PositiveRealUnitCore.scale r2 x hr2) hr1 =
          PositiveRealUnitCore.scale (r1 * r2) x (mul_pos hr1 hr2)
        exact PositiveRealUnitCore.scale_scale x r1 r2 hr1 hr2))
  | _ => throwError "invalid derive_positive_real_unit command"
