/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.ComplexTensor.Basic
/-!

## Derivative of Real Lorentz tensors

-/
open Matrix
open TensorProduct
open TensorSpecies
namespace realLorentzTensor
open Tensor

/-- The map between coordinates given a map ` ℝT(d, cm) → ℝT(d, cn)`. -/
noncomputable def mapToBasis {d n m : ℕ} {cm : Fin m → realLorentzTensor.Color}
    {cn : Fin n → realLorentzTensor.Color} (f : ℝT(d, cm) → ℝT(d, cn)) :
    (ComponentIdx (S := realLorentzTensor d) cm → ℝ) →
    ComponentIdx (S := realLorentzTensor d) cn → ℝ :=
  Finsupp.equivFunOnFinite ∘ (basis cn).repr.toEquiv.toFun ∘
  f ∘ (basis cm).repr.symm.toEquiv.toFun
  ∘ Finsupp.equivFunOnFinite.symm

open ComponentIdx
/-- The derivative of a function `f : ℝT(d, cm) → ℝT(d, cn)`, giving a function
    `ℝT(d, cm) → ℝT(d, (Sum.elim cm cn) ∘ finSumFinEquiv.symm)`. -/
noncomputable def derivative {d n m : ℕ} {cm : Fin m → realLorentzTensor.Color}
    {cn : Fin n → realLorentzTensor.Color} (f : ℝT(d, cm) → ℝT(d, cn)) :
    ℝT(d, cm) → ℝT(d, (Fin.append (fun i => (realLorentzTensor d).τ (cm i)) cn)) := fun y =>
      (Tensor.basis _).repr.toEquiv.symm <|
      Finsupp.equivFunOnFinite.symm <| fun b =>
  /- The `b` component of the derivative of `f` evaluated at `y` is: -/
  /- The derivative of `mapToBasis f` -/
  fderiv ℝ (mapToBasis f)
  /- evaluated at the point `y` in `ℝT(d, cm)` -/
    (Finsupp.equivFunOnFinite ((basis cm).repr y))
  /- In the direction of `(splitEquiv b).1` -/
    (Finsupp.single (fun i => Fin.cast (by simp) ((ComponentIdx.prodEquiv b).1 i)) (1 : ℝ))
  /- The `(splitEquiv b).2` component of that derivative. -/
    (ComponentIdx.prodEquiv b).2

@[inherit_doc realLorentzTensor.derivative]
scoped[realLorentzTensor] notation "∂" => realLorentzTensor.derivative

lemma derivative_repr {d n m : ℕ} {cm : Fin m → realLorentzTensor.Color}
    {cn : Fin n → realLorentzTensor.Color} (f : ℝT(d, cm) → ℝT(d, cn))
    (y : ℝT(d, cm))
    (b : (j : Fin (m + n)) → Fin ((realLorentzTensor d).repDim
      (Fin.append (fun i => (realLorentzTensor d).τ (cm i)) cn j)))
    (h1 : DifferentiableAt ℝ (mapToBasis f)
      (Finsupp.equivFunOnFinite ((basis cm).repr y))) :
    (Tensor.basis _).repr (∂ f y) b =
    fderiv ℝ (fun y => mapToBasis f y (ComponentIdx.prodEquiv b).2)
      ((basis cm).repr y)
      (Finsupp.single (fun i => Fin.cast (by simp) ((ComponentIdx.prodEquiv b).1 i)) (1 : ℝ)) := by
  simp [derivative]
  rw [fderiv_pi]
  · simp
    rfl
  · rw [← differentiableAt_pi]
    exact h1

TODO "6V2CQ" "Prove that the derivative obeys the following equivariant
  property with respect to the Lorentz group.
  For a function `f : ℝT(d, cm) → ℝT(d, cn)` then
  `Λ • (∂ f (x)) = ∂ (fun x => Λ • f (Λ⁻¹ • x)) (Λ • x)`."

end realLorentzTensor
