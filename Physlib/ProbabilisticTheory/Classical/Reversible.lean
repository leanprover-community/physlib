/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Classical.PureState
public import Physlib.ProbabilisticTheory.Classical.NormalChannel
public import Physlib.ProbabilisticTheory.State.Symmetry
public import Physlib.Mathematics.ForMathlib.MeasurableEquiv

/-!
# Reversible classical dynamics

The reversible transformations of a classical system are the measurable bijections of its
configuration space.

## i. Overview

The Koopman channel of a measurable bijection `φ` with measurable inverse turns each observable
`f` into `f ∘ φ`. The Koopman channel of the inverse undoes it, so it is a reversible
transformation of the observables.

Conversely a reversible transformation `T` is normal and maps pure states to pure states.
The Dirac state at `x` is therefore carried to a pure normal state `f ↦ T f x`. On a standard
Borel configuration space this is again a Dirac state, at a configuration `φ x`. Every
reversible transformation is the Koopman channel of the measurable bijection `φ`. Genuinely
stochastic dynamics cannot be undone by another channel.

For a single configuration space this identifies the group of reversible transformations with
the group of measurable automorphisms. A real one-parameter group of reversible classical
channels is therefore the same as a measurable flow `ℝ → (X ≃ᵐ X)` with the group law. No
Hamiltonian, invariant measure or continuity in time is assumed. Continuity is extra structure,
and the supremum norm is too strong for it. A Koopman channel sends every indicator to an indicator,
so a group continuous in the supremum norm fixes every event and is trivial.

## ii. Key results

- `ProbabilisticTheory.Classical.ofMeasurableEquiv` : the reversible transformation of a
  measurable bijection.
- `ProbabilisticTheory.Classical.reversibleEquiv` : reversible transformations are measurable
  bijections.
- `ProbabilisticTheory.Classical.automorphismMulEquiv` : the symmetry group of a classical system
  is the group of measurable automorphisms of its configuration space.

## iii. Table of contents

- A. Reversible transformations of measurable bijections
- B. The motion of configurations under a reversible transformation
- C. Reversible transformations are measurable bijections

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory.Classical

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ## A. Reversible transformations of measurable bijections -/

/-- The reversible transformation of a measurable bijection `φ` turns `f` into `f ∘ φ`. -/
noncomputable def ofMeasurableEquiv (φ : Y ≃ᵐ X) : Reversible (measurable X) (measurable Y) where
  toLinearMap := (koopman φ φ.measurable).toLinearMap
  invFun := koopman φ.symm φ.symm.measurable
  left_inv f := DFunLike.coe_injective (funext fun x ↦ congrArg f (φ.apply_symm_apply x))
  right_inv f := DFunLike.coe_injective (funext fun x ↦ congrArg f (φ.symm_apply_apply x))
  map_le_map_iff' {f g} := ⟨fun h ↦ le_def.mpr fun x ↦ by
    have := le_def.mp h (φ.symm x)
    change f (φ (φ.symm x)) ≤ g (φ (φ.symm x)) at this
    rwa [φ.apply_symm_apply] at this, fun h ↦ (koopman φ φ.measurable).monotone' h⟩
  map_one' := DFunLike.coe_injective rfl

@[simp]
lemma coe_ofMeasurableEquiv (φ : Y ≃ᵐ X) (f : Observables (measurable X)) :
    ⇑(ofMeasurableEquiv φ f) = f ∘ φ := rfl

/-! ## B. The motion of configurations under a reversible transformation -/

variable [StandardBorelSpace X] (T : Reversible (measurable X) (measurable Y))

/-- The motion of configurations under a reversible transformation `T`: it sends `x` to the
configuration whose Dirac state is the pure normal state `f ↦ T f x`. -/
noncomputable def motion (x : Y) : X :=
  configurationEquiv.symm ⟨(dirac _ x).comap T.toChannel,
    T.isNormal_toChannel.comp (isNormal_dirac x), (isPure_dirac x).comap T⟩

lemma dirac_motion (x : Y) :
    dirac _ (motion T x) = (dirac _ x).comap T.toChannel :=
  congrArg Subtype.val (configurationEquiv.apply_symm_apply _)

/-- A reversible transformation evaluates each observable along its motion of configurations. -/
lemma apply_apply (f : Observables (measurable X)) (x : Y) : T f x = f (motion T x) :=
  (DFunLike.congr_fun (dirac_motion T x) f).symm

/-- The motion of configurations is measurable. -/
lemma measurable_motion : Measurable (motion T) := fun s hs ↦ by
  convert measurable_coe (T (indicator ⟨s, hs⟩)) (measurableSet_singleton 1)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [apply_apply, coe_indicator]
  by_cases hx : motion T x ∈ s <;> simp [hx]

/-- The inverse transformation reverses the motion of configurations. -/
lemma motion_motion_symm [StandardBorelSpace Y] (x : X) : motion T (motion T.symm x) = x :=
  dirac_injective <| Channel.ext fun f ↦ by
    rw [dirac_apply, dirac_apply, ← apply_apply, ← apply_apply,
      Reversible.symm_apply_apply]

/-! ## C. Reversible transformations are measurable bijections -/

variable [StandardBorelSpace Y]

/-- The measurable bijection of configurations of a reversible transformation. -/
noncomputable def toMeasurableEquiv : Y ≃ᵐ X where
  toFun := motion T
  invFun := motion T.symm
  left_inv x := by simpa using motion_motion_symm T.symm x
  right_inv := motion_motion_symm T
  measurable_toFun := measurable_motion T
  measurable_invFun := measurable_motion T.symm

omit [StandardBorelSpace Y] in
/-- The motion of configurations under the Koopman transformation of `φ` is `φ`. -/
lemma motion_ofMeasurableEquiv (φ : Y ≃ᵐ X) : motion (ofMeasurableEquiv φ) = φ :=
  funext fun x ↦ dirac_injective <| Channel.ext fun f ↦ by
    rw [dirac_apply, dirac_apply, ← apply_apply, coe_ofMeasurableEquiv,
      Function.comp_apply]

/-- The reversible transformations between classical systems on standard Borel spaces are the
measurable bijections between their configuration spaces. -/
noncomputable def reversibleEquiv : Reversible (measurable X) (measurable Y) ≃ (Y ≃ᵐ X) where
  toFun T := toMeasurableEquiv T
  invFun φ := ofMeasurableEquiv φ
  left_inv T := Reversible.ext fun f ↦ DFunLike.coe_injective <| funext fun x ↦
    (apply_apply T f x).symm
  right_inv φ := MeasurableEquiv.ext (motion_ofMeasurableEquiv φ)

/-- The symmetry group of a classical system on a standard Borel space is the group of measurable
automorphisms of its configuration space. The automorphism `φ` moves configurations along `φ`, so
it turns an observable `f` into `f ∘ φ⁻¹`. -/
noncomputable def automorphismMulEquiv : (X ≃ᵐ X) ≃* Reversible (measurable X) (measurable X) where
  toFun φ := ofMeasurableEquiv φ.symm
  invFun T := (toMeasurableEquiv T).symm
  left_inv φ :=
    (congrArg MeasurableEquiv.symm (reversibleEquiv.right_inv φ.symm)).trans φ.symm_symm
  right_inv T := (congrArg ofMeasurableEquiv (toMeasurableEquiv T).symm_symm).trans
    (reversibleEquiv.left_inv T)
  map_mul' _ _ := Reversible.ext fun _ ↦ DFunLike.coe_injective rfl

end ProbabilisticTheory.Classical
