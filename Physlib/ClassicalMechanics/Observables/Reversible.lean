/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ClassicalMechanics.Observables.PureState
public import Physlib.ClassicalMechanics.Observables.NormalChannel
public import Physlib.ProbabilisticTheory.State.Symmetry
public import Physlib.Mathematics.ForMathlib.MeasurableEquiv

/-!
# Reversible classical dynamics

The reversible transformations of a classical system are the measurable bijections of its
configuration space.

## i. Overview

A measurable map `φ : Ω' → Ω` of configurations turns each observable `f` on `Ω` into the
observable `f ∘ φ` on `Ω'`. This is the Koopman channel of `φ`. A Markov kernel describes
this channel when it moves every configuration `x` with certainty to `φ x`. A measurable bijection
with measurable inverse gives a reversible transformation of the observables.

Conversely a reversible transformation `T` is normal and maps pure states to pure states.
The Dirac state at `x` is therefore carried to a pure normal state `f ↦ T f x`. On a standard
Borel configuration space this is again a Dirac state, at a configuration `φ x`. Every
reversible transformation is the Koopman channel of the measurable bijection `φ`. Genuinely
stochastic dynamics cannot be undone by another channel.

For a single configuration space this identifies the group of reversible transformations with
the group of measurable automorphisms. A real one-parameter group of reversible classical
channels is therefore the same as a measurable flow `ℝ → (Ω ≃ᵐ Ω)` with the group law. No
Hamiltonian, invariant measure or continuity in time is assumed. Continuity is extra structure,
and the supremum norm is too strong for it. A Koopman channel sends every event indicator to an
event indicator, so a group continuous in the supremum norm fixes every event and is trivial.

## ii. Key results

- `ProbabilisticTheory.ClassicalReversible` : reversible transformations of classical systems.
- `ProbabilisticTheory.Classical.koopman` : the channel of a measurable map of configurations.
- `ProbabilisticTheory.Classical.ofMeasurableEquiv` : the reversible transformation of a
  measurable bijection.
- `ProbabilisticTheory.Classical.reversibleEquiv` : reversible transformations are measurable
  bijections.
- `ProbabilisticTheory.Classical.automorphismMulEquiv` : the symmetry group of a classical system
  is the group of measurable automorphisms of its configuration space.

## iii. Table of contents

- A. Koopman channels
- B. The map of configurations of a reversible transformation
- C. Reversible transformations are measurable bijections

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-- A reversible transformation from the bounded measurable observables on `Ω` to those
on `Ω'`. -/
abbrev ClassicalReversible (Ω Ω' : Type*) [MeasurableSpace Ω] [MeasurableSpace Ω'] :=
  Reversible (ofCStarAlgebra (Classical.measurableAlgebra Ω))
    (ofCStarAlgebra (Classical.measurableAlgebra Ω'))

namespace Classical

open MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ## A. Koopman channels -/

/-- The Koopman channel of a measurable map `φ` of configurations turns `f` into `f ∘ φ`. -/
noncomputable def koopman (φ : Ω' → Ω) (hφ : Measurable φ) : ClassicalChannel Ω Ω' :=
  .ofLinearMap
    { toFun f := ofFun (toFun f ∘ φ) ((measurable_toFun f).comp hφ)
        ⟨_, fun x ↦ abs_toFun_le_norm f (φ x)⟩
      map_add' _ _ := toFun_injective rfl
      map_smul' c f := toFun_injective <| by
        rw [toFun_ofFun, RingHom.id_apply, map_smul, map_smul, toFun_ofFun]; rfl }
    (fun _ hf ↦ toFun_le_toFun_iff.mp fun x ↦ toFun_le_toFun_iff.mpr hf (φ x))
    (toFun_injective rfl)

@[simp]
lemma toFun_koopman (φ : Ω' → Ω) (hφ : Measurable φ) (f : ClassicalObservable Ω) :
    toFun (koopman φ hφ f) = toFun f ∘ φ := rfl

/-- The reversible transformation of a measurable bijection `φ` turns `f` into `f ∘ φ`. -/
noncomputable def ofMeasurableEquiv (φ : Ω' ≃ᵐ Ω) : ClassicalReversible Ω Ω' where
  toLinearMap := (koopman φ φ.measurable).toLinearMap
  invFun := koopman φ.symm φ.symm.measurable
  left_inv f := toFun_injective (funext fun x ↦ congrArg (toFun f) (φ.apply_symm_apply x))
  right_inv f := toFun_injective (funext fun x ↦ congrArg (toFun f) (φ.symm_apply_apply x))
  map_le_map_iff' {f g} := ⟨fun h ↦ toFun_le_toFun_iff.mp fun x ↦ by
    have := toFun_le_toFun_iff.mpr h (φ.symm x)
    change toFun f (φ (φ.symm x)) ≤ toFun g (φ (φ.symm x)) at this
    rwa [φ.apply_symm_apply] at this, fun h ↦ (koopman φ φ.measurable).monotone' h⟩
  map_one' := toFun_injective rfl

@[simp]
lemma toFun_ofMeasurableEquiv (φ : Ω' ≃ᵐ Ω) (f : ClassicalObservable Ω) :
    toFun (ofMeasurableEquiv φ f) = toFun f ∘ φ := rfl

/-! ## B. The map of configurations of a reversible transformation -/

variable [StandardBorelSpace Ω] (T : ClassicalReversible Ω Ω')

/-- The map of configurations of a reversible transformation `T`: it sends `x` to the
configuration whose Dirac state is the pure normal state `f ↦ T f x`. -/
noncomputable def configMap (x : Ω') : Ω :=
  pureStateEquiv.symm ⟨(dirac x).comap T.toChannel,
    T.isNormal_toChannel.comp (isNormal_dirac x), (isPure_dirac x).comap T⟩

lemma dirac_configMap (x : Ω') : dirac (configMap T x) = (dirac x).comap T.toChannel :=
  congrArg Subtype.val (pureStateEquiv.apply_symm_apply _)

/-- A reversible transformation evaluates each observable along its map of configurations. -/
lemma toFun_reversible_apply (f : ClassicalObservable Ω) (x : Ω') :
    toFun (T f) x = toFun f (configMap T x) :=
  (DFunLike.congr_fun (dirac_configMap T x) f).symm

/-- The map of configurations is measurable. -/
lemma measurable_configMap : Measurable (configMap T) := fun s hs ↦ by
  convert measurable_toFun (T (indicator s hs)) (measurableSet_singleton 1)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [toFun_reversible_apply, toFun_indicator]
  by_cases hx : configMap T x ∈ s <;> simp [hx]

/-- The inverse transformation inverts the map of configurations. -/
lemma configMap_configMap_symm [StandardBorelSpace Ω'] (x : Ω) :
    configMap T (configMap T.symm x) = x :=
  dirac_injective <| Channel.ext fun f ↦ by
    rw [dirac_apply, dirac_apply, ← toFun_reversible_apply, ← toFun_reversible_apply,
      Reversible.symm_apply_apply]

/-! ## C. Reversible transformations are measurable bijections -/

variable [StandardBorelSpace Ω']

/-- The measurable bijection of configurations of a reversible transformation. -/
noncomputable def toMeasurableEquiv : Ω' ≃ᵐ Ω where
  toFun := configMap T
  invFun := configMap T.symm
  left_inv x := by simpa using configMap_configMap_symm T.symm x
  right_inv := configMap_configMap_symm T
  measurable_toFun := measurable_configMap T
  measurable_invFun := measurable_configMap T.symm

omit [StandardBorelSpace Ω'] in
/-- The map of configurations of the Koopman transformation of `φ` is `φ`. -/
lemma configMap_ofMeasurableEquiv (φ : Ω' ≃ᵐ Ω) : configMap (ofMeasurableEquiv φ) = φ :=
  funext fun x ↦ dirac_injective <| Channel.ext fun f ↦ by
    rw [dirac_apply, dirac_apply, ← toFun_reversible_apply, toFun_ofMeasurableEquiv,
      Function.comp_apply]

/-- The reversible transformations between classical systems on standard Borel spaces are the
measurable bijections between their configuration spaces. -/
noncomputable def reversibleEquiv : ClassicalReversible Ω Ω' ≃ (Ω' ≃ᵐ Ω) where
  toFun T := toMeasurableEquiv T
  invFun φ := ofMeasurableEquiv φ
  left_inv T := Reversible.ext fun f ↦ toFun_injective <| funext fun x ↦
    (toFun_reversible_apply T f x).symm
  right_inv φ := MeasurableEquiv.ext (configMap_ofMeasurableEquiv φ)

/-- The symmetry group of a classical system on a standard Borel space is the group of measurable
automorphisms of its configuration space. The automorphism `φ` moves configurations along `φ`, so
it turns an observable `f` into `f ∘ φ⁻¹`. -/
noncomputable def automorphismMulEquiv : (Ω ≃ᵐ Ω) ≃* ClassicalReversible Ω Ω where
  toFun φ := ofMeasurableEquiv φ.symm
  invFun T := (toMeasurableEquiv T).symm
  left_inv φ :=
    (congrArg MeasurableEquiv.symm (reversibleEquiv.right_inv φ.symm)).trans φ.symm_symm
  right_inv T := (congrArg ofMeasurableEquiv (toMeasurableEquiv T).symm_symm).trans
    (reversibleEquiv.left_inv T)
  map_mul' _ _ := Reversible.ext fun _ ↦ toFun_injective rfl

end Classical

end ProbabilisticTheory
