/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.LTMCTDimensionBase
public import Physlib.Units.ISQDimensionBase
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
/-!

# Bridging PhysLib's default basis and the ISQ basis

`LTMCTDimensionBase` (length, time, mass, charge, temperature) and `ISQDimensionBase`
(the seven ISO/IEC 80000-1 base quantities) make different base/derived choices. This
module relates them by the two truth-preserving directions of `Dimension.Embedding`
and `Dimension.Projection`:

* `ltmctToISQ : Dimension.Embedding LTMCTDimensionBase ISQDimensionBase` — the
  dimension-preserving **inclusion** of PhysLib dimensions into ISQ dimensions. It
  sends the charge generator to the *derived* ISQ charge `I · T` (`toISQHom_C𝓭`), so it
  is faithful (`toISQHom_injective`) and physically correct, not a bare relabelling.
* `isqToLTMCT : Dimension.Projection ISQDimensionBase LTMCTDimensionBase` — the
  truth-preserving **reduction** of ISQ dimensions onto PhysLib's. It reads electric
  current as charge/time and forgets amount of substance and luminous intensity (the
  base quantities PhysLib does not track).

The two fit together as a retraction, `isqToLTMCT ∘ ltmctToISQ = id`
(`isqToLTMCT_comp_ltmctToISQ`): PhysLib's basis embeds faithfully into ISQ and is
recovered exactly by the projection — but the reverse composite is *not* the identity,
because amount of substance and luminous intensity cannot be recovered once dropped.
That is the asymmetry: one can reduce ISQ to LTMCT, but not conjure the extra base
quantities back without *adding* them.

-/

@[expose] public section

namespace Dimension

/-- The function underlying `toISQHom`: fix length, mass, time and temperature, and
  send PhysLib's charge generator to the derived ISQ charge `I · T` (the current
  exponent is the charge exponent, and the time exponent absorbs it). -/
def toISQFun (d : Dimension LTMCTDimensionBase) : Dimension ISQDimensionBase :=
  ofFunction fun
    | .length => d.exponent .length
    | .mass => d.exponent .mass
    | .time => d.exponent .time + d.exponent .charge
    | .current => d.exponent .charge
    | .temperature => d.exponent .temperature
    | .amount => 0
    | .luminousIntensity => 0

/-- The dimension-preserving embedding of PhysLib dimensions into the ISQ dimensions. -/
def toISQHom : Dimension LTMCTDimensionBase →* Dimension ISQDimensionBase where
  toFun := toISQFun
  map_one' := by ext b; cases b <;> simp [toISQFun]
  map_mul' d1 d2 := by
    ext b
    cases b <;> simp only [toISQFun, ofFunction_exponent, mul_exponent]
    all_goals ring

/-- `toISQHom` applied to a dimension is `toISQFun`. -/
lemma toISQHom_apply (d : Dimension LTMCTDimensionBase) : toISQHom d = toISQFun d := rfl

/-- The function underlying `fromISQHom`: fix length, mass and temperature, read
  electric current as charge/time (the charge exponent is the current exponent, and the
  time exponent subtracts it), and drop amount of substance and luminous intensity. -/
def fromISQFun (d : Dimension ISQDimensionBase) : Dimension LTMCTDimensionBase :=
  ofFunction fun
    | .length => d.exponent .length
    | .time => d.exponent .time - d.exponent .current
    | .mass => d.exponent .mass
    | .charge => d.exponent .current
    | .temperature => d.exponent .temperature

/-- The truth-preserving reduction of ISQ dimensions onto PhysLib's. -/
def fromISQHom : Dimension ISQDimensionBase →* Dimension LTMCTDimensionBase where
  toFun := fromISQFun
  map_one' := by ext b; cases b <;> simp [fromISQFun]
  map_mul' d1 d2 := by
    ext b
    cases b <;> simp only [fromISQFun, ofFunction_exponent, mul_exponent]
    all_goals ring

/-- `fromISQHom` applied to a dimension is `fromISQFun`. -/
lemma fromISQHom_apply (d : Dimension ISQDimensionBase) : fromISQHom d = fromISQFun d := rfl

/-- The projection recovers PhysLib's basis from its image under the embedding:
  `fromISQHom ∘ toISQHom = id`. -/
lemma fromISQHom_comp_toISQHom :
    fromISQHom.comp toISQHom = MonoidHom.id (Dimension LTMCTDimensionBase) := by
  refine MonoidHom.ext fun d => Dimension.ext fun b => ?_
  cases b <;> simp only [MonoidHom.comp_apply, MonoidHom.id_apply, toISQHom_apply,
    fromISQHom_apply, fromISQFun, toISQFun, ofFunction_exponent]
  all_goals ring

/-- `toISQHom` is injective: PhysLib dimensions include faithfully into ISQ. -/
lemma toISQHom_injective : Function.Injective toISQHom := by
  intro d1 d2 h
  have key : ∀ b : ISQDimensionBase, (toISQFun d1).exponent b = (toISQFun d2).exponent b := by
    intro b
    have hb := congrArg (fun d => Dimension.exponent d b) h
    simpa only [toISQHom_apply] using hb
  ext b
  cases b with
  | length => simpa only [toISQFun, ofFunction_exponent] using key .length
  | time =>
      have ht := key .time
      have hc := key .current
      simp only [toISQFun, ofFunction_exponent] at ht hc
      linarith
  | mass => simpa only [toISQFun, ofFunction_exponent] using key .mass
  | charge => simpa only [toISQFun, ofFunction_exponent] using key .current
  | temperature => simpa only [toISQFun, ofFunction_exponent] using key .temperature

/-- `fromISQHom` is surjective: every PhysLib dimension is the reduction of some ISQ
  dimension (namely its own embedding). -/
lemma fromISQHom_surjective : Function.Surjective fromISQHom := fun y =>
  ⟨toISQHom y, by rw [← MonoidHom.comp_apply, fromISQHom_comp_toISQHom, MonoidHom.id_apply]⟩

/-- PhysLib's dimensions embed into the ISQ dimensions (charge ↦ `I · T`). -/
def ltmctToISQ : Embedding LTMCTDimensionBase ISQDimensionBase where
  toHom := toISQHom
  inj := toISQHom_injective

/-- The ISQ dimensions project onto PhysLib's, reading current as charge/time and
  forgetting amount of substance and luminous intensity. -/
def isqToLTMCT : Projection ISQDimensionBase LTMCTDimensionBase where
  toHom := fromISQHom
  surj := fromISQHom_surjective

/-- The projection is a retraction of the embedding: `isqToLTMCT ∘ ltmctToISQ = id`. So
  PhysLib's basis embeds faithfully into ISQ and is recovered by the projection, but not
  conversely — amount of substance and luminous intensity cannot be recovered. -/
lemma isqToLTMCT_comp_ltmctToISQ :
    isqToLTMCT.toHom.comp ltmctToISQ.toHom = MonoidHom.id (Dimension LTMCTDimensionBase) :=
  fromISQHom_comp_toISQHom

/-- The embedding is physically faithful on charge: PhysLib's charge generator `C𝓭`
  maps to the *derived* ISQ charge `I · T`. -/
lemma toISQHom_C𝓭 : toISQHom C𝓭 = ISQDimensionBase.charge := by
  ext b
  cases b <;> simp [toISQHom_apply, toISQFun, C𝓭, ISQDimensionBase.charge, single_exponent]

end Dimension
