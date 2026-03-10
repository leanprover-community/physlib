/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import PhysLean.StatisticalMechanics.BoltzmannConstant
public import PhysLean.Meta.TODO.Basic
/-!

# Temperature

In this module we define the type `Temperature`, corresponding to the temperature in a given
(but arbitrary) set of units which have absolute zero at zero.

This is the version of temperature most often used in undergraduate and
non-mathematical physics.

The choice of units can be made on a case-by-case basis, as long as they are done consistently.

-/

@[expose] public section
open NNReal

/-- The type `Temperature` represents the temperature in a given (but arbitrary) set of units
  (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals. -/
structure Temperature where
  /-- The nonnegative real value of the temperature. -/
  val : ℝ≥0

namespace Temperature
open Constants

/-- Coercion to `ℝ≥0`. -/
instance : Coe Temperature ℝ≥0 := ⟨fun T => T.val⟩

/-- The underlying real-number associated with the temperature. -/
noncomputable def toReal (T : Temperature) : ℝ := NNReal.toReal T.val

/-- Coercion to `ℝ`. -/
noncomputable instance : Coe Temperature ℝ := ⟨toReal⟩

/-- Topology on `Temperature` induced from `ℝ≥0`. -/
instance : TopologicalSpace Temperature :=
  TopologicalSpace.induced (fun T : Temperature => (T.val : ℝ≥0)) inferInstance

instance : Zero Temperature := ⟨⟨0⟩⟩

@[ext] lemma ext {T₁ T₂ : Temperature} (h : T₁.val = T₂.val) : T₁ = T₂ := by
  cases T₁; cases T₂; cases h; rfl

/-- The inverse temperature defined as `1/(kB * T)` in a given, but arbitrary set of units.
  This has dimensions equivalent to `Energy`. -/
noncomputable def β (T : Temperature) : ℝ≥0 :=
  ⟨1 / (kB * (T : ℝ)), by
    apply div_nonneg
    · exact zero_le_one
    · apply mul_nonneg
      · exact kB_nonneg
      · simp [toReal]⟩

/-- The temperature associated with a given inverse temperature `β`. -/
noncomputable def ofβ (β : ℝ≥0) : Temperature :=
  ⟨⟨1 / (kB * β), by
      apply div_nonneg
      · exact zero_le_one
      · apply mul_nonneg
        · exact kB_nonneg
        · exact β.2⟩⟩

lemma ofβ_eq : ofβ = fun β => ⟨⟨1 / (kB * β), by
    apply div_nonneg
    · exact zero_le_one
    · apply mul_nonneg
      · exact kB_nonneg
      · exact β.2⟩⟩ := by
  rfl

@[simp]
lemma β_ofβ (β' : ℝ≥0) : β (ofβ β') = β' := by
  ext
  simp [β, ofβ, toReal]
  field_simp [kB_ne_zero]

@[simp]
lemma ofβ_β (T : Temperature) : ofβ (β T) = T := by
  ext
  change ((1 : ℝ) / (kB * ((β T : ℝ)))) = (T : ℝ)
  have : (β T : ℝ) = (1 : ℝ) / (kB * (T : ℝ)) := rfl
  simpa [this] using
    show (1 / (kB * (1 / (kB * (T : ℝ))))) = (T : ℝ) from by
      field_simp [kB_ne_zero]

/-- Positivity of `β` from positivity of temperature. -/
lemma beta_pos (T : Temperature) (hT_pos : 0 < T.val) : 0 < (T.β : ℝ) := by
  unfold Temperature.β
  have h_prod : 0 < (kB : ℝ) * T.val := mul_pos kB_pos hT_pos
  simpa [Temperature.β] using inv_pos.mpr h_prod

/-! ### Regularity of `ofβ` -/

open Filter Topology

lemma ofβ_continuousOn : ContinuousOn (ofβ : ℝ≥0 → Temperature) (Set.Ioi 0) := by
  rw [ofβ_eq]
  refine continuousOn_of_forall_continuousAt ?_
  intro x hx
  have h1 : ContinuousAt (fun t : ℝ => 1 / (kB * t)) x.1 := by
    refine ContinuousAt.div₀ ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · simp
      constructor
      · exact kB_ne_zero
      · exact ne_of_gt hx
  have hℝ : ContinuousAt (fun b : ℝ≥0 => (1 : ℝ) / (kB * (b : ℝ))) x :=
    h1.comp (continuous_subtype_val.continuousAt)
  have hNN :
      ContinuousAt (fun b : ℝ≥0 =>
          (⟨(1 : ℝ) / (kB * (b : ℝ)),
            by
              have hb : 0 ≤ kB * (b : ℝ) :=
                mul_nonneg kB_nonneg (by exact_mod_cast (show 0 ≤ b from b.2))
              exact div_nonneg zero_le_one hb⟩ : ℝ≥0)) x :=
    hℝ.codRestrict (fun b => by
      have hb : 0 ≤ kB * (b : ℝ) :=
        mul_nonneg kB_nonneg (by exact_mod_cast (show 0 ≤ b from b.2))
      exact div_nonneg zero_le_one hb)
  have hind : Topology.IsInducing (fun T : Temperature => (T.val : ℝ≥0)) := ⟨rfl⟩
  have : Tendsto (fun b : ℝ≥0 => ofβ b) (𝓝 x) (𝓝 (ofβ x)) := by
    simp [hind.nhds_eq_comap, ofβ_eq]
    simp_all only [Set.mem_Ioi, one_div, mul_inv_rev, val_eq_coe]
    exact hNN
  exact this

lemma ofβ_differentiableOn :
    DifferentiableOn ℝ (fun (x : ℝ) => ((ofβ (Real.toNNReal x)).val : ℝ)) (Set.Ioi 0) := by
  refine DifferentiableOn.congr (f := fun x => 1 / (kB * x)) ?_ ?_
  · refine DifferentiableOn.fun_div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (by simpa using hx)
      simp [mul_eq_zero, kB_ne_zero, hx0]
  · intro x hx
    simp at hx
    have hx' : 0 < x := by simpa using hx
    simp [ofβ_eq, hx'.le, Real.toNNReal, NNReal.coe_mk]

/-! ### Convergence -/

open Filter Topology

/-- Eventually, `ofβ β` is positive as β → ∞`. -/
lemma eventually_pos_ofβ : ∀ᶠ b : ℝ≥0 in atTop, ((Temperature.ofβ b : Temperature) : ℝ) > 0 := by
  have hge : ∀ᶠ b : ℝ≥0 in atTop, (1 : ℝ≥0) ≤ b := Filter.eventually_ge_atTop 1
  refine hge.mono ?_
  intro b hb
  have hbpos : 0 < (b : ℝ) := (zero_lt_one.trans_le hb)
  have hden : 0 < kB * (b : ℝ) := mul_pos kB_pos hbpos
  have : 0 < (1 : ℝ) / (kB * (b : ℝ)) := one_div_pos.mpr hden
  simpa [Temperature.ofβ, one_div, Temperature.toReal] using this

/-- General helper: for any `a > 0`, we have `1 / (a * b) → 0` as `b → ∞` in `ℝ≥0`. -/
private lemma tendsto_const_inv_mul_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun b : ℝ≥0 => (1 : ℝ) / (a * (b : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hεpos : 0 < ε := hε
  let Breal : ℝ := (1 / (a * ε)) + 1
  have hBpos : 0 < Breal := by
    have : 0 < (1 / (a * ε)) := by
      have : 0 < a * ε := mul_pos ha hεpos
      exact one_div_pos.mpr this
    linarith
  let B : ℝ≥0 := ⟨Breal, le_of_lt hBpos⟩
  have h_ev : ∀ᶠ b : ℝ≥0 in atTop, b ≥ B := Filter.eventually_ge_atTop B
  refine h_ev.mono ?_
  intro b hb
  have hBposR : 0 < (B : ℝ) := hBpos
  have hbposR : 0 < (b : ℝ) := by
    have hBB : (B : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    exact lt_of_lt_of_le hBposR hBB
  have hb0 : 0 < (a * (b : ℝ)) := mul_pos ha hbposR
  have hB0 : 0 < (a * (B : ℝ)) := mul_pos ha hBposR
  have hmono : (1 : ℝ) / (a * (b : ℝ)) ≤ (1 : ℝ) / (a * (B : ℝ)) := by
    have hBB : (B : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hden_le : (a * (B : ℝ)) ≤ (a * (b : ℝ)) :=
      mul_le_mul_of_nonneg_left hBB (le_of_lt ha)
    simpa [one_div] using one_div_le_one_div_of_le hB0 hden_le
  have hB_gt_base : (1 / (a * ε)) < (B : ℝ) := by
    simp [B, Breal]
  have hden_gt : (1 / ε) < (a * (B : ℝ)) := by
    have h' := mul_lt_mul_of_pos_left hB_gt_base ha
    have hane : a ≠ 0 := ne_of_gt ha
    have hx' : a * (ε⁻¹ * a⁻¹) = (1 / ε) := by
      have : a * (ε⁻¹ * a⁻¹) = ε⁻¹ := by
        simp [mul_comm, hane]
      simpa [one_div] using this
    simpa [hx'] using h'
  have hpos : 0 < (1 / ε) := by simpa [one_div] using inv_pos.mpr hεpos
  have hBbound : (1 : ℝ) / (a * (B : ℝ)) < ε := by
    have := one_div_lt_one_div_of_lt hpos hden_gt
    simpa [one_div, inv_div] using this
  set A : ℝ := (1 : ℝ) / (a * (b : ℝ)) with hA
  have hA_nonneg : 0 ≤ A := by
    have : 0 ≤ a * (b : ℝ) :=
      mul_nonneg (le_of_lt ha) (by exact_mod_cast (show 0 ≤ b from b.2))
    simpa [hA] using div_nonneg zero_le_one this
  have hxlt : A < ε := by
    have := lt_of_le_of_lt hmono hBbound
    simpa [hA] using this
  have hAbs : |A| < ε := by
    simpa [abs_of_nonneg hA_nonneg] using hxlt
  have hAbs' : |A - 0| < ε := by simpa [sub_zero] using hAbs
  have hdist : dist A 0 < ε := by simpa [Real.dist_eq] using hAbs'
  simpa [Real.dist_eq, hA, one_div, mul_comm, mul_left_comm, mul_assoc] using hdist

/-- Core convergence: as β → ∞, `toReal (ofβ β) → 0` in `ℝ`. -/
lemma tendsto_toReal_ofβ_atTop :
    Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hform :
      (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
        = (fun b : ℝ≥0 => (1 : ℝ) / (kB * (b : ℝ))) := by
    funext b; simp [Temperature.ofβ, Temperature.toReal]
  have hsrc :
      Tendsto (fun b : ℝ≥0 => (1 : ℝ) / (kB * (b : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_inv_mul_atTop kB kB_pos
  simpa [hform] using hsrc

/-- As β → ∞, T = ofβ β → 0+ in ℝ (within Ioi 0). -/
lemma tendsto_ofβ_atTop :
    Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  have h_to0 := tendsto_toReal_ofβ_atTop
  have h_into :
      Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ)) atTop (𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_principal.2 (by simpa using Temperature.eventually_pos_ofβ)
  have : Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop ((nhds (0 : ℝ)) ⊓ 𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_inf.2 ⟨h_to0, h_into⟩
  simpa [nhdsWithin] using this

/-! ### Conversion to and from `ℝ≥0` -/

open Constants

/-- Build a `Temperature` directly from a nonnegative real. -/
@[simp] def ofNNReal (t : ℝ≥0) : Temperature := ⟨t⟩

@[simp]
lemma ofNNReal_val (t : ℝ≥0) : (ofNNReal t).val = t := rfl

@[simp]
lemma coe_ofNNReal_coe (t : ℝ≥0) : ((ofNNReal t : Temperature) : ℝ≥0) = t := rfl

@[simp]
lemma coe_ofNNReal_real (t : ℝ≥0) : ((⟨t⟩ : Temperature) : ℝ) = t := rfl

/-- Convenience: build a temperature from a real together with a proof of nonnegativity. -/
@[simp]
noncomputable def ofRealNonneg (t : ℝ) (ht : 0 ≤ t) : Temperature :=
  ofNNReal ⟨t, ht⟩

@[simp]
lemma ofRealNonneg_val {t : ℝ} (ht : 0 ≤ t) :
    (ofRealNonneg t ht).val = ⟨t, ht⟩ := rfl

/-! ### Calculus relating T and β -/

open Set
open scoped ENNReal

/-- Map a real `t` to the inverse temperature `β` corresponding to the temperature `Real.toNNReal t`
(`max t 0`), returned as a real number. -/
noncomputable def betaFromReal (t : ℝ) : ℝ :=
  ((Temperature.ofNNReal (Real.toNNReal t)).β : ℝ)

/-- Explicit closed-form for `Beta_fun_T t` when `t > 0`. -/
lemma beta_fun_T_formula (t : ℝ) (ht : 0 < t) :
    betaFromReal t = 1 / (kB * t) := by
  have ht0 : (0 : ℝ) ≤ t := ht.le
  have : ((Temperature.ofNNReal (Real.toNNReal t)).β : ℝ) = 1 / (kB * t) := by
    simp [Temperature.β, Temperature.ofNNReal, Temperature.toReal,
      Real.toNNReal_of_nonneg ht0, one_div, mul_comm]
  simpa [betaFromReal] using this

/-- On `Ioi 0`, `Beta_fun_T t` equals `1 / (kB * t)`. -/
lemma beta_fun_T_eq_on_Ioi :
    EqOn betaFromReal (fun t : ℝ => 1 / (kB * t)) (Set.Ioi 0) := by
  intro t ht
  exact beta_fun_T_formula t ht

lemma deriv_beta_wrt_T (T : Temperature) (hT_pos : 0 < T.val) :
    HasDerivWithinAt betaFromReal (-1 / (kB * (T.val : ℝ)^2)) (Set.Ioi 0) (T.val : ℝ) := by
  let f : ℝ → ℝ := fun t => 1 / (kB * t)
  have h_eq : EqOn betaFromReal f (Set.Ioi 0) := beta_fun_T_eq_on_Ioi
  have hTne : (T.val : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hf_def : f = fun t : ℝ => (kB)⁻¹ * t⁻¹ := by
    funext t
    by_cases ht : t = 0
    · simp [f, ht]
    · simp [f, one_div, *] at *
      ring
  have h_inv :
      HasDerivAt (fun t : ℝ => t⁻¹)
        (-((T.val : ℝ) ^ 2)⁻¹) (T.val : ℝ) := by
    simpa using (hasDerivAt_inv (x := (T.val : ℝ)) hTne)
  have h_deriv_aux :
      HasDerivAt (fun t : ℝ => (kB)⁻¹ * t⁻¹)
        ((kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹)) (T.val : ℝ) :=
    h_inv.const_mul ((kB)⁻¹)
  have h_pow_simp :
      (kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹) = -1 / (kB * (T.val : ℝ)^2) := by
    calc
      (kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹)
          = -((kB)⁻¹ * ((T.val : ℝ) ^ 2)⁻¹) := by
            ring
      _ = -(1 / kB * (1 / (T.val : ℝ) ^ 2)) := by
            simp [one_div]
      _ = -1 / (kB * (T.val : ℝ) ^ 2) := by
        rw [one_div]
        field_simp [pow_two, mul_comm, mul_left_comm, mul_assoc, kB_ne_zero, hTne]
  have h_deriv_f :
      HasDerivAt f (-1 / (kB * (T.val : ℝ)^2)) (T.val : ℝ) := by
    simpa [hf_def, h_pow_simp] using h_deriv_aux
  have h_mem : (T.val : ℝ) ∈ Set.Ioi (0 : ℝ) := hT_pos
  exact (h_deriv_f.hasDerivWithinAt).congr h_eq (h_eq h_mem)

/-- Chain rule for β(T) : d/dT F(β(T)) = F'(β(T)) * (-1 / (kB * T^2)), within `Ioi 0`. -/
lemma chain_rule_T_beta {F : ℝ → ℝ} {F' : ℝ}
    (T : Temperature) (hT_pos : 0 < T.val)
    (hF_deriv : HasDerivWithinAt F F' (Set.Ioi 0) (T.β : ℝ)) :
    HasDerivWithinAt (fun t : ℝ => F (betaFromReal t))
      (F' * (-1 / (kB * (T.val : ℝ)^2))) (Set.Ioi 0) (T.val : ℝ) := by
  have hβ_deriv := deriv_beta_wrt_T (T:=T) hT_pos
  have h_map : Set.MapsTo betaFromReal (Set.Ioi 0) (Set.Ioi 0) := by
    intro t ht
    have ht_pos : 0 < t := ht
    have : 0 < 1 / (kB * t) := by
      have : 0 < kB * t := mul_pos kB_pos ht_pos
      exact one_div_pos.mpr this
    have h_eqt : betaFromReal t = 1 / (kB * t) := beta_fun_T_eq_on_Ioi ht
    simpa [h_eqt] using this
  have h_beta_at_T : betaFromReal (T.val : ℝ) = (T.β : ℝ) := by
    have hTposR : 0 < (T.val : ℝ) := hT_pos
    have h_eqt := beta_fun_T_eq_on_Ioi hTposR
    simpa [Temperature.β, Temperature.toReal] using h_eqt
  have hF_deriv' : HasDerivWithinAt F F' (Set.Ioi 0) (betaFromReal (T.val : ℝ)) := by
    simpa [h_beta_at_T] using hF_deriv
  have h_comp := hF_deriv'.comp (T.val : ℝ) hβ_deriv h_map
  simpa [mul_comm] using h_comp

end Temperature
