/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# Polynomially-bounded Schwartz submodules

## i. Overview

In this module we define polynomially-bounded Schwartz submodules of `SpaceDHilbertSpace d μ`.

For each `a : ℕ∞`, `PolyBddSchwartzSubmodule d a μ` is the submodule corresponding to Schwartz
maps `f` satisfying the polynomial growth bounds `‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` for all `(k : ℕ) ≤ a`.
In particular, for `a = ⊤` such a bound holds for all natural numbers.

These serve as a natural domain for singular unbounded operators. For example, the `1/r` Coulomb
potential operator maps `PolyBddSchwartzSubmodule d ⊤ μ` to itself. In the same way that multiplying
a Schwartz map by any polynomial in the coordinates results in a square-integrable function,
polynomially-bounded Schwartz maps may be multiplied by Laurent polynomials and remain
square-integrable (the precise condition depends on `d`, `a` and the negative degree of
the Laurent polynomial).

Note: the condition defining polynomially-bounded Schwartz maps is phrased as
`‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` rather than as `‖f x‖ ≤ Cₖ * ‖x‖ ^ k` to mirror `SchwartzMap.decay`.
These two conditions only differ at `x = 0` and are therefore equivalent for `d > 0` since
then `f 0` may be determined by continuity. For `d = 0` the former does not constrain `f 0 = 0`
(since `x = 0` is the only point and `0⁻¹ = 0`) while the latter does (and would therefore spoil
their being dense in `SpaceDHilbertSpace 0 ≅ ℂ`).

For `d > 0` and `a ≠ 0` every polynomially-bounded Schwartz map vanishes at the origin. So when
the measure `μ` gives positive mass to the origin, the state concentrated at the origin is
orthogonal to `PolyBddSchwartzSubmodule d a μ`, and the submodule is not dense. For a measure `μ`
finite on compact sets this is the only obstruction. The submodule is then dense if and only if
`d = 0`, `a = 0` or `μ {0} = 0`, without the assumption `μ ≤ volume` of
`PolyBddSchwartzSubmodule.dense`.

## ii. Key results

- `PolyBddSchwartzSubmodule d (a : ℕ∞) μ`: Restriction of `SchwartzSubmodule d μ` to those
  Schwartz maps which are bounded by powers of `‖x‖`.
- `PolyBddSchwartzSubmodule.dense`: These submodules are dense in `SpaceDHilbertSpace d μ` when
  `μ ≤ volume`.
- `PolyBddSchwartzSubmodule.dense_of_measure_singleton_zero_eq_zero`: These submodules are dense
  in `SpaceDHilbertSpace d μ` when `μ` is finite on compact sets and `μ {0} = 0`.
- `PolyBddSchwartzSubmodule.dense_iff`: For `μ` finite on compact sets, these submodules are
  dense if and only if `d = 0`, `a = 0` or `μ {0} = 0`.

## iii. Table of contents

- A. Definitions
- B. Coercions
- C. (In)equalities
- D. Density
  - D.1. Measures with no mass at the origin
  - D.2. Characterization of density

## iv. References

* None.
-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

noncomputable section

open MeasureTheory
open InnerProductSpace
open SchwartzMap
open SchwartzSubmodule

/-!
## A. Definitions
-/

/-- A function is a bounded Schwartz map if it is both Schwartz and bounded by powers of `‖x‖`. -/
def PolyBddSchwartzMap (d : ℕ) (a : ℕ∞) : Submodule ℂ 𝓢(Space d, ℂ) where
  carrier := {f : 𝓢(Space d, ℂ) |
    ∀ k : ℕ, k ≤ a → ∃ C : ℝ, 0 < C ∧ ∀ x : Space d, ‖x‖ ^ (-k : ℤ) * ‖f x‖ ≤ C}
  add_mem' := by
    intro f g hf hg k hk
    obtain ⟨C₁, hC₁_pos, hC₁⟩ := hf k hk
    obtain ⟨C₂, hC₂_pos, hC₂⟩ := hg k hk
    refine ⟨C₁ + C₂, by positivity, fun x ↦ ?_⟩
    refine le_trans ?_ (add_le_add (hC₁ x) (hC₂ x))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le (f x) (g x)) (by positivity)
  zero_mem' := fun _ _ ↦ ⟨1, by simp⟩
  smul_mem' := by
    intro c f hf k hk
    obtain ⟨C, hC_pos, hC⟩ := hf k hk
    refine ⟨(1 + ‖c‖) * C, by positivity, fun x ↦ ?_⟩
    rw [smul_apply, norm_smul, mul_rotate', mul_comm ‖f x‖]
    exact le_trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)) (by linarith)

/-- The continuous linear map `schwartzIncl` with domain restricted to `PolyBddSchwartzMap d a`. -/
def polyBddSchwartzIncl {d : ℕ} {a : ℕ∞} (μ : Measure (Space d)) [μ.HasTemperateGrowth] :
    PolyBddSchwartzMap d a →L[ℂ] SpaceDHilbertSpace d μ :=
  ⟨(schwartzIncl μ).domRestrict (PolyBddSchwartzMap d a),
    (schwartzIncl μ).continuous_domRestrict (schwartzIncl μ).continuous _⟩

/-- The submodule of `SpaceDHilbertSpace d` corresponding to bounded Schwartz maps. -/
abbrev PolyBddSchwartzSubmodule
    (d : ℕ) (a : ℕ∞) (μ : Measure (Space d) := volume) [μ.HasTemperateGrowth] :
    Submodule ℂ (SpaceDHilbertSpace d μ) :=
  (polyBddSchwartzIncl (a := a) μ).range

lemma polyBddSchwartzIncl_injective
    {d : ℕ} (a : ℕ∞) (μ : Measure (Space d)) [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] :
    Function.Injective (polyBddSchwartzIncl (a := a) μ) :=
  LinearMap.injective_domRestrict_iff.mpr <| (schwartzIncl_ker μ).symm ▸ disjoint_bot_right

/-- The linear equivalence between polynomially-bounded Schwartz maps and the corresponding
  submodule of the Hilbert space. -/
def polyBddSchwartzEquiv
    {d : ℕ} {a : ℕ∞} (μ : Measure (Space d)) [μ.HasTemperateGrowth] [μ.IsOpenPosMeasure] :
    PolyBddSchwartzMap d a ≃ₗ[ℂ] PolyBddSchwartzSubmodule d a μ :=
  LinearEquiv.ofInjective (polyBddSchwartzIncl μ).toLinearMap (polyBddSchwartzIncl_injective a μ)

namespace PolyBddSchwartzSubmodule

variable {d : ℕ} {a : ℕ∞}
variable (μ : Measure (Space d)) [μ.HasTemperateGrowth]

/-!
## B. Coercions
-/

instance : CoeOut (PolyBddSchwartzMap d a) 𝓢(Space d, ℂ) := ⟨fun f ↦ f.val⟩

instance : CoeFun (PolyBddSchwartzMap d a) (fun _ ↦ Space d → ℂ) := ⟨fun f ↦ ⇑f.val⟩

@[simp]
lemma toFun_eq_coe (f : PolyBddSchwartzMap d a) (x : Space d) : f.val.toFun x = f.val x := rfl

lemma polyBddSchwartzEquiv_symm_apply_coe [μ.IsOpenPosMeasure]
    {ψ : SchwartzSubmodule d μ} (hψ : ↑ψ ∈ PolyBddSchwartzSubmodule d a μ) :
    ((polyBddSchwartzEquiv μ).symm ⟨ψ, hψ⟩).val = (schwartzEquiv μ).symm ψ := by
  apply (schwartzEquiv μ).injective
  apply SetLike.coe_eq_coe.mp
  obtain ⟨g, hg⟩ := (polyBddSchwartzEquiv μ).surjective ⟨ψ.val, hψ⟩
  have hg' : polyBddSchwartzIncl μ g = ψ := SetLike.coe_eq_coe.mpr hg
  rw [← hg, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, ← hg']
  rfl

variable {μ} in
lemma polyBddSchwartzEquiv_coe_ae [μ.IsOpenPosMeasure] (f : PolyBddSchwartzMap d a) :
    polyBddSchwartzEquiv μ f =ᵐ[μ] f.val :=
  schwartzEquiv_coe_ae f.val

/-!
## C. (In)equalities
-/

lemma PolyBddSchwartzMap_zero_eq_top (d : ℕ) : PolyBddSchwartzMap d 0 = ⊤ := by
  ext f
  have := f.decay 0 0
  simp_all [PolyBddSchwartzMap]

/-- In dimension zero every Schwartz map is polynomially bounded. Space is then the single point
  `0`, where `‖x‖ ^ (-k) = 0` for `k > 0` (see the note in the module documentation). -/
lemma PolyBddSchwartzMap_dim_zero_eq_top : PolyBddSchwartzMap 0 a = ⊤ := by
  refine Submodule.eq_top_iff'.mpr (fun f k _ ↦ ?_)
  refine ⟨1 + ‖f 0‖, by positivity, fun x ↦ ?_⟩
  simp only [Space.point_dim_zero_eq, norm_zero, zpow_neg, zpow_natCast]
  rcases k with _ | k <;> simp [add_nonneg]

lemma PolyBddSchwartzMap_antitone (d : ℕ) {a b : ℕ∞} (h : a ≤ b) :
    PolyBddSchwartzMap d b ≤ PolyBddSchwartzMap d a := fun _ hx k hk ↦ hx k (hk.trans h)

/-- A Schwartz map that vanishes on a neighbourhood of the origin, that is whose topological
  support does not contain `0`, is polynomially bounded for every order `a`. Near the origin the
  map is zero, and away from it the factor `‖x‖ ^ (-k)` is bounded. -/
lemma mem_PolyBddSchwartzMap_of_zero_notMem_tsupport {f : 𝓢(Space d, ℂ)}
    (hf : (0 : Space d) ∉ tsupport f) : f ∈ PolyBddSchwartzMap d a := by
  intro k _
  -- `f` vanishes on a ball `B(0, r)` and is bounded by `M`
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (notMem_tsupport_iff_eventuallyEq.mp hf)
  obtain ⟨M, hM, hfM⟩ := f.decay 0 0
  simp only [pow_zero, norm_iteratedFDeriv_zero, one_mul] at hfM
  refine ⟨(r ^ k)⁻¹ * M + 1, by positivity, fun x ↦ ?_⟩
  rcases lt_or_ge ‖x‖ r with hx | hx
  · have hfx : f x = 0 := hball (mem_ball_zero_iff.mpr hx)
    rw [hfx, norm_zero, mul_zero]
    positivity
  · rw [zpow_neg, zpow_natCast]
    refine le_add_of_le_of_nonneg (mul_le_mul ?_ (hfM x) (norm_nonneg _) (by positivity))
      zero_le_one
    exact inv_anti₀ (pow_pos hr k) (pow_le_pow_left₀ hr.le hx k)

open Filter in
/-- For `d > 0` and `a ≠ 0`, polynomially-bounded Schwartz maps vanish at the origin. The bound
  for `k = 1` gives `‖f x‖ ≤ C * ‖x‖` away from the origin, and `f` is continuous. So these maps
  cannot describe a state with a nonzero amplitude at the origin. -/
lemma PolyBddSchwartzMap_apply_zero_eq_zero [NeZero d] (ha : a ≠ 0) {f : 𝓢(Space d, ℂ)}
    (hf : f ∈ PolyBddSchwartzMap d a) : f 0 = 0 := by
  -- `‖f x‖ ≤ C * ‖x‖` away from the origin, then continuity of `f` at the origin
  obtain ⟨C, -, hb⟩ := hf 1 (by exact_mod_cast Order.one_le_iff_ne_zero.mpr ha)
  have hlim : Tendsto (fun x ↦ ‖f x‖) (nhdsWithin (0 : Space d) {0}ᶜ) (nhds ‖f 0‖) :=
    (f.continuous.norm.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun x : Space d ↦ C * ‖x‖) (nhdsWithin (0 : Space d) {0}ᶜ) (nhds 0) := by
    have h : Tendsto (fun x : Space d ↦ C * ‖x‖) (nhds 0) (nhds (C * ‖(0 : Space d)‖)) :=
      (continuous_const.mul continuous_norm).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ x in nhdsWithin (0 : Space d) {0}ᶜ, ‖f x‖ ≤ C * ‖x‖ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h1 := hb x
    simp only [Nat.cast_one, zpow_neg, zpow_one] at h1
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hx)] at h1
    exact h1.trans_eq (mul_comm _ _)
  exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto hlim hlim2 hev)

lemma of_zero_eq : PolyBddSchwartzSubmodule d 0 μ = SchwartzSubmodule d μ := by
  simp [PolyBddSchwartzSubmodule, polyBddSchwartzIncl, PolyBddSchwartzMap_zero_eq_top]

lemma le_SchwartzSubmodule (d : ℕ) (a : ℕ∞) : PolyBddSchwartzSubmodule d a ≤ SchwartzSubmodule d :=
  LinearMap.range_domRestrict_le_range _ _

lemma antitone {a b : ℕ∞} (h : a ≤ b) :
    PolyBddSchwartzSubmodule d b μ ≤ PolyBddSchwartzSubmodule d a μ := by
  simp only [PolyBddSchwartzSubmodule, polyBddSchwartzIncl,
    ContinuousLinearMap.toLinearMap_domRestrict, LinearMap.range_domRestrict]
  exact Submodule.map_mono (PolyBddSchwartzMap_antitone d h)

/-!
## D. Density
-/

open Filter Complex

/-!
### D.1. Measures with no mass at the origin
-/

/-- If the measure `μ` is finite on compact sets and gives no mass to the origin, then
  `PolyBddSchwartzSubmodule d a μ` is dense in `SpaceDHilbertSpace d μ`, for every `d` and `a`.
  A state orthogonal to the submodule is orthogonal to every smooth compactly supported function
  that vanishes near the origin, so it vanishes almost everywhere away from the origin. Since
  `μ {0} = 0`, it vanishes almost everywhere. -/
lemma dense_of_measure_singleton_zero_eq_zero [IsFiniteMeasureOnCompacts μ] (h : μ {0} = 0) :
    Dense (PolyBddSchwartzSubmodule d a μ : Set (SpaceDHilbertSpace d μ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro φ hφ
  -- `φ` vanishes a.e. on `{0}ᶜ`: pair it with smooth compactly supported functions on `{0}ᶜ`
  have hint : ∀ᵐ x ∂μ, x ∈ ({0}ᶜ : Set (Space d)) → φ x = 0 := by
    refine isOpen_compl_singleton.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((Lp.memLp φ).locallyIntegrable one_le_two).locallyIntegrableOn _) ?_
    intro g g_smooth g_cpt g_supp
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ := Complex.ofRealCLM.contDiff.comp g_smooth
    have h0G : (0 : Space d) ∉ tsupport (hg₁.toSchwartzMap hg₂) := fun h0 ↦
      g_supp (tsupport_comp_subset (map_zero Complex.ofRealCLM) g h0) (Set.mem_singleton 0)
    have hG : hg₁.toSchwartzMap hg₂ ∈ PolyBddSchwartzMap d a :=
      mem_PolyBddSchwartzMap_of_zero_notMem_tsupport h0G
    have hmem : polyBddSchwartzIncl μ ⟨_, hG⟩ ∈ PolyBddSchwartzSubmodule d a μ :=
      ⟨⟨_, hG⟩, rfl⟩
    have h0 := (Submodule.mem_orthogonal _ _).mp hφ _ hmem
    rw [L2.inner_def] at h0
    refine (integral_congr_ae ?_).trans h0
    have hae : (polyBddSchwartzIncl μ ⟨_, hG⟩ : Space d → ℂ) =ᵐ[μ] hg₁.toSchwartzMap hg₂ :=
      coeFn_toLp _ 2 μ
    filter_upwards [hae] with x hx
    rw [hx]
    simp [Complex.real_smul, mul_comm]
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hint, measure_eq_zero_iff_ae_notMem.mp h] with x h1 h2
  exact h1 h2

/-!
### D.2. Characterization of density
-/

/-- For `d > 0` and `a ≠ 0`, the indicator function of `{0}`, the state concentrated at the
  origin, is orthogonal to `PolyBddSchwartzSubmodule d a μ`, because every polynomially-bounded
  Schwartz map vanishes at the origin. This state is nonzero exactly when `μ {0} ≠ 0`. It then
  cannot be approximated by elements of the submodule. -/
lemma indicatorConstLp_singleton_zero_mem_orthogonal [NeZero d] (ha : a ≠ 0)
    (hfin : μ {0} ≠ ⊤) :
    indicatorConstLp 2 (measurableSet_singleton (0 : Space d)) hfin (1 : ℂ) ∈
      (PolyBddSchwartzSubmodule d a μ)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hu
  rw [L2.inner_indicatorConstLp_one]
  refine integral_eq_zero_of_ae ?_
  have hae : (polyBddSchwartzIncl μ f : Space d → ℂ) =ᵐ[μ] (f : 𝓢(Space d, ℂ)) :=
    coeFn_toLp _ 2 μ
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (measurableSet_singleton 0)]
    with x hx hx0
  obtain rfl := Set.mem_singleton_iff.mp hx0
  exact hx.trans (PolyBddSchwartzMap_apply_zero_eq_zero ha f.2)

/-- For a measure `μ` finite on compact sets, `PolyBddSchwartzSubmodule d a μ` is dense in
  `SpaceDHilbertSpace d μ` if and only if `d = 0`, `a = 0` or `μ {0} = 0`. When `d > 0`, `a ≠ 0`
  and `μ` gives positive mass to the origin, for example for the Dirac measure at `0`, the state
  concentrated at the origin is a nonzero vector orthogonal to the submodule
  (`indicatorConstLp_singleton_zero_mem_orthogonal`). -/
lemma dense_iff [IsFiniteMeasureOnCompacts μ] :
    Dense (PolyBddSchwartzSubmodule d a μ : Set (SpaceDHilbertSpace d μ)) ↔
      d = 0 ∨ a = 0 ∨ μ {0} = 0 := by
  constructor
  · -- otherwise the indicator function of `{0}` is a nonzero element of the orthogonal complement
    intro hdense
    by_contra hcon
    push Not at hcon
    obtain ⟨hd, ha, hμ⟩ := hcon
    have : NeZero d := ⟨hd⟩
    have hfin : μ {0} ≠ ⊤ := isCompact_singleton.measure_lt_top.ne
    have horth := indicatorConstLp_singleton_zero_mem_orthogonal μ ha hfin
    have hbot : (PolyBddSchwartzSubmodule d a μ)ᗮ = ⊥ :=
      Submodule.topologicalClosure_eq_top_iff.mp
        (Submodule.dense_iff_topologicalClosure_eq_top.mp hdense)
    rw [hbot, Submodule.mem_bot] at horth
    have hnorm := norm_indicatorConstLp (p := 2) two_ne_zero ENNReal.ofNat_ne_top
      (hs := measurableSet_singleton (0 : Space d)) (hμs := hfin) (c := (1 : ℂ))
    rw [horth, norm_zero, norm_one, one_mul] at hnorm
    have hpos : 0 < μ.real {0} := ENNReal.toReal_pos hμ hfin
    exact (Real.rpow_pos_of_pos hpos _).ne hnorm
  · rintro (rfl | rfl | h)
    · have hS : PolyBddSchwartzSubmodule 0 a μ = SchwartzSubmodule 0 μ := by
        simp [PolyBddSchwartzSubmodule, polyBddSchwartzIncl, PolyBddSchwartzMap_dim_zero_eq_top]
      rw [hS]
      exact SchwartzSubmodule.dense 0 μ
    · rw [of_zero_eq μ]
      exact SchwartzSubmodule.dense d μ
    · exact dense_of_measure_singleton_zero_eq_zero μ h

/-- If `μ ≤ volume`, then `PolyBddSchwartzSubmodule d a μ` is dense in `SpaceDHilbertSpace d μ`.
  This covers the Lebesgue measure itself, used for the hydrogen atom, whose Hamiltonian has a
  domain containing such a submodule. For `d > 0` the Lebesgue measure gives no mass to the
  origin, hence neither does `μ`, and `dense_iff` applies. -/
lemma dense (hμ : μ ≤ volume) [IsFiniteMeasureOnCompacts μ] :
    Dense (PolyBddSchwartzSubmodule d a μ : Set (SpaceDHilbertSpace d μ)) := by
  rcases eq_or_ne d 0 with rfl | hd
  · exact (dense_iff μ).mpr (Or.inl rfl)
  · have : NeZero d := ⟨hd⟩
    refine (dense_iff μ).mpr (Or.inr (Or.inr ?_))
    have h0 : (volume : Measure (Space d)) {0} = 0 := by simp
    exact nonpos_iff_eq_zero.mp ((hμ {0}).trans h0.le)

/-- The case `a = ⊤` of `dense`: the Schwartz maps satisfying `‖x‖ ^ (-k) * ‖f x‖ ≤ Cₖ` for
  every `k` are dense in `SpaceDHilbertSpace d μ` when `μ ≤ volume`. -/
lemma dense_top (hμ : μ ≤ volume) [IsFiniteMeasureOnCompacts μ] :
    Dense (PolyBddSchwartzSubmodule d ⊤ μ : Set (SpaceDHilbertSpace d μ)) :=
  dense μ hμ

end PolyBddSchwartzSubmodule
end
end SpaceDHilbertSpace
end QuantumMechanics
