/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Physlib.Meta.TODO.Basic
/-!

# Hilbert space for one dimension quantum mechanics

-/

TODO "Remove 1d Hilbert space once dependencies are moved over to SpaceDHilbertSpace."

@[expose] public section

namespace QuantumMechanics

namespace OneDimension

noncomputable section

/-- The Hilbert space for a one dimensional quantum system is defined as
  the space of almost-everywhere equal equivalence classes of square integrable functions
  from `ℝ` to `ℂ`. -/
abbrev HilbertSpace := MeasureTheory.Lp (α := ℝ) ℂ 2

namespace HilbertSpace
open Module MeasureTheory
open InnerProductSpace

/-- The anti-linear map from the Hilbert space to it's dual. -/
def toBra : HilbertSpace →ₛₗ[starRingEnd ℂ] StrongDual ℂ HilbertSpace :=
  InnerProductSpace.toDual ℂ HilbertSpace

@[simp] lemma toBra_apply (f g : HilbertSpace) : toBra f g = ⟪f, g⟫_ℂ := rfl

/-- The anti-linear map, `toBra`, taking a ket to it's corresponding
  bra is surjective. -/
lemma toBra_surjective : Function.Surjective toBra :=
  (InnerProductSpace.toDual ℂ HilbertSpace).surjective

/-- The anti-linear map, `toBra`, taking a ket to it's corresponding
  bra is injective. -/
lemma toBra_injective : Function.Injective toBra := by
  intro f g h
  simpa [toBra] using h

/-!

## Member of the Hilbert space as a property

-/

/-- The proposition `MemHS f` for a function `f : ℝ → ℂ` is defined
  to be true if the function `f` can be lifted to the Hilbert space. -/
def MemHS (f : ℝ → ℂ) : Prop := MemLp f 2 MeasureTheory.volume

lemma aeStronglyMeasurable_of_memHS {f : ℝ → ℂ} (h : MemHS f) : AEStronglyMeasurable f :=
  h.aestronglyMeasurable

/-- A function `f` satisfies `MemHS f` if and only if it is almost everywhere
  strongly measurable, and square integrable. -/
lemma memHS_iff {f : ℝ → ℂ} : MemHS f ↔
    AEStronglyMeasurable f ∧ Integrable (fun x => ‖f x‖ ^ 2) := by
  refine ⟨fun h => ⟨h.aestronglyMeasurable,
    (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h⟩, ?_⟩
  rintro ⟨h1, h2⟩
  exact (memLp_two_iff_integrable_sq_norm h1).mpr h2

@[simp]
lemma zero_memHS : MemHS 0 := by
  change MemHS (fun x => (0 : ℂ))
  rw [memHS_iff]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integrable_fun_zero, and_true]
  fun_prop

@[simp]
lemma zero_fun_memHS : MemHS (fun _ : ℝ => (0 : ℂ)) := zero_memHS

lemma memHS_add {f g : ℝ → ℂ} (hf : MemHS f) (hg : MemHS g) :
    MemHS (f + g) := MeasureTheory.MemLp.add hf hg

lemma memHS_smul {f : ℝ → ℂ} {c : ℂ} (hf : MemHS f) :
    MemHS (c • f) := MeasureTheory.MemLp.const_smul hf c

lemma memHS_of_ae {g : ℝ → ℂ} (f : ℝ → ℂ) (hf : MemHS f) (hfg : f =ᵐ[MeasureTheory.volume] g) :
    MemHS g := MemLp.ae_eq hfg hf

/-!

# Construction of elements of the Hilbert space

-/

lemma aeEqFun_mk_mem_iff (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    AEEqFun.mk f hf ∈ HilbertSpace ↔ MemHS f := by
  simp only [Lp.mem_Lp_iff_memLp]
  exact MeasureTheory.memLp_congr_ae (AEEqFun.coeFn_mk f hf)

/-- Given a function `f : ℝ → ℂ` such that `MemHS f` is true via `hf`, then `HilbertSpace.mk hf`
  is the element of the `HilbertSpace` defined by `f`. -/
def mk {f : ℝ → ℂ} (hf : MemHS f) : HilbertSpace :=
  ⟨AEEqFun.mk f hf.aestronglyMeasurable,
    (aeEqFun_mk_mem_iff f hf.aestronglyMeasurable).mpr hf⟩

lemma coe_hilbertSpace_memHS (f : HilbertSpace) : MemHS (f : ℝ → ℂ) := by
  rw [← aeEqFun_mk_mem_iff f.1 (Lp.aestronglyMeasurable f)]
  have hf : f = AEEqFun.mk f.1 (Lp.aestronglyMeasurable f) := (AEEqFun.mk_coeFn _).symm
  exact hf ▸ f.2

lemma mk_surjective (f : HilbertSpace) : ∃ (g : ℝ → ℂ), ∃ (hg : MemHS g), mk hg = f := by
  use f, coe_hilbertSpace_memHS f
  simp [mk]

lemma coe_mk_ae {f : ℝ → ℂ} (hf : MemHS f) : (mk hf : ℝ → ℂ) =ᵐ[MeasureTheory.volume] f :=
  AEEqFun.coeFn_mk f hf.aestronglyMeasurable

lemma inner_mk_mk {f g : ℝ → ℂ} {hf : MemHS f} {hg : MemHS g} :
    inner ℂ (mk hf) (mk hg) = ∫ x : ℝ, starRingEnd ℂ (f x) * g x := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coe_mk_ae hf, coe_mk_ae hg] with _ hf hg
  simp [hf, hg, mul_comm]

@[simp]
lemma eLpNorm_mk {f : ℝ → ℂ} {hf : MemHS f} : eLpNorm (mk hf) 2 volume = eLpNorm f 2 volume :=
  MeasureTheory.eLpNorm_congr_ae (coe_mk_ae hf)

lemma mem_iff' {f : ℝ → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.AEEqFun.mk f hf ∈ HilbertSpace
    ↔ MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) :=
  (aeEqFun_mk_mem_iff f hf).trans (memLp_two_iff_integrable_sq_norm hf)

lemma mk_add {f g : ℝ → ℂ} {hf : MemHS f} {hg : MemHS g} :
    mk (memHS_add hf hg) = mk hf + mk hg := rfl

lemma mk_smul {f : ℝ → ℂ} {c : ℂ} {hf : MemHS f} :
    mk (memHS_smul (c := c) hf) = c • mk hf := rfl

lemma mk_eq_iff {f g : ℝ → ℂ} {hf : MemHS f} {hg : MemHS g} :
    mk hf = mk hg ↔ f =ᵐ[volume] g := by
  simp [mk]

lemma ext_iff {f g : HilbertSpace} :
    f = g ↔ (f : ℝ → ℂ) =ᶠ[ae volume] (g : ℝ → ℂ) := by
  exact Lp.ext_iff

end HilbertSpace
end
end OneDimension
end QuantumMechanics
