/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Axis
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
/-!
# Boost-weight gradings of representations of `SL(2,ℂ)`

An element of a representation has boost weight `k` along the `i`-th spatial axis when the
one-parameter boost family acts on it by `t ^ k`; `boostWeightSubmodule rep i k` collects these elements.
`IsBoostGraded rep` says the representation acts on an algebra by algebra automorphisms and
that the weight spaces span along every axis. Given it, the weight spaces are independent
(they sit in eigenspaces of a single boost at distinct eigenvalues), so they decompose the
algebra as an internal direct sum, grade it as a graded algebra, and support the weight
projections `boostProj` together with their calculus: how projections interact with submodules,
weight-shifting operators, and products.

The section-A transports (`weightSpan_tprod_eq_top`, `weightSpan_prod_eq_top`,
`weightSpan_symmetricAlgebra_eq_top`, `weightSpan_exteriorAlgebra_eq_top`,
`weightSpan_baseChange_eq_top`, `weightSpan_eq_top_of_two`) are the tools
for establishing `IsBoostGraded` for a concrete algebra, by descending to the spaces it is
built from.

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups TensorProduct

/-!

## A. Boost weights of a general representation

The descent to the component spaces is uniform, so it is carried out once here for an arbitrary
representation. The weight spaces are defined exactly as `boostWeightSubmodule` is, and
`weightSpan rep i = ⊤` says that they span. The point of the section is that this condition
propagates along
every construction the jet algebra is built from: tensor products, products, symmetric algebras,
exterior algebras and base change. The recursion bottoms out at a finite-dimensional space with
an eigenbasis, where the light-cone combinations do the work.

-/

namespace BoostWeight

variable {K : Type*} [Field K] [Algebra ℝ K]
variable {M N V : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup V] [Module K V]
variable {i : Fin 3}

private lemma algebraMap_ne_zero {t : ℝ} (ht : t ≠ 0) : (algebraMap ℝ K t) ≠ 0 :=
  fun h => ht ((algebraMap ℝ K).injective (by simpa using h))

/-- The weight-`w` space of a representation: the vectors scaling by `t ^ w` under the
  `z`-boost at parameter `t`. -/
def boostWeightSubmodule (rep : Representation K SL(2,ℂ) M) (i : Fin 3) (w : ℤ) : Submodule K M where
  carrier := {x | ∀ (t : ℝ) (ht : t ≠ 0),
    rep (Lorentz.SL2C.boostAxis i t ht) x = (algebraMap ℝ K t) ^ w • x}
  add_mem' {a b} ha hb := fun t ht => by rw [map_add, ha t ht, hb t ht, smul_add]
  zero_mem' := fun t ht => by rw [map_zero, smul_zero]
  smul_mem' c x hx := fun t ht => by rw [map_smul, hx t ht, smul_comm]

lemma mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) M} {i : Fin 3} {w : ℤ} {x : M} :
    x ∈ boostWeightSubmodule rep i w ↔ ∀ (t : ℝ) (ht : t ≠ 0),
      rep (Lorentz.SL2C.boostAxis i t ht) x = (algebraMap ℝ K t) ^ w • x := Iff.rfl

/-- The span of all the weight spaces. -/
def weightSpan (rep : Representation K SL(2,ℂ) M) (i : Fin 3) : Submodule K M :=
  ⨆ w, boostWeightSubmodule rep i w

/-- A representation of `SL(2,ℂ)` on an algebra is **boost-graded** when it acts by algebra
  automorphisms and its boost-weight spaces span, along every coordinate axis. This is the
  interface behind the boost-weight grading: given it, the weight spaces decompose the algebra
  as an internal direct sum, grade it as an algebra, and support the projections `boostProj` with
  their calculus. -/
class IsBoostGraded {A : Type*} [Ring A] [Algebra K A]
    (rep : Representation K SL(2,ℂ) A) : Prop where
  apply_one : ∀ Λ, rep Λ 1 = 1
  apply_mul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y
  weightSpan_eq_top : ∀ i : Fin 3, weightSpan rep i = ⊤

lemma mem_weightSpan_of_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) M} {w : ℤ} {x : M}
    (h : x ∈ boostWeightSubmodule rep i w) : x ∈ weightSpan rep i :=
  Submodule.mem_iSup_of_mem w h

/-- A representation with a spanning family of vectors in the weight span is graded. -/
lemma weightSpan_eq_top_of_span {rep : Representation K SL(2,ℂ) M} {S : Set M}
    (hS : Submodule.span K S = ⊤) (h : ∀ x ∈ S, x ∈ weightSpan rep i) :
    weightSpan rep i = ⊤ :=
  eq_top_iff.mpr (hS ▸ Submodule.span_le.mpr h)

/-- A representation with a basis of vectors lying in the weight span is graded. -/
lemma weightSpan_eq_top_of_basis {ι : Type*} {rep : Representation K SL(2,ℂ) M}
    (b : Module.Basis ι K M) (h : ∀ n, b n ∈ weightSpan rep i) : weightSpan rep i = ⊤ :=
  weightSpan_eq_top_of_span b.span_eq (by rintro _ ⟨n, rfl⟩; exact h n)

/-!

### Tensor products

-/

lemma tmul_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) M} {rep₂ : Representation K SL(2,ℂ) N}
    {a b : ℤ} {x : M} {y : N} (hx : x ∈ boostWeightSubmodule rep i a) (hy : y ∈ boostWeightSubmodule rep₂ i b) :
    x ⊗ₜ[K] y ∈ boostWeightSubmodule (rep.tprod rep₂) i (a + b) := by
  intro t ht
  show (TensorProduct.map _ _) _ = _
  rw [TensorProduct.map_tmul, hx t ht, hy t ht]
  simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul]
  rw [← zpow_add₀ (algebraMap_ne_zero (K := K) ht), add_comm b a]

lemma weightSpan_tprod_eq_top {rep : Representation K SL(2,ℂ) M}
    {rep₂ : Representation K SL(2,ℂ) N} (h₁ : weightSpan rep i = ⊤)
    (h₂ : weightSpan rep₂ i = ⊤) : weightSpan (rep.tprod rep₂) i = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add u v hu hv => exact Submodule.add_mem _ hu hv
  | tmul x y =>
    have hx := Submodule.eq_top_iff'.mp h₁ x
    have hy := Submodule.eq_top_iff'.mp h₂ y
    induction hx using Submodule.iSup_induction' with
    | mem a x' hx' =>
      induction hy using Submodule.iSup_induction' with
      | mem b y' hy' => exact mem_weightSpan_of_mem_boostWeightSubmodule (tmul_mem_boostWeightSubmodule hx' hy')
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add u v _ _ ihu ihv => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ihu ihv
    | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ ihu ihv


/-!

### Products

-/

lemma inl_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) M} {rep₂ : Representation K SL(2,ℂ) N}
    {a : ℤ} {x : M} (hx : x ∈ boostWeightSubmodule rep i a) :
    ((x, 0) : M × N) ∈ boostWeightSubmodule (rep.prod rep₂) i a := by
  intro t ht
  show ((rep _ x, rep₂ _ 0) : M × N) = _
  rw [map_zero, hx t ht, Prod.smul_mk, smul_zero]

lemma inr_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) M} {rep₂ : Representation K SL(2,ℂ) N}
    {a : ℤ} {y : N} (hy : y ∈ boostWeightSubmodule rep₂ i a) :
    ((0, y) : M × N) ∈ boostWeightSubmodule (rep.prod rep₂) i a := by
  intro t ht
  show ((rep _ 0, rep₂ _ y) : M × N) = _
  rw [map_zero, hy t ht, Prod.smul_mk, smul_zero]

lemma weightSpan_prod_eq_top {rep : Representation K SL(2,ℂ) M}
    {rep₂ : Representation K SL(2,ℂ) N} (h₁ : weightSpan rep i = ⊤)
    (h₂ : weightSpan rep₂ i = ⊤) : weightSpan (rep.prod rep₂) i = ⊤ := by
  have hleft : ∀ x : M, ((x, (0 : N))) ∈ weightSpan (rep.prod rep₂) i := by
    intro x
    have hx := Submodule.eq_top_iff'.mp h₁ x
    induction hx using Submodule.iSup_induction' with
    | mem a u hu => exact mem_weightSpan_of_mem_boostWeightSubmodule (inl_mem_boostWeightSubmodule hu)
    | zero => exact Submodule.zero_mem _
    | add u v _ _ ihu ihv =>
      rw [show ((u + v, (0 : N))) = ((u, (0 : N))) + ((v, (0 : N))) from by ext <;> simp]
      exact Submodule.add_mem _ ihu ihv
  have hright : ∀ y : N, (((0 : M), y)) ∈ weightSpan (rep.prod rep₂) i := by
    intro y
    have hy := Submodule.eq_top_iff'.mp h₂ y
    induction hy using Submodule.iSup_induction' with
    | mem a u hu => exact mem_weightSpan_of_mem_boostWeightSubmodule (inr_mem_boostWeightSubmodule hu)
    | zero => exact Submodule.zero_mem _
    | add u v _ _ ihu ihv =>
      rw [show (((0 : M), u + v)) = (((0 : M), u)) + (((0 : M), v)) from by ext <;> simp]
      exact Submodule.add_mem _ ihu ihv
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  rw [show z = ((z.1, (0 : N))) + (((0 : M), z.2)) from by ext <;> simp]
  exact Submodule.add_mem _ (hleft z.1) (hright z.2)

/-!

### Algebras generated in degree one

-/

variable {A : Type*} [Ring A] [Algebra K A]

lemma one_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) A} (hone : ∀ Λ, rep Λ 1 = 1) :
    (1 : A) ∈ boostWeightSubmodule rep i 0 := fun t _ => by rw [hone, zpow_zero, one_smul]

lemma mul_mem_boostWeightSubmodule {rep : Representation K SL(2,ℂ) A}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y)
    {a b : ℤ} {x y : A} (hx : x ∈ boostWeightSubmodule rep i a) (hy : y ∈ boostWeightSubmodule rep i b) :
    x * y ∈ boostWeightSubmodule rep i (a + b) := by
  intro t ht
  rw [hmul, hx t ht, hy t ht, smul_mul_smul_comm,
    zpow_add₀ (algebraMap_ne_zero (K := K) ht)]

lemma mul_mem_weightSpan {rep : Representation K SL(2,ℂ) A}
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y)
    {x y : A} (hx : x ∈ weightSpan rep i) (hy : y ∈ weightSpan rep i) :
    x * y ∈ weightSpan rep i := by
  induction hx using Submodule.iSup_induction' with
  | mem a u hu =>
    induction hy using Submodule.iSup_induction' with
    | mem b v hv => exact mem_weightSpan_of_mem_boostWeightSubmodule (mul_mem_boostWeightSubmodule hmul hu hv)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add v w _ _ ihv ihw => rw [mul_add]; exact Submodule.add_mem _ ihv ihw
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add u v _ _ ihu ihv => rw [add_mul]; exact Submodule.add_mem _ ihu ihv

lemma algebraMap_mem_weightSpan {rep : Representation K SL(2,ℂ) A}
    (hone : ∀ Λ, rep Λ 1 = 1) (r : K) : algebraMap K A r ∈ weightSpan rep i := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (mem_weightSpan_of_mem_boostWeightSubmodule (one_mem_boostWeightSubmodule hone))

/-- A symmetric algebra is boost-graded as soon as its degree-one part is. -/
lemma weightSpan_symmetricAlgebra_eq_top {V : Type*} [AddCommGroup V] [Module K V]
    {repV : Representation K SL(2,ℂ) V}
    {repA : Representation K SL(2,ℂ) (SymmetricAlgebra K V)}
    (hone : ∀ Λ, repA Λ 1 = 1)
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : SymmetricAlgebra K V),
      repA Λ (x * y) = repA Λ x * repA Λ y)
    (hι : ∀ (Λ : SL(2,ℂ)) (x : V),
      repA Λ (SymmetricAlgebra.ι K V x) = SymmetricAlgebra.ι K V (repV Λ x))
    (hV : weightSpan repV i = ⊤) : weightSpan repA i = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact algebraMap_mem_weightSpan hone r
  | ι v =>
    have hv := Submodule.eq_top_iff'.mp hV v
    induction hv using Submodule.iSup_induction' with
    | mem a u hu =>
      refine mem_weightSpan_of_mem_boostWeightSubmodule (w := a) fun t ht => ?_
      rw [hι, hu t ht, map_smul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | mul u v ihu ihv => exact mul_mem_weightSpan hmul ihu ihv
  | add u v ihu ihv => exact Submodule.add_mem _ ihu ihv

/-- An exterior algebra is boost-graded as soon as its degree-one part is. -/
lemma weightSpan_exteriorAlgebra_eq_top {V : Type*} [AddCommGroup V] [Module K V]
    {repV : Representation K SL(2,ℂ) V}
    {repA : Representation K SL(2,ℂ) (ExteriorAlgebra K V)}
    (hone : ∀ Λ, repA Λ 1 = 1)
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : ExteriorAlgebra K V),
      repA Λ (x * y) = repA Λ x * repA Λ y)
    (hι : ∀ (Λ : SL(2,ℂ)) (x : V),
      repA Λ (ExteriorAlgebra.ι K x) = ExteriorAlgebra.ι K (repV Λ x))
    (hV : weightSpan repV i = ⊤) : weightSpan repA i = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => exact algebraMap_mem_weightSpan hone r
  | ι v =>
    have hv := Submodule.eq_top_iff'.mp hV v
    induction hv using Submodule.iSup_induction' with
    | mem a u hu =>
      refine mem_weightSpan_of_mem_boostWeightSubmodule (w := a) fun t ht => ?_
      rw [hι, hu t ht, map_smul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | mul u v ihu ihv => exact mul_mem_weightSpan hmul ihu ihv
  | add u v ihu ihv => exact Submodule.add_mem _ ihu ihv

/-!

### The light-cone eigenbasis of a spacetime-indexed space

-/

/-- A space with a basis indexed by spacetime directions transforming by the columns of the
  Lorentz matrix is boost-graded: the light-cone combinations `b₀ ∓ b₃` are eigenvectors of
  weight `±2` and the transverse directions are invariant. -/
lemma weightSpan_eq_top_of_lorentzColumns {rep : Representation K SL(2,ℂ) M}
    (b : Module.Basis (Fin 1 ⊕ Fin 3) K M)
    (h : ∀ (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3), rep Λ (b μ) =
      ∑ j, algebraMap ℝ K ((Lorentz.SL2C.toLorentzGroup Λ).1 j μ) • b j) :
    weightSpan rep 2 = ⊤ := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℝ K).injective
  have key : ∀ (t : ℝ) (ht : t ≠ 0) (μ : Fin 1 ⊕ Fin 3),
      rep (Lorentz.SL2C.boostAxis 2 t ht) (b μ) =
        ∑ j, algebraMap ℝ K ((LorentzGroup.boostAxis 2 t ht).1 j μ) • b j := by
    intro t ht μ
    rw [h]
    rfl
  have hplus : b (Sum.inl 0) - b (Sum.inr 2) ∈ boostWeightSubmodule rep 2 2 := by
    intro t ht
    have h0 : (algebraMap ℝ K t) ≠ 0 := algebraMap_ne_zero ht
    rw [map_sub, key t ht, key t ht]
    simp [Fintype.sum_sum_type, Fin.sum_univ_three, LorentzGroup.boostAxis_apply]
    match_scalars <;>
      (field_simp; try ring_nf; try norm_num; try simp only [map_ofNat, true_or])
  have hminus : b (Sum.inl 0) + b (Sum.inr 2) ∈ boostWeightSubmodule rep 2 (-2) := by
    intro t ht
    have h0 : (algebraMap ℝ K t) ≠ 0 := algebraMap_ne_zero ht
    rw [map_add, key t ht, key t ht]
    simp [Fintype.sum_sum_type, Fin.sum_univ_three, LorentzGroup.boostAxis_apply]
    match_scalars <;> (field_simp; try ring_nf; try simp only [map_ofNat])
  have htr : ∀ i' : Fin 3, i' = 0 ∨ i' = 1 → b (Sum.inr i') ∈ boostWeightSubmodule rep 2 0 := by
    rintro i (rfl | rfl) <;>
    · intro t ht
      rw [key t ht]
      simp [LorentzGroup.boostAxis_apply]
  refine weightSpan_eq_top_of_basis b fun μ => ?_
  match μ with
  | Sum.inl 0 =>
    rw [show b (Sum.inl 0) = (2⁻¹ : K) • ((b (Sum.inl 0) - b (Sum.inr 2))
        + (b (Sum.inl 0) + b (Sum.inr 2))) from by match_scalars <;> (field_simp; try ring)]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (mem_weightSpan_of_mem_boostWeightSubmodule hplus) (mem_weightSpan_of_mem_boostWeightSubmodule hminus))
  | Sum.inr 0 => exact mem_weightSpan_of_mem_boostWeightSubmodule (htr 0 (Or.inl rfl))
  | Sum.inr 1 => exact mem_weightSpan_of_mem_boostWeightSubmodule (htr 1 (Or.inr rfl))
  | Sum.inr 2 =>
    rw [show b (Sum.inr 2) = (2⁻¹ : K) • ((b (Sum.inl 0) + b (Sum.inr 2))
        - (b (Sum.inl 0) - b (Sum.inr 2))) from by match_scalars <;> (field_simp; try ring)]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (mem_weightSpan_of_mem_boostWeightSubmodule hminus) (mem_weightSpan_of_mem_boostWeightSubmodule hplus))

/-!

### Base change from the real to the complex scalars

-/

lemma weightSpan_baseChange_eq_top {A : Type*} [AddCommGroup A] [Module ℝ A]
    {repR : Representation ℝ SL(2,ℂ) A} {repC : Representation ℂ SL(2,ℂ) (ℂ ⊗[ℝ] A)}
    (h : ∀ (Λ : SL(2,ℂ)) (c : ℂ) (y : A), repC Λ (c ⊗ₜ[ℝ] y) = c ⊗ₜ[ℝ] repR Λ y)
    (hR : weightSpan repR i = ⊤) : weightSpan repC i = ⊤ := by
  have htmul : ∀ (c : ℂ) (w : ℤ) (y : A), y ∈ boostWeightSubmodule repR i w →
      (c ⊗ₜ[ℝ] y : ℂ ⊗[ℝ] A) ∈ boostWeightSubmodule repC i w := by
    intro c w y hy t ht
    rw [h, hy t ht, TensorProduct.tmul_smul,
      show ((algebraMap ℝ ℝ) t) ^ w = t ^ w from by simp,
      ← algebraMap_smul (R := ℝ) ℂ (t ^ w) (c ⊗ₜ[ℝ] y), map_zpow₀]
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add u v hu hv => exact Submodule.add_mem _ hu hv
  | tmul c y =>
    have hy := Submodule.eq_top_iff'.mp hR y
    induction hy using Submodule.iSup_induction' with
    | mem w u hu => exact mem_weightSpan_of_mem_boostWeightSubmodule (htmul c w u hu)
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add u v _ _ ihu ihv => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ihu ihv


/-!

### Transport between the three axes

-/

/-- The axis boosts are conjugate, so the weight spaces span along every axis as soon as they
  span along the `z`-axis. -/
lemma weightSpan_eq_top_of_two {rep : Representation K SL(2,ℂ) M} (h : weightSpan rep 2 = ⊤)
    (i : Fin 3) : weightSpan rep i = ⊤ := by
  obtain ⟨R, hR⟩ := Lorentz.SL2C.exists_conj_boostAxis i
  have hsurj : ∀ x : M, rep R (rep R⁻¹ x) = x := by
    intro x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hmap : ∀ (w : ℤ) (u : M), u ∈ boostWeightSubmodule rep 2 w → rep R u ∈ boostWeightSubmodule rep i w := by
    intro w u hu t ht
    rw [← Module.End.mul_apply, ← map_mul, hR t ht, inv_mul_cancel_right, map_mul,
      Module.End.mul_apply, hu t ht, map_smul]
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, rep R y = x := ⟨rep R⁻¹ x, hsurj x⟩
  have hy := Submodule.eq_top_iff'.mp h y
  induction hy using Submodule.iSup_induction' with
  | mem w u hu => exact mem_weightSpan_of_mem_boostWeightSubmodule (hmap w u hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv

/-!

## B. The graded-algebra theory of a boost-graded representation

-/

section Theory

omit [Algebra ℝ K] in
/-- Multiply a two-term linear decomposition into a submodule. -/
lemma mul_mem_of_eq_smul_add_smul {p : Submodule K A} {a u v y : A}
    (c d : K) (hu : a * u ∈ p) (hv : a * v ∈ p) (hy : y = c • u + d • v) : a * y ∈ p := by
  subst hy
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  exact add_mem (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv)

omit [Algebra ℝ K] in
/-- An integer-indexed supremum of submodules supported on the weights `0`, `2`, `-2`
  collapses to the three corresponding terms. -/
lemma iSup_eq_sup_zero_two_neg_two (f : ℤ → Submodule K M)
    (hf : ∀ l : ℤ, l ≠ 0 → l ≠ 2 → l ≠ -2 → f l = ⊥) :
    (⨆ l, f l) = f 0 ⊔ f 2 ⊔ f (-2) := by
  refine le_antisymm (iSup_le fun l => ?_)
    (sup_le (sup_le (le_iSup f 0) (le_iSup f 2)) (le_iSup f (-2)))
  by_cases h0 : l = 0
  · subst h0; exact le_sup_left.trans le_sup_left
  by_cases h2 : l = 2
  · subst h2; exact le_sup_right.trans le_sup_left
  by_cases hn2 : l = -2
  · subst hn2; exact le_sup_right
  · rw [hf l h0 h2 hn2]; exact bot_le

/-- The weight space of weight `k` sits inside the `2 ^ k` eigenspace of the boost at
  parameter two. -/
lemma boostWeightSubmodule_le_eigenspace (rep : Representation K SL(2,ℂ) M) (k : ℤ) :
    boostWeightSubmodule rep i k ≤
      Module.End.eigenspace (rep (Lorentz.SL2C.boostAxis i 2 two_ne_zero))
      ((algebraMap ℝ K 2) ^ k) := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  exact hx 2 two_ne_zero

private lemma zpow_algebraMap_two_injective :
    Function.Injective (fun k : ℤ => ((algebraMap ℝ K 2) ^ k)) := by
  intro a b hab
  simp only [← map_zpow₀] at hab
  exact zpow_right_injective₀ (by norm_num) (by norm_num) ((algebraMap ℝ K).injective hab)

/-- The weight spaces are independent: a decomposition into homogeneous parts is unique when
  it exists. -/
lemma boostWeightSubmodule_iSupIndep (rep : Representation K SL(2,ℂ) M) :
    iSupIndep (boostWeightSubmodule rep i) :=
  ((Module.End.eigenspaces_iSupIndep
      (rep (Lorentz.SL2C.boostAxis i 2 two_ne_zero) : Module.End K M)).comp
    zpow_algebraMap_two_injective).mono fun k => boostWeightSubmodule_le_eigenspace rep k


/-!

### Weight-zero vectors

An invariant of the group has weight zero along every axis, and the weight spaces are
independent, so a weight-zero vector written as a sum of vectors of definite weights is equal
to the weight-zero term of that sum. The `Invariants` files use these to read an invariant off
its weight decomposition.

-/

/-- A vector fixed by the whole group has boost weight zero along every axis. -/
lemma mem_boostWeightSubmodule_zero_of_invariant {rep : Representation K SL(2,ℂ) M} {x : M}
    (hinv : ∀ g : SL(2,ℂ), rep g x = x) (i : Fin 3) :
    x ∈ boostWeightSubmodule rep i 0 := by
  rw [mem_boostWeightSubmodule]
  intro t ht
  rw [hinv, zpow_zero, one_smul]

/-- Vectors of distinct boost weights adding to zero are each zero. -/
lemma eq_zero_of_sum_mem_boostWeightSubmodule
    {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [AddCommGroup A] [Module K A]
    {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {s : Finset ℤ} {w : ℤ → A}
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (hsum : ∑ m ∈ s, w m = 0) :
    ∀ m ∈ s, w m = 0 := by
  intro m₀ hm₀
  refine Submodule.disjoint_def.1
    (iSupIndep_def.1 (boostWeightSubmodule_iSupIndep rep) m₀) (w m₀) (hw m₀ hm₀) ?_
  have h : w m₀ = -∑ m ∈ s.erase m₀, w m :=
    eq_neg_of_add_eq_zero_left (by rw [Finset.add_sum_erase s w hm₀]; exact hsum)
  rw [h]
  exact neg_mem (sum_mem fun m hm => Submodule.mem_iSup_of_mem m
    (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hm)
      (hw m (Finset.mem_of_mem_erase hm))))

/-- A weight-zero vector written as a sum of definite weights equals the weight-zero term. -/
lemma eq_component_zero_of_mem_boostWeightSubmodule
    {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [AddCommGroup A] [Module K A]
    {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {s : Finset ℤ} {w : ℤ → A} {x : A}
    (hx : x ∈ boostWeightSubmodule rep i 0)
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (h0 : (0 : ℤ) ∈ s) (hsum : x = ∑ m ∈ s, w m) :
    x = w 0 := by
  have hv : ∀ m ∈ s, Function.update w 0 (w 0 - x) m ∈ boostWeightSubmodule rep i m := by
    intro m hm
    by_cases h : m = 0
    · subst h
      rw [Function.update_self]
      exact sub_mem (hw 0 h0) hx
    · rw [Function.update_of_ne h]
      exact hw m hm
  have hsum0 : ∑ m ∈ s, Function.update w 0 (w 0 - x) m = 0 := by
    rw [Finset.sum_update_of_mem h0, hsum, ← Finset.add_sum_erase s w h0, Finset.erase_eq]
    abel
  have h := eq_zero_of_sum_mem_boostWeightSubmodule hv hsum0 0 h0
  rw [Function.update_self] at h
  exact (sub_eq_zero.1 h).symm

/-- If each `S m` lies in the weight-`m` space, a weight-zero vector of their join lies in
  `S 0`. -/
lemma mem_of_mem_iSup_of_boostWeight_zero {rep : Representation K SL(2,ℂ) M} {i : Fin 3}
    {S : ℤ → Submodule K M} (hS : ∀ m : ℤ, S m ≤ boostWeightSubmodule rep i m) {x : M}
    (hx : x ∈ ⨆ m, S m) (h0 : x ∈ boostWeightSubmodule rep i 0) : x ∈ S 0 := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hx
  have hkey := eq_component_zero_of_mem_boostWeightSubmodule (i := i)
    (s := insert 0 f.support) (w := fun m => f m) h0
    (fun m _ => hS m (hf m)) (Finset.mem_insert_self 0 _) ?_
  · rw [hkey]
    exact hf 0
  · rw [Finsupp.sum]
    by_cases h : (0 : ℤ) ∈ f.support
    · rw [Finset.insert_eq_self.2 h]
    · rw [Finset.sum_insert h, Finsupp.notMem_support_iff.1 h, zero_add]

variable (rep : Representation K SL(2,ℂ) A)

/-- The unit has boost weight zero. -/
lemma one_mem [IsBoostGraded rep] : (1 : A) ∈ boostWeightSubmodule rep i 0 :=
  one_mem_boostWeightSubmodule (IsBoostGraded.apply_one (rep := rep))

/-- Boost weights add under multiplication. -/
lemma mul_mem [IsBoostGraded rep] {k l : ℤ} {x y : A} (hx : x ∈ boostWeightSubmodule rep i k)
    (hy : y ∈ boostWeightSubmodule rep i l) : x * y ∈ boostWeightSubmodule rep i (k + l) :=
  mul_mem_boostWeightSubmodule (IsBoostGraded.apply_mul (rep := rep)) hx hy

/-- Boost weights add under multiplication, with the sum of the weights given explicitly. -/
lemma mul_mem' [IsBoostGraded rep] {k l n : ℤ} {x y : A} (hx : x ∈ boostWeightSubmodule rep i k)
    (hy : y ∈ boostWeightSubmodule rep i l) (hkl : k + l = n) : x * y ∈ boostWeightSubmodule rep i n :=
  hkl ▸ mul_mem rep hx hy

instance [IsBoostGraded rep] : SetLike.GradedMonoid (boostWeightSubmodule rep i) where
  one_mem := one_mem rep
  mul_mem _ _ _ _ hx hy := mul_mem rep hx hy

/-- Recover the two summands from the sum and difference: if `u + v` and `u - v` lie in a
  submodule then so do `u` and `v`. -/
lemma mem_of_add_mem_of_sub_mem {p : Submodule K M} {u v : M}
    (h₁ : u + v ∈ p) (h₂ : u - v ∈ p) : u ∈ p ∧ v ∈ p := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℝ K).injective
  constructor
  · rw [show u = (2⁻¹ : K) • (u + v) + (2⁻¹ : K) • (u - v) from by
      match_scalars <;> (field_simp; try norm_num)]
    exact add_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  · rw [show v = (2⁻¹ : K) • (u + v) - (2⁻¹ : K) • (u - v) from by
      match_scalars <;> (field_simp; try norm_num)]
    exact sub_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)

/-- A product of two submodules of pure weights `k` and `l` with `k + l ≠ n` lands in the span
  of the weights other than `n`. -/
lemma mul_le_iSup_boostWeightSubmodule_of_ne [IsBoostGraded rep] {X Y : Submodule K A} {k l n : ℤ}
    (hX : X ≤ boostWeightSubmodule rep i k) (hY : Y ≤ boostWeightSubmodule rep i l) (h : k + l ≠ n) :
    X * Y ≤ ⨆ (j : ℤ) (_ : j ≠ n), boostWeightSubmodule rep i j :=
  Submodule.mul_le.2 fun _ hx _ hy => Submodule.mem_iSup_of_mem (k + l)
    (Submodule.mem_iSup_of_mem h (mul_mem rep (hX hx) (hY hy)))

/-- **Extracting the weight-`k` part of a submodule.** -/
lemma boostWeightSubmodule_inf_eq {k : ℤ} {S V : Submodule K A}
    (hS0 : S ≤ boostWeightSubmodule rep i k) (hSV : S ≤ V)
    (hV : V ≤ S ⊔ ⨆ (j : ℤ) (_ : j ≠ k), boostWeightSubmodule rep i j) :
    boostWeightSubmodule rep i k ⊓ V = S := by
  refine le_antisymm ((inf_le_inf_left _ hV).trans ?_) (le_inf hS0 hSV)
  rw [inf_comm, sup_inf_assoc_of_le _ hS0,
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep rep (i := i) k).symm, sup_bot_eq]

/-- **Extracting the weight-`k` part of a span of homogeneous elements.** -/
lemma boostWeightSubmodule_inf_eq_span {k : ℤ} {S T : Set A} {V : Submodule K A}
    (hS : ∀ x ∈ S, x ∈ boostWeightSubmodule rep i k)
    (hT : ∀ x ∈ T, ∃ j ≠ k, x ∈ boostWeightSubmodule rep i j)
    (hSV : Submodule.span K S ≤ V) (hV : V ≤ Submodule.span K (S ∪ T)) :
    boostWeightSubmodule rep i k ⊓ V = Submodule.span K S := by
  refine boostWeightSubmodule_inf_eq rep (Submodule.span_le.2 hS) hSV (hV.trans ?_)
  rw [Submodule.span_union]
  refine sup_le le_sup_left (le_sup_of_le_right (Submodule.span_le.2 ?_))
  intro x hx
  obtain ⟨j, hj, hxj⟩ := hT x hx
  exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj hxj)

/-- The span of the homogeneous elements contains one. -/
lemma one_mem_iSup_boostWeightSubmodule [IsBoostGraded rep] : (1 : A) ∈ ⨆ k, boostWeightSubmodule rep i k :=
  Submodule.mem_iSup_of_mem 0 (one_mem rep)

/-- The span of the homogeneous elements is closed under multiplication. -/
lemma mul_mem_iSup_boostWeightSubmodule [IsBoostGraded rep] {x y : A}
    (hx : x ∈ ⨆ k, boostWeightSubmodule rep i k) (hy : y ∈ ⨆ k, boostWeightSubmodule rep i k) :
    x * y ∈ ⨆ k, boostWeightSubmodule rep i k := by
  induction hx using Submodule.iSup_induction' with
  | mem k a ha =>
    induction hy using Submodule.iSup_induction' with
    | mem l b hb => exact Submodule.mem_iSup_of_mem (k + l) (mul_mem rep ha hb)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add b c _ _ ihb ihc => rw [mul_add]; exact Submodule.add_mem _ ihb ihc
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ iha ihb => rw [add_mul]; exact Submodule.add_mem _ iha ihb

/-- The homogeneous elements span a subalgebra. -/
noncomputable def subalgebra [IsBoostGraded rep] (i : Fin 3) : Subalgebra K A :=
  Submodule.toSubalgebra (⨆ k, boostWeightSubmodule rep i k) (one_mem_iSup_boostWeightSubmodule rep)
    fun _ _ hx hy => mul_mem_iSup_boostWeightSubmodule rep hx hy

@[simp]
lemma mem_subalgebra [IsBoostGraded rep] {i : Fin 3} {x : A} :
    x ∈ subalgebra rep i ↔ x ∈ ⨆ k, boostWeightSubmodule rep i k := Iff.rfl

/-- The decomposition into weight spaces is internal exactly when the homogeneous elements
  span; independence always holds. -/
theorem isInternal_iff :
    DirectSum.IsInternal (boostWeightSubmodule rep i) ↔ (⨆ k, boostWeightSubmodule rep i k) = ⊤ := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨And.right, fun h => ⟨boostWeightSubmodule_iSupIndep rep, h⟩⟩

/-- The homogeneous elements of a boost-graded representation span, along every axis. -/
theorem iSup_boostWeightSubmodule_eq_top [IsBoostGraded rep] : (⨆ k, boostWeightSubmodule rep i k) = ⊤ :=
  IsBoostGraded.weightSpan_eq_top (rep := rep) i

/-- **The boost weight grades the algebra.** For each axis the weight spaces decompose a
  boost-graded representation as an internal direct sum. -/
theorem boostWeightSubmodule_isInternal [IsBoostGraded rep] : DirectSum.IsInternal (boostWeightSubmodule rep i) :=
  (isInternal_iff rep).mpr (iSup_boostWeightSubmodule_eq_top rep)

/-- The decomposition into boost-weight components. -/
noncomputable instance [IsBoostGraded rep] (i : Fin 3) :
    DirectSum.Decomposition (boostWeightSubmodule rep i) :=
  (boostWeightSubmodule_isInternal rep (i := i)).chooseDecomposition

/-- **A boost-graded representation is a graded algebra along each axis.** -/
noncomputable instance [IsBoostGraded rep] (i : Fin 3) : GradedAlgebra (boostWeightSubmodule rep i) where
  one_mem := one_mem rep
  mul_mem _ _ _ _ hx hy := mul_mem rep hx hy

/-- The projection onto the part of boost weight `k` along the `i`-th axis, read off from the
  boost-weight decomposition. -/
noncomputable def boostProj [IsBoostGraded rep] (i : Fin 3) (k : ℤ) : A →ₗ[K] A :=
  (boostWeightSubmodule rep i k).subtype ∘ₗ
    DirectSum.component K ℤ (fun k => (boostWeightSubmodule rep i k : Submodule K A)) k ∘ₗ
      (DirectSum.decomposeLinearEquiv (boostWeightSubmodule rep i)).toLinearMap

variable [IsBoostGraded rep]

lemma boostProj_apply (i : Fin 3) (k : ℤ) (x : A) :
    boostProj rep i k x = (DirectSum.decompose (boostWeightSubmodule rep i) x k : A) := rfl

/-- The projection lands in the weight it projects onto. -/
lemma boostProj_mem (i : Fin 3) (k : ℤ) (x : A) : boostProj rep i k x ∈ boostWeightSubmodule rep i k :=
  (DirectSum.decompose (boostWeightSubmodule rep i) x k).2

/-- On an element of weight `k` the weight-`k` projection is the identity. -/
@[simp]
lemma boostProj_of_mem {k : ℤ} {x : A} (hx : x ∈ boostWeightSubmodule rep i k) : boostProj rep i k x = x :=
  DirectSum.decompose_of_mem_same _ hx

/-- On an element of another weight the projection vanishes. -/
lemma boostProj_of_mem_ne {k l : ℤ} {x : A} (hx : x ∈ boostWeightSubmodule rep i l) (hlk : l ≠ k) :
    boostProj rep i k x = 0 :=
  DirectSum.decompose_of_mem_ne _ hx hlk

/-- An element is of weight `k` exactly when the weight-`k` projection fixes it. -/
lemma boostProj_eq_self_iff {k : ℤ} {x : A} : boostProj rep i k x = x ↔ x ∈ boostWeightSubmodule rep i k :=
  ⟨fun h => h ▸ boostProj_mem rep i k x, boostProj_of_mem rep⟩

/-- The projections are idempotent. -/
@[simp]
lemma boostProj_boostProj (i : Fin 3) (k : ℤ) (x : A) :
    boostProj rep i k (boostProj rep i k x) = boostProj rep i k x :=
  boostProj_of_mem rep (boostProj_mem rep i k x)

/-- Distinct projections are orthogonal. -/
lemma boostProj_boostProj_of_ne {k l : ℤ} (hlk : l ≠ k) (x : A) :
    boostProj rep i k (boostProj rep i l x) = 0 :=
  boostProj_of_mem_ne rep (boostProj_mem rep i l x) hlk

/-- The image of the weight-`k` projection is the weight-`k` space. -/
lemma range_boostProj (i : Fin 3) (k : ℤ) : LinearMap.range (boostProj rep i k) = boostWeightSubmodule rep i k := by
  refine le_antisymm (LinearMap.range_le_iff_comap.mpr (le_top.antisymm fun x _ => ?_))
    fun x hx => ⟨x, boostProj_of_mem rep hx⟩
  exact boostProj_mem rep i k x

/-- The weight-`k` projection fixes a submodule of pure weight `k`. -/
lemma map_boostProj_of_le {k : ℤ} {W : Submodule K A} (h : W ≤ boostWeightSubmodule rep i k) :
    W.map (boostProj rep i k) = W := by
  refine le_antisymm ?_ fun x hx => ⟨x, hx, boostProj_of_mem rep (h hx)⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [boostProj_of_mem rep (h hx)]
  exact hx

/-- The weight-`k` projection annihilates a submodule of pure weight `l ≠ k`. -/
lemma map_boostProj_of_le_ne {k l : ℤ} {W : Submodule K A} (h : W ≤ boostWeightSubmodule rep i l)
    (hlk : l ≠ k) : W.map (boostProj rep i k) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [boostProj_of_mem_ne rep (h hx) hlk]
  exact zero_mem ⊥

/-- The submodule image of a projection is unchanged by projecting again. -/
lemma map_boostProj_idem (i : Fin 3) (k : ℤ) (X : Submodule K A) :
    (X.map (boostProj rep i k)).map (boostProj rep i k) = X.map (boostProj rep i k) :=
  map_boostProj_of_le rep (by rintro _ ⟨y, _, rfl⟩; exact boostProj_mem rep i k y)

/-- The weight-`k` part of a projection-closed submodule is its projection image. -/
lemma inf_boostWeightSubmodule_eq_map {k : ℤ} {X : Submodule K A} (h : X.map (boostProj rep i k) ≤ X) :
    boostWeightSubmodule rep i k ⊓ X = X.map (boostProj rep i k) := by
  refine le_antisymm (fun x hx => ⟨x, hx.2, boostProj_of_mem rep hx.1⟩) (le_inf ?_ h)
  rintro _ ⟨y, _, rfl⟩
  exact boostProj_mem rep i k y

/-- An operator shifting every boost weight by `k - l` carries the weight-`l` component to
  the weight-`k` component: the two sides agree on every homogeneous piece, and the pieces
  span. -/
lemma boostProj_comm {D : A →ₗ[K] A} (k l : ℤ)
    (hD : ∀ {w : ℤ} {y : A}, y ∈ boostWeightSubmodule rep i w → D y ∈ boostWeightSubmodule rep i (w + k - l))
    (x : A) : boostProj rep i k (D x) = D (boostProj rep i l x) := by
  have hx : x ∈ ⨆ m, boostWeightSubmodule rep i m := by rw [iSup_boostWeightSubmodule_eq_top rep]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem w y hyw =>
    have hd := hD hyw
    by_cases hwl : w = l
    · subst hwl
      rw [show w + k - w = k from by ring] at hd
      rw [boostProj_of_mem rep hd, boostProj_of_mem rep hyw]
    · rw [boostProj_of_mem_ne rep hyw hwl, map_zero,
        boostProj_of_mem_ne rep hd (show w + k - l ≠ k from by omega)]
  | zero => simp only [map_zero]
  | add y₁ y₂ _ _ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

/-- The weight-`k` part of a product of submodules is bounded by the products of the weight
  parts pairing to `k`. -/
lemma boostProj_map_mul_le (k : ℤ) (V W : Submodule K A) :
    (V * W).map (boostProj rep i k) ≤
    ⨆ (l : ℤ), (V.map (boostProj rep i l)) * (W.map (boostProj rep i (k - l))) := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  refine Submodule.mul_le.2 fun v hv w hw => ?_
  rw [Submodule.mem_comap, boostProj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
  refine sum_mem fun ij hij => ?_
  have hk : k - ij.1 = ij.2 := by
    have := (Finset.mem_filter.1 hij).2
    omega
  refine Submodule.mem_iSup_of_mem ij.1 ?_
  rw [hk]
  exact Submodule.mul_mem_mul ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩

/-- For submodules closed under the weight projections the bound of `boostProj_map_mul_le` is an
  equality. -/
lemma boostProj_map_mul (k : ℤ) {V W : Submodule K A}
    (hV : ∀ l : ℤ, V.map (boostProj rep i l) ≤ V) (hW : ∀ l : ℤ, W.map (boostProj rep i l) ≤ W) :
    (V * W).map (boostProj rep i k) =
    ⨆ (l : ℤ), (V.map (boostProj rep i l)) * (W.map (boostProj rep i (k - l))) := by
  refine le_antisymm (boostProj_map_mul_le rep k V W) (iSup_le fun l => ?_)
  refine Submodule.mul_le.2 fun v' hv' w' hw' => ?_
  refine ⟨v' * w', Submodule.mul_mem_mul (hV l hv') (hW (k - l) hw'), ?_⟩
  obtain ⟨v, hv, rfl⟩ := hv'
  obtain ⟨w, hw, rfl⟩ := hw'
  exact boostProj_of_mem rep (mul_mem' rep (boostProj_mem rep i l v) (boostProj_mem rep i (k - l) w)
    (by ring))

end Theory

/-!

## C. Weight decompositions of submodules

-/

/-- A **weight decomposition** of a submodule `V`: a finitely supported family of subspaces of
  pure boost weight whose supremum is `V`. Exhibiting one collapses all the per-span
  boilerplate: the projection images, the weight intersections, projection-closure and the
  off-support vanishing become the generic lemmas below. -/
structure WeightDecomposition (rep : Representation K SL(2,ℂ) M) (i : Fin 3)
    (V : Submodule K M) where
  /-- The weight-`k` piece of the decomposition. -/
  piece : ℤ → Submodule K M
  /-- The finite set of weights that occur. -/
  supp : Finset ℤ
  piece_le : ∀ k, piece k ≤ boostWeightSubmodule rep i k
  piece_eq_bot : ∀ k ∉ supp, piece k = ⊥
  iSup_piece : (⨆ k, piece k) = V

namespace WeightDecomposition

/-- Transport a weight decomposition along an equality of submodules. -/
def copy {rep : Representation K SL(2,ℂ) M} {i : Fin 3} {V₁ V₂ : Submodule K M}
    (d₁ : WeightDecomposition rep i V₁) (hV : V₁ = V₂) : WeightDecomposition rep i V₂ where
  piece := d₁.piece
  supp := d₁.supp
  piece_le := d₁.piece_le
  piece_eq_bot := d₁.piece_eq_bot
  iSup_piece := d₁.iSup_piece.trans hV

@[simp]
lemma copy_piece {rep : Representation K SL(2,ℂ) M} {i : Fin 3} {V₁ V₂ : Submodule K M}
    (d₁ : WeightDecomposition rep i V₁) (hV : V₁ = V₂) (k : ℤ) :
    (d₁.copy hV).piece k = d₁.piece k := rfl

/-- **The join of two weight decompositions** along the same axis: the weight-`k` piece of
  the join is the join of the weight-`k` pieces. -/
def sup {rep : Representation K SL(2,ℂ) M} {i : Fin 3} {V₁ V₂ : Submodule K M}
    (d₁ : WeightDecomposition rep i V₁) (d₂ : WeightDecomposition rep i V₂) :
    WeightDecomposition rep i (V₁ ⊔ V₂) where
  piece k := d₁.piece k ⊔ d₂.piece k
  supp := d₁.supp ∪ d₂.supp
  piece_le k := sup_le (d₁.piece_le k) (d₂.piece_le k)
  piece_eq_bot k hk := by
    rw [d₁.piece_eq_bot k fun hk' => hk (Finset.mem_union_left _ hk'),
      d₂.piece_eq_bot k fun hk' => hk (Finset.mem_union_right _ hk'), bot_sup_eq]
  iSup_piece := by rw [iSup_sup_eq, d₁.iSup_piece, d₂.iSup_piece]

@[simp]
lemma sup_piece {rep : Representation K SL(2,ℂ) M} {i : Fin 3} {V₁ V₂ : Submodule K M}
    (d₁ : WeightDecomposition rep i V₁) (d₂ : WeightDecomposition rep i V₂) (k : ℤ) :
    (d₁.sup d₂).piece k = d₁.piece k ⊔ d₂.piece k := rfl

variable {rep : Representation K SL(2,ℂ) A} [IsBoostGraded rep] {i : Fin 3}
  {V : Submodule K A} (d : WeightDecomposition rep i V)

include d

/-- Each piece sits inside the decomposed submodule. -/
lemma piece_le_self (k : ℤ) : d.piece k ≤ V :=
  le_of_le_of_eq (le_iSup d.piece k) d.iSup_piece

/-- The weight-`k` projection image of `V` is the weight-`k` piece. -/
lemma map_boostProj (k : ℤ) : V.map (boostProj rep i k) = d.piece k := by
  have h := congrArg (Submodule.map (boostProj rep i k)) d.iSup_piece
  rw [← h, Submodule.map_iSup]
  refine le_antisymm (iSup_le fun l => ?_)
    (le_iSup_of_le k (map_boostProj_of_le rep (d.piece_le k)).ge)
  by_cases hlk : l = k
  · subst hlk
    exact (map_boostProj_of_le rep (d.piece_le l)).le
  · rw [map_boostProj_of_le_ne rep (d.piece_le l) hlk]
    exact bot_le

/-- A decomposed submodule is closed under every weight projection. -/
lemma map_boostProj_le (k : ℤ) : V.map (boostProj rep i k) ≤ V := by
  rw [d.map_boostProj]
  exact d.piece_le_self k

/-- The weight-`k` part of a decomposed submodule is the weight-`k` piece. -/
lemma inf_eq (k : ℤ) : boostWeightSubmodule rep i k ⊓ V = d.piece k := by
  rw [inf_boostWeightSubmodule_eq_map rep (d.map_boostProj_le k), d.map_boostProj]

/-- Off the support the projection image vanishes. -/
lemma map_boostProj_of_notMem {k : ℤ} (h : k ∉ d.supp) :
    V.map (boostProj rep i k) = ⊥ := by
  rw [d.map_boostProj, d.piece_eq_bot k h]

/-- A projection-closed submodule whose projections vanish off a finite set is weight
  decomposed by its projection images. -/
noncomputable def ofMapClosed (rep : Representation K SL(2,ℂ) A) [IsBoostGraded rep]
    {i : Fin 3} {V : Submodule K A} (s : Finset ℤ)
    (hcl : ∀ k, V.map (boostProj rep i k) ≤ V)
    (hbot : ∀ k ∉ s, V.map (boostProj rep i k) = ⊥) :
    WeightDecomposition rep i V where
  piece k := V.map (boostProj rep i k)
  supp := s
  piece_le k := by
    rintro _ ⟨y, _, rfl⟩
    exact boostProj_mem rep i k y
  piece_eq_bot := hbot
  iSup_piece := by
    classical
    refine le_antisymm (iSup_le hcl) fun x hx => ?_
    rw [← DirectSum.sum_support_decompose (boostWeightSubmodule rep i) x]
    exact sum_mem fun k _ => Submodule.mem_iSup_of_mem k ⟨x, hx, rfl⟩

open scoped Pointwise in
/-- The convolution decomposition of a product of decomposed submodules. -/
noncomputable def mul {W : Submodule K A} (d₁ : WeightDecomposition rep i V)
    (d₂ : WeightDecomposition rep i W) : WeightDecomposition rep i (V * W) :=
  ofMapClosed rep (d₁.supp + d₂.supp)
    (fun k => by
      rw [boostProj_map_mul rep k d₁.map_boostProj_le d₂.map_boostProj_le]
      exact iSup_le fun l => Submodule.mul_le.2 fun a ha b hb =>
        Submodule.mul_mem_mul (d₁.map_boostProj_le l ha) (d₂.map_boostProj_le (k - l) hb))
    (fun k hk => by
      rw [boostProj_map_mul rep k d₁.map_boostProj_le d₂.map_boostProj_le]
      refine iSup_eq_bot.mpr fun l => ?_
      by_cases hl : l ∈ d₁.supp
      · rw [d₂.map_boostProj, d₂.piece_eq_bot (k - l)
          (fun hmem => hk (by simpa using Finset.add_mem_add hl hmem)), Submodule.mul_bot]
      · rw [d₁.map_boostProj, d₁.piece_eq_bot l hl, Submodule.bot_mul])

end WeightDecomposition

end BoostWeight

end Lorentz

end
