/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Star.StarAlgHom

/-!

# Local algebras of a system with a finite configuration space at each site

The algebra of operators of a finite region is the algebra of matrices on the configurations of
its sites, and a larger region contains it through `M ↦ M ⊗ 1`.

## i. Overview

Every site `s` of a system carries a finite set `Ω s`: the basis states of its local Hilbert
space, such as the two `σ^z` values of a spin, the occupation numbers of a fermion mode, or the
orbitals of an atom. A configuration of a finite region `X` assigns a value to each of its sites,
and the Hilbert space of the region is spanned by these configurations. This is the tensor
product of the local spaces. The operators of the region are the complex matrices indexed by its
configurations, a finite-dimensional C*-algebra, and the operators of a larger region `Y ⊇ X`
contain them as `M ↦ M ⊗ 1`: `M` acts on the sites of `X` and the identity on the others.
This is an injective unital `*`-homomorphism, compatible with composition.

The sites may be the sites of an infinite crystal, and the regions are its finite subsets, so
that the quasi-local algebra of the infinite system is the limit of the local ones. Only finite
site spaces are used.

## ii. Key results

- `Cfg` : the configurations of a region.
- `Alg` : the algebra of operators of a region.
- `inclStarAlg` : the inclusion `M ↦ M ⊗ 1` as a unital `*`-homomorphism.
- `inclMat_trans`, `inclMat_refl` : functoriality of the inclusions.

## iii. Table of contents

- A. Configurations of a region and gluing
- B. The operator `M ⊗ 1`

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 6.1.

-/

@[expose] public section

namespace CondensedMatter

namespace QuasiLocal

open scoped Matrix

variable {S : Type*} [DecidableEq S]
variable (Ω : S → Type*) [∀ s, Fintype (Ω s)] [∀ s, DecidableEq (Ω s)]

/-!

## A. Configurations of a region and gluing

-/

/-- The configurations of a region: a value of the local configuration space at each of its
sites. -/
abbrev Cfg (X : Finset S) : Type _ := (x : ↥X) → Ω x.1

variable {Ω}

/-- The restriction of a configuration of a region to a subregion. -/
abbrev restr {X Y : Finset S} (h : X ≤ Y) (c : Cfg Ω Y) : Cfg Ω X := fun x => c ⟨x.1, h x.2⟩

/-- Two configurations of a region agree outside a subregion. -/
def Agree {X Y : Finset S} (_h : X ≤ Y) (c c' : Cfg Ω Y) : Prop := ∀ y : ↥Y, y.1 ∉ X → c y = c' y

instance {X Y : Finset S} (h : X ≤ Y) (c c' : Cfg Ω Y) : Decidable (Agree h c c') := by
  unfold Agree; infer_instance

/-- Replace the values of `c` inside the subregion `X` by those of `a`. -/
def glue {X Y : Finset S} (_h : X ≤ Y) (c : Cfg Ω Y) (a : Cfg Ω X) : Cfg Ω Y :=
  fun y => if hy : y.1 ∈ X then a ⟨y.1, hy⟩ else c y

omit [∀ s, Fintype (Ω s)] in
omit [∀ s, DecidableEq (Ω s)] in
lemma restr_glue {X Y : Finset S} (h : X ≤ Y) (c : Cfg Ω Y) (a : Cfg Ω X) :
    restr h (glue h c a) = a := by
  funext x; simp [glue, x.2]

omit [∀ s, Fintype (Ω s)] in
omit [∀ s, DecidableEq (Ω s)] in
lemma agree_glue {X Y : Finset S} (h : X ≤ Y) (c : Cfg Ω Y) (a : Cfg Ω X) :
    Agree h c (glue h c a) := by
  intro y hy; simp [glue, hy]

omit [∀ s, Fintype (Ω s)] in
omit [∀ s, DecidableEq (Ω s)] in
lemma agree_iff_glue {X Y : Finset S} (h : X ≤ Y) {c c' : Cfg Ω Y} :
    Agree h c c' ↔ glue h c (restr h c') = c' := by
  constructor
  · intro hc
    funext y
    by_cases hy : y.1 ∈ X
    · simp [glue, hy]
    · simp [glue, hy, hc y hy]
  · intro hc y hy
    rw [← hc]; simp [glue, hy]

omit [DecidableEq S] in
omit [∀ s, Fintype (Ω s)] in
omit [∀ s, DecidableEq (Ω s)] in
lemma agree_refl {X Y : Finset S} (h : X ≤ Y) (c : Cfg Ω Y) : Agree h c c := fun _ _ => rfl

omit [DecidableEq S] in
omit [∀ s, Fintype (Ω s)] in
omit [∀ s, DecidableEq (Ω s)] in
lemma Agree.symm {X Y : Finset S} {h : X ≤ Y} {c c' : Cfg Ω Y} (hc : Agree h c c') :
    Agree h c' c := fun y hy => (hc y hy).symm

omit [DecidableEq S] in
omit [∀ s, Fintype (Ω s)] in
omit [∀ s, DecidableEq (Ω s)] in
lemma Agree.trans {X Y : Finset S} {h : X ≤ Y} {c c' c'' : Cfg Ω Y} (hc : Agree h c c')
    (hc' : Agree h c' c'') : Agree h c c'' := fun y hy => (hc y hy).trans (hc' y hy)

omit [∀ s, Fintype (Ω s)] in
omit [∀ s, DecidableEq (Ω s)] in
lemma eq_of_agree_of_restr_eq {X Y : Finset S} {h : X ≤ Y} {c c' : Cfg Ω Y} (hc : Agree h c c')
    (hr : restr h c = restr h c') : c = c' := by
  funext y
  by_cases hy : y.1 ∈ X
  · exact congrFun hr ⟨y.1, hy⟩
  · exact hc y hy

/-!

## B. The operator `M ⊗ 1`

-/

variable (Ω) in
/-- The operators on the sites of a region: matrices indexed by configurations. -/
abbrev Alg (X : Finset S) : Type _ := Matrix (Cfg Ω X) (Cfg Ω X) ℂ

/-- The operator `M ⊗ 1` on a larger region: `M` on the sites of `X` and the identity on the other
sites. -/
def inclMat {X Y : Finset S} (h : X ≤ Y) (M : Alg Ω X) : Alg Ω Y :=
  Matrix.of fun c c' => if Agree h c c' then M (restr h c) (restr h c') else 0

omit [∀ s, Fintype (Ω s)] in
lemma inclMat_apply {X Y : Finset S} (h : X ≤ Y) (M : Alg Ω X) (c c' : Cfg Ω Y) :
    inclMat h M c c' = if Agree h c c' then M (restr h c) (restr h c') else 0 := rfl

omit [∀ s, Fintype (Ω s)] in
lemma inclMat_one {X Y : Finset S} (h : X ≤ Y) : inclMat h (1 : Alg Ω X) = 1 := by
  ext c c'
  simp only [inclMat_apply, Matrix.one_apply]
  by_cases hc : Agree h c c'
  · by_cases hr : restr h c = restr h c'
    · obtain rfl := eq_of_agree_of_restr_eq hc hr
      simp [hc]
    · have : c ≠ c' := fun e => hr (by rw [e])
      simp [hc, hr, this]
  · have : c ≠ c' := fun e => hc (e ▸ agree_refl h c)
    simp [hc, this]

omit [∀ s, Fintype (Ω s)] in
lemma inclMat_add {X Y : Finset S} (h : X ≤ Y) (M N : Alg Ω X) :
    inclMat h (M + N) = inclMat h M + inclMat h N := by
  ext c c'; simp only [inclMat_apply, Matrix.add_apply]; split_ifs <;> simp

omit [∀ s, Fintype (Ω s)] in
lemma inclMat_smul {X Y : Finset S} (h : X ≤ Y) (r : ℂ) (M : Alg Ω X) :
    inclMat h (r • M) = r • inclMat h M := by
  ext c c'; simp only [inclMat_apply, Matrix.smul_apply]; split_ifs <;> simp

omit [∀ s, Fintype (Ω s)] in
lemma inclMat_conjTranspose {X Y : Finset S} (h : X ≤ Y) (M : Alg Ω X) :
    inclMat h Mᴴ = (inclMat h M)ᴴ := by
  ext c c'
  simp only [inclMat_apply, Matrix.conjTranspose_apply]
  by_cases hc : Agree h c c'
  · simp [hc, hc.symm]
  · have h2 : ¬Agree h c' c := fun h' => hc h'.symm
    simp [hc, h2]

lemma inclMat_mul {X Y : Finset S} (h : X ≤ Y) (M N : Alg Ω X) :
    inclMat h (M * N) = inclMat h M * inclMat h N := by
  ext c c''
  rw [Matrix.mul_apply]
  -- the terms of the sum vanish unless the intermediate configuration agrees with `c`
  set f : Cfg Ω Y → ℂ := fun c' => inclMat h M c c' * inclMat h N c' c'' with hf
  have hsum : ∑ c', f c' = ∑ a : Cfg Ω X, f (glue h c a) := by
    refine Finset.sum_bij_ne_zero (fun c' _ _ => restr h c') (fun _ _ _ => Finset.mem_univ _)
      ?_ ?_ ?_
    · intro c₁ _ h₁ c₂ _ h₂ hr
      have a₁ : Agree h c c₁ := by
        by_contra hc; apply h₁; simp [hf, inclMat_apply, hc]
      have a₂ : Agree h c c₂ := by
        by_contra hc; apply h₂; simp [hf, inclMat_apply, hc]
      exact eq_of_agree_of_restr_eq (a₁.symm.trans a₂) hr
    · intro a _ ha
      exact ⟨glue h c a, Finset.mem_univ _, ha, restr_glue h c a⟩
    · intro c' _ h'
      have hc : Agree h c c' := by
        by_contra hc; apply h'; simp [hf, inclMat_apply, hc]
      rw [(agree_iff_glue h).1 hc]
  rw [hsum]
  have hterm : ∀ a, f (glue h c a)
      = if Agree h c c'' then M (restr h c) a * N a (restr h c'') else 0 := by
    intro a
    have hag : Agree h c (glue h c a) := agree_glue h c a
    simp only [hf, inclMat_apply, hag, ↓reduceIte, restr_glue]
    by_cases hc : Agree h c c''
    · have : Agree h (glue h c a) c'' := hag.symm.trans hc
      simp [hc, this]
    · have : ¬Agree h (glue h c a) c'' := fun h' => hc (hag.trans h')
      simp [hc, this]
  simp only [hterm, inclMat_apply, Matrix.mul_apply]
  split_ifs <;> simp

omit [∀ s, Fintype (Ω s)] in
lemma inclMat_refl {X : Finset S} (M : Alg Ω X) : inclMat (le_refl X) M = M := by
  ext c c'
  have hc : Agree (le_refl X) c c' := fun y hy => absurd y.2 hy
  simp [inclMat_apply, hc]

omit [∀ s, Fintype (Ω s)] in
omit [∀ s, DecidableEq (Ω s)] in
lemma agree_trans_iff {X Y Z : Finset S} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (c c' : Cfg Ω Z) :
    Agree (h₁.trans h₂) c c' ↔ Agree h₂ c c' ∧ Agree h₁ (restr h₂ c) (restr h₂ c') := by
  constructor
  · intro hc
    exact ⟨fun z hz => hc z (fun hx => hz (h₁ hx)), fun y hy => hc ⟨y.1, h₂ y.2⟩ hy⟩
  · rintro ⟨hc, hc'⟩ z hz
    by_cases hy : z.1 ∈ Y
    · exact hc' ⟨z.1, hy⟩ hz
    · exact hc z hy

omit [∀ s, Fintype (Ω s)] in
lemma inclMat_trans {X Y Z : Finset S} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (M : Alg Ω X) :
    inclMat (h₁.trans h₂) M = inclMat h₂ (inclMat h₁ M) := by
  ext c c'
  by_cases h2 : Agree h₂ c c'
  · by_cases h1 : Agree h₁ (restr h₂ c) (restr h₂ c')
    · have h : Agree (h₁.trans h₂) c c' := (agree_trans_iff h₁ h₂ c c').2 ⟨h2, h1⟩
      simp [inclMat_apply, h, h1, h2]
    · have h : ¬Agree (h₁.trans h₂) c c' := fun h => h1 ((agree_trans_iff h₁ h₂ c c').1 h).2
      simp [inclMat_apply, h, h1, h2]
  · have h : ¬Agree (h₁.trans h₂) c c' := fun h => h2 ((agree_trans_iff h₁ h₂ c c').1 h).1
    simp [inclMat_apply, h, h2]

/-- The operator `M ⊗ 1` as a unital `*`-homomorphism. -/
def inclStarAlg {X Y : Finset S} (h : X ≤ Y) : Alg Ω X →⋆ₐ[ℂ] Alg Ω Y where
  toFun := inclMat h
  map_one' := inclMat_one h
  map_mul' := inclMat_mul h
  map_zero' := by ext c c'; simp [inclMat_apply]
  map_add' := inclMat_add h
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    rw [← inclMat_one h]; exact inclMat_smul h r 1
  map_star' := inclMat_conjTranspose h


end QuasiLocal

end CondensedMatter
