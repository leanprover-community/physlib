/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.MomentumSectors
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!

# Bloch's theorem on the lattice

A translation-invariant evolution of configurations of unit cells acts through its Bloch matrix.

## i. Overview

Consider degrees of freedom attached to the cells of a lattice whose translation group is `Λ`,
an abelian group such as `ℤ ^ d`. The contents of one unit cell, orbitals or spin components, form
a module `M`, and a configuration is a finitely supported assignment of an element of `M` to each
cell: `ψ : Λ →₀ M`. Translation acts by `(T a ψ) m = ψ (m - a)`. A crystal momentum is a character
`χ` of `Λ`, and the Fourier transform of a configuration is `ev χ ψ = ∑ m, χ m • ψ m`.

* The kernel of the Fourier transform is precisely the span that defines the momentum fiber. So the
  fiber at momentum `χ` is a copy of the unit cell `M`: Bloch's reduction to a single cell.
* Every translation-invariant linear map `D` satisfies `ev χ (D ψ) = H(k) (ev χ ψ)` for a matrix
  `H(k)` on the unit cell, its *Bloch matrix*. No finite-range assumption is needed, as a
  configuration has finite support, and the matrix is `H(k) v = ∑ m, χ m • (D (δ₀ v)) m`.
* The Bloch matrix of a product is the product of Bloch matrices, and of the inverse the inverse.
* A hopping Hamiltonian with amplitude `t n` to the cell displaced by `n` has
  `H(k) = ∑ n, exp (i k n) t n`: the Fourier transform of its hoppings.

No analysis, finite dimensionality or positivity is used. The analytic counterpart on `ℓ²` is in
`RegularRep` and `Spectrum`, and the finite periodic crystal in `FiniteBloch`.

## ii. Key results

- `translation` : translating a configuration of unit cells.
- `ev` : the Fourier transform of a configuration at a crystal momentum.
- `ker_ev` : the kernel of the Fourier transform defines the momentum fiber.
- `fiberEquiv` : the fiber at momentum `χ` is the contents of a unit cell.
- `symbol` : the Bloch matrix of a translation-invariant map.
- `ev_apply` : Bloch's theorem, Fourier transform intertwines the map and its Bloch matrix.
- `symbol_comp`, `symbol_id`, `isUnit_symbol` : the Bloch matrix of a product and of an inverse.
- `hopping`, `symbol_hopping` : the Bloch Hamiltonian of a hopping model.

## iii. Table of contents

- A. Translations and Fourier evaluation
- B. The momentum fiber is the unit cell
- C. Bloch matrices
- D. Hopping operators

## iv. References

* F. Bloch, Über die Quantenmechanik der Elektronen in Kristallgittern, Z. Phys. 52 (1929). [ref:
  bloch_1929]
* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 8.

-/

@[expose] public section

namespace CondensedMatter

namespace Bloch

open ProbabilisticTheory.Representation

variable {Λ K M : Type*} [AddCommGroup Λ] [CommRing K] [AddCommGroup M] [Module K M]

/-!

## A. Translations and Fourier evaluation

-/

/-- Translation of finitely supported configurations: `(T a ψ) m = ψ (m - a)`. -/
noncomputable def translation : Multiplicative Λ →* Module.End K (Λ →₀ M) where
  toFun a := Finsupp.lmapDomain M K (· + Multiplicative.toAdd a)
  map_one' := LinearMap.ext fun ψ => by
    have : (fun m : Λ => m + Multiplicative.toAdd (1 : Multiplicative Λ)) = id := by
      funext m; simp
    show Finsupp.mapDomain (fun m : Λ => m + Multiplicative.toAdd (1 : Multiplicative Λ)) ψ = ψ
    rw [this]; exact Finsupp.mapDomain_id
  map_mul' a b := LinearMap.ext fun ψ => by
    show Finsupp.mapDomain (fun m : Λ => m + Multiplicative.toAdd (a * b)) ψ
      = Finsupp.mapDomain (fun m : Λ => m + Multiplicative.toAdd a)
          (Finsupp.mapDomain (fun m : Λ => m + Multiplicative.toAdd b) ψ)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext m
    simp only [Function.comp, toAdd_mul]
    abel

lemma translation_single (a : Multiplicative Λ) (m : Λ) (v : M) :
    translation (K := K) a (Finsupp.single m v)
      = Finsupp.single (m + Multiplicative.toAdd a) v := by
  simp [translation, Finsupp.mapDomain_single]

/-- A character `χ` of `Λ`, viewed as a function on the multiplicative group of translations. -/
def charFun (χ : AddChar Λ K) : Multiplicative Λ → K := fun g => χ (Multiplicative.toAdd g)

/-- Fourier evaluation at the character `χ`: `ev χ ψ = ∑ m, χ m • ψ m`. -/
noncomputable def ev (χ : AddChar Λ K) : (Λ →₀ M) →ₗ[K] M :=
  Finsupp.lsum K fun m => χ m • (LinearMap.id : M →ₗ[K] M)

@[simp] lemma ev_single (χ : AddChar Λ K) (m : Λ) (v : M) :
    ev χ (Finsupp.single m v) = χ m • v := by
  simp [ev]

lemma ev_translation (χ : AddChar Λ K) (a : Multiplicative Λ) (ψ : Λ →₀ M) :
    ev χ (translation (K := K) a ψ) = charFun χ a • ev χ ψ := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, smul_add]
  | single m v =>
    simp only [translation_single, charFun, AddChar.map_add_eq_mul, ev_single, mul_smul]
    exact smul_comm _ _ _

lemma ev_single_zero (χ : AddChar Λ K) (v : M) : ev χ (Finsupp.single 0 v) = v := by simp

lemma ev_surjective (χ : AddChar Λ K) : Function.Surjective (ev (M := M) χ) :=
  fun v => ⟨Finsupp.single 0 v, ev_single_zero χ v⟩

/-!

## B. The momentum fiber is the unit cell

-/

/-- Every configuration is congruent, modulo the fiber relations, to its Fourier evaluation
placed in the origin cell. -/
lemma sub_single_ev_mem_cobound (χ : AddChar Λ K) (ψ : Λ →₀ M) :
    ψ - Finsupp.single 0 (ev χ ψ)
      ∈ cobound (translation (K := K) (Λ := Λ) (M := M)) (charFun χ) := by
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have := Submodule.add_mem _ hf hg
    convert this using 1
    simp only [map_add, Finsupp.single_add]
    abel
  | single m v =>
    have h := sub_smul_mem_cobound (translation (K := K) (Λ := Λ) (M := M)) (charFun χ)
      (Multiplicative.ofAdd m) (Finsupp.single 0 v)
    simpa [translation_single, charFun, Finsupp.smul_single] using h

/-- The kernel of Fourier evaluation is exactly the span defining the momentum fiber. -/
lemma ker_ev (χ : AddChar Λ K) :
    LinearMap.ker (ev (M := M) χ)
      = cobound (translation (K := K) (Λ := Λ) (M := M)) (charFun χ) := by
  apply le_antisymm
  · intro ψ hψ
    have := sub_single_ev_mem_cobound χ ψ
    rwa [LinearMap.mem_ker.1 hψ, Finsupp.single_zero, sub_zero] at this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨g, v, rfl⟩
    simp [ev_translation]

/-- The momentum fiber of the translation action at `χ` is canonically the unit-cell space
`M`. -/
noncomputable def fiberEquiv (χ : AddChar Λ K) :
    Fiber (translation (K := K) (Λ := Λ) (M := M)) (charFun χ) ≃ₗ[K] M :=
  (Submodule.quotEquivOfEq _ _ (ker_ev χ).symm).trans
    (LinearMap.quotKerEquivOfSurjective (ev χ) (ev_surjective χ))

@[simp] lemma fiberEquiv_mk (χ : AddChar Λ K) (ψ : Λ →₀ M) :
    fiberEquiv χ (Fiber.mk (translation (K := K)) (charFun χ) ψ) = ev χ ψ := by
  simp [fiberEquiv, Fiber.mk]

/-!

## C. Bloch matrices

-/

/-- The Bloch matrix of a linear map `D` at the character `χ`: apply `D` to the unit cell at the
origin and Fourier-evaluate. -/
noncomputable def symbol (χ : AddChar Λ K) (D : (Λ →₀ M) →ₗ[K] (Λ →₀ M)) :
    M →ₗ[K] M :=
  ev χ ∘ₗ D ∘ₗ Finsupp.lsingle 0

lemma symbol_apply (χ : AddChar Λ K) (D : (Λ →₀ M) →ₗ[K] (Λ →₀ M)) (v : M) :
    symbol χ D v = ev χ (D (Finsupp.single 0 v)) := rfl

/-- **Bloch theorem.** Fourier evaluation intertwines a translation-equivariant linear map with
its Bloch matrix. -/
lemma ev_apply {D : (Λ →₀ M) →ₗ[K] (Λ →₀ M)}
    (hD : IsEquivariant (translation (K := K)) (translation (K := K)) D)
    (χ : AddChar Λ K) (ψ : Λ →₀ M) : ev χ (D ψ) = symbol χ D (ev χ ψ) := by
  have h1 := hD.cobound_le_comap (charFun χ) (sub_single_ev_mem_cobound χ ψ)
  rw [← ker_ev, Submodule.mem_comap, LinearMap.mem_ker] at h1
  simp only [map_sub] at h1
  exact sub_eq_zero.1 h1

/-- The Bloch matrix of the identity is the identity. -/
@[simp] lemma symbol_id (χ : AddChar Λ K) :
    symbol χ (LinearMap.id : (Λ →₀ M) →ₗ[K] _) = .id := by
  ext v : 1; simp [symbol_apply]

/-- The Bloch matrix is multiplicative: only the left factor needs to be equivariant. -/
lemma symbol_comp {D₁ D₂ : (Λ →₀ M) →ₗ[K] (Λ →₀ M)}
    (h₁ : IsEquivariant (translation (K := K)) (translation (K := K)) D₁)
    (χ : AddChar Λ K) : symbol χ (D₁ ∘ₗ D₂) = symbol χ D₁ ∘ₗ symbol χ D₂ := by
  ext v : 1
  calc symbol χ (D₁ ∘ₗ D₂) v = ev χ (D₁ (D₂ (Finsupp.single 0 v))) := rfl
    _ = symbol χ D₁ (ev χ (D₂ (Finsupp.single 0 v))) := ev_apply h₁ χ _
    _ = (symbol χ D₁ ∘ₗ symbol χ D₂) v := rfl

/-- The Bloch matrix is additive. -/
lemma symbol_add (χ : AddChar Λ K) (D₁ D₂ : (Λ →₀ M) →ₗ[K] (Λ →₀ M)) :
    symbol χ (D₁ + D₂) = symbol χ D₁ + symbol χ D₂ := by
  ext v : 1; simp [symbol_apply]

/-- If an equivariant map is invertible by an equivariant map, its Bloch matrix is invertible a
every momentum. -/
lemma isUnit_symbol {D E : (Λ →₀ M) →ₗ[K] (Λ →₀ M)}
    (hD : IsEquivariant (translation (K := K)) (translation (K := K)) D)
    (hE : IsEquivariant (translation (K := K)) (translation (K := K)) E)
    (h₁ : D ∘ₗ E = LinearMap.id) (h₂ : E ∘ₗ D = LinearMap.id) (χ : AddChar Λ K) :
    IsUnit (symbol χ D) := by
  refine ⟨⟨symbol χ D, symbol χ E, ?_, ?_⟩, rfl⟩
  · show symbol χ D ∘ₗ symbol χ E = LinearMap.id
    rw [← symbol_comp hD, h₁, symbol_id]
  · show symbol χ E ∘ₗ symbol χ D = LinearMap.id
    rw [← symbol_comp hE, h₂, symbol_id]

/-!

## D. Hopping operators

-/

/-- One hopping term: apply `Hn` in each cell, then translate by `n`. -/
noncomputable def hop (n : Λ) (Hn : M →ₗ[K] M) : (Λ →₀ M) →ₗ[K] (Λ →₀ M) :=
  translation (Multiplicative.ofAdd n) ∘ₗ Finsupp.mapRange.linearMap Hn

/-- A finite-range hopping operator with hopping matrices `H n : M → M`:
`(hopping H ψ) m = ∑ n, H n (ψ (m - n))`. -/
noncomputable def hopping (H : Λ →₀ (M →ₗ[K] M)) : (Λ →₀ M) →ₗ[K] (Λ →₀ M) :=
  H.sum hop

lemma isEquivariant_hop (n : Λ) (Hn : M →ₗ[K] M) :
    IsEquivariant (translation (K := K)) (translation (K := K)) (hop n Hn) := by
  intro g ψ
  induction ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m v =>
    simp [hop, translation_single, add_assoc]
    congr 1
    abel

lemma isEquivariant_hopping (H : Λ →₀ (M →ₗ[K] M)) :
    IsEquivariant (translation (K := K)) (translation (K := K)) (hopping H) := by
  intro g ψ
  simp only [hopping, Finsupp.sum, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun n _ => isEquivariant_hop n (H n) g ψ

/-- **Bloch Hamiltonian.** The Bloch matrix of a hopping operator is `∑ n, χ n • H n`. -/
lemma symbol_hopping (χ : AddChar Λ K) (H : Λ →₀ (M →ₗ[K] M)) :
    symbol χ (hopping H) = H.sum fun n Hn => χ n • Hn := by
  ext v : 1
  simp [symbol_apply, hopping, hop, Finsupp.sum, translation_single]

end Bloch

end CondensedMatter
