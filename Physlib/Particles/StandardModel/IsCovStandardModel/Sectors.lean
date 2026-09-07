/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.MassWeight
/-!
# The sectors of the field algebra

Each covariant generator belongs to one of three classes — gauge, Higgs or fermion —
and a word in the generators realises a set of classes. The sector of a class set `S`
is the non-unital subalgebra spanned by the words realising exactly `S`; the sectors
exhaust the field algebra and are preserved by the gauge and Lorentz actions.

Refining by the mass weight, `sectorMassWeight S w` is the span of the words
realising `S` of total weight `w`; it is exactly the intersection of the sector with
the mass-weight submodule (`sectorMassWeight_eq_inf`), and for each weight `w` the
mass-weight submodule decomposes as the join of the sectors' weight-`w` parts
(`massWeightSubmodule_eq_iSup_sectorMassWeight`).

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz


namespace IsCovStandardModel

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare)
/-!

## The different sectors of the Standard Model

Each covariant generator belongs to one of three classes — gauge, Higgs or fermion —
and a word in the generators realises a set of classes. The sector of a class set `S`
is spanned by the words realising exactly `S`. It contains no non-zero scalar, since
the empty word realises no class at all, and it is closed under multiplication because
`S ∪ S = S`: it is a non-unital subalgebra. The seven non-empty class sets give the
seven sectors below.

-/

/-- The span of the words in the covariant generators realising exactly the classes
  `S`. -/
def sectorSubmodule (S : Finset GeneratorClass) : Submodule ℂ B :=
  Submodule.span ℂ
    {x | ∃ gl : List Generators, wordClasses gl = S ∧ (gl.map h.generatorVal).prod = x}

/-- Multiplication carries the class spans of `S` and `T` into that of `S ∪ T`. -/
lemma mul_mem_sectorSubmodule {S T : Finset GeneratorClass} {x y : B}
    (hx : x ∈ h.sectorSubmodule S) (hy : y ∈ h.sectorSubmodule T) :
    x * y ∈ h.sectorSubmodule (S ∪ T) := by
  induction hx using Submodule.span_induction with
  | mem x hxw =>
    obtain ⟨gl, hgl, rfl⟩ := hxw
    induction hy using Submodule.span_induction with
    | mem y hyw =>
      obtain ⟨gl', hgl', rfl⟩ := hyw
      refine Submodule.subset_span ⟨gl ++ gl', ?_, ?_⟩
      · rw [wordClasses_append, hgl, hgl']
      · rw [List.map_append, List.prod_append]
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b ha hb iha ihb => rw [mul_add]; exact Submodule.add_mem _ iha ihb
    | smul c a ha iha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ iha
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b ha hb iha ihb => rw [add_mul]; exact Submodule.add_mem _ iha ihb
  | smul c a ha iha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ iha

/-- The sector realising exactly the classes `S`: the span of the words whose
  generators realise `S`. It is a non-unital subalgebra — closed under multiplication
  since `S ∪ S = S`, but containing no non-zero scalar, since the empty word realises
  no class. -/
def sector (S : Finset GeneratorClass) : NonUnitalSubalgebra ℂ B :=
  (h.sectorSubmodule S).toNonUnitalSubalgebra fun x y hx hy => by
    have hxy := h.mul_mem_sectorSubmodule hx hy
    rwa [Finset.union_self] at hxy

@[simp]
lemma mem_sector {S : Finset GeneratorClass} {x : B} :
    x ∈ h.sector S ↔ x ∈ h.sectorSubmodule S := Iff.rfl

/-- A word lies in the sector of the classes it realises. -/
lemma list_prod_mem_sector (gl : List Generators) :
    (gl.map h.generatorVal).prod ∈ h.sector (wordClasses gl) :=
  Submodule.subset_span ⟨gl, rfl, rfl⟩

/-- Multiplication carries the sectors of `S` and `T` into the sector of `S ∪ T`. -/
lemma mul_mem_sector {S T : Finset GeneratorClass} {x y : B}
    (hx : x ∈ h.sector S) (hy : y ∈ h.sector T) : x * y ∈ h.sector (S ∪ T) :=
  h.mul_mem_sectorSubmodule hx hy

/-- Every sector sits inside the field algebra. -/
lemma mem_fieldAlgebra_of_mem_sector {S : Finset GeneratorClass} {x : B}
    (hx : x ∈ h.sector S) : x ∈ h.fieldAlgebra := by
  rw [mem_sector, sectorSubmodule] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨gl, -, rfl⟩ := hy
    refine Subalgebra.list_prod_mem _ fun z hz => ?_
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp hz
    exact h.generatorVal_mem_fieldAlgebra g
  | zero => exact Subalgebra.zero_mem _
  | add a b ha hb iha ihb => exact Subalgebra.add_mem _ iha ihb
  | smul c a ha iha => exact Subalgebra.smul_mem _ iha c

/-- **The sectors exhaust the field algebra**: every element of the field algebra is a
  sum of elements of the sectors, since every word realises exactly one class set. The
  unit is supplied by `sector ∅`, the sector of the empty word, so the join is the
  whole of `fieldAlgebra` — read as a non-unital subalgebra, the two sides having
  otherwise different types. -/
lemma fieldAlgebra_eq_iSup_sector :
    h.fieldAlgebra.toNonUnitalSubalgebra = ⨆ S : Finset GeneratorClass, h.sector S := by
  refine le_antisymm ?_ (iSup_le fun S => ?_)
  · intro x hx
    rw [Subalgebra.mem_toNonUnitalSubalgebra, h.fieldAlgebra_eq_adjoin_range,
      ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l₀, hl₀, rfl⟩ := Submonoid.exists_list_of_mem_closure hy
      obtain ⟨gl, rfl⟩ := h.exists_list_map_eq l₀ hl₀
      exact le_iSup (fun S : Finset GeneratorClass => h.sector S) (wordClasses gl)
        (h.list_prod_mem_sector gl)
    | zero => exact zero_mem _
    | add a b ha hb iha ihb => exact add_mem iha ihb
    | smul c a ha iha => exact SMulMemClass.smul_mem c iha
  · intro x hx
    exact Subalgebra.mem_toNonUnitalSubalgebra.mpr (h.mem_fieldAlgebra_of_mem_sector hx)


/-!

### The sectors are preserved by the gauge and Lorentz actions

Both actions carry a covariant tower into combinations of towers of the same
species, hence each generator into the sector of its own class, hence — word by
word — each sector into itself.

-/

/-- Any Higgs tower symbol lies in the Higgs sector. -/
lemma H_mem_sector {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ HiggsVec) : H l φ ∈ h.sector {GeneratorClass.higgs} := by
  rw [← HiggsVec.orthonormBasis.toBasis.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.H n l j]

/-- Any conjugate-Higgs tower symbol lies in the Higgs sector. -/
lemma barH_mem_sector {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) :
    barH l φ ∈ h.sector {GeneratorClass.higgs} := by
  rw [← HiggsVec.orthonormBasis.toBasis.conj.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.barH n l j]

/-- Any field-strength tower symbol lies in the gauge sector. -/
lemma F_mem_sector {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : F l μ ν φ ∈ h.sector {GeneratorClass.gauge} := by
  rw [← GaugeAlgebra.stdBasis.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => ?_
  rw [← algebraMap_smul ℂ (φ (GaugeAlgebra.stdBasis j))]
  refine SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.F n l μ ν j]

/-- Any `d` tower symbol lies in the fermion sector. -/
lemma d_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ DownSinglet) : d i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← DownSinglet.basis.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.d i n l j]

/-- Any `bard` tower symbol lies in the fermion sector. -/
lemma bard_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) : bard i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← DownSinglet.basis.conj.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.bard i n l j]

/-- Any `u` tower symbol lies in the fermion sector. -/
lemma u_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ UpSinglet) : u i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← UpSinglet.basis.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.u i n l j]

/-- Any `baru` tower symbol lies in the fermion sector. -/
lemma baru_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) : baru i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← UpSinglet.basis.conj.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.baru i n l j]

/-- Any `Q` tower symbol lies in the fermion sector. -/
lemma Q_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ QuarkDoublet) : Q i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← QuarkDoublet.basis.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.Q i n l j]

/-- Any `barQ` tower symbol lies in the fermion sector. -/
lemma barQ_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) : barQ i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← QuarkDoublet.basis.conj.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.barQ i n l j]

/-- Any `L` tower symbol lies in the fermion sector. -/
lemma L_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ LeptonDoublet) : L i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← LeptonDoublet.basis.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.L i n l j]

/-- Any `barL` tower symbol lies in the fermion sector. -/
lemma barL_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) : barL i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← LeptonDoublet.basis.conj.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.barL i n l j]

/-- Any `e` tower symbol lies in the fermion sector. -/
lemma e_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ LeptonSinglet) : e i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← LeptonSinglet.basis.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.e i n l j]

/-- Any `bare` tower symbol lies in the fermion sector. -/
lemma bare_mem_sector (i : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) : bare i l φ ∈ h.sector {GeneratorClass.fermion} := by
  rw [← LeptonSinglet.basis.conj.sum_dual_apply_smul_coord φ]
  simp only [map_sum, map_smul]
  refine sum_mem fun j _ => SMulMemClass.smul_mem _ ?_
  simpa [generatorVal, wordClasses, Generators.kind] using
    h.list_prod_mem_sector [Generators.bare i n l j]

/-- The gauge action carries a covariant generator into the sector of its class. -/
lemma repGauge_generatorVal_mem_sector (g : GaugeGroupI) (a : Generators) :
    repGauge g (h.generatorVal a) ∈ h.sector {a.kind} := by
  cases a with
  | H n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isHiggsSector.H_equivariant g _ n l]
    exact h.H_mem_sector l _
  | barH n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isHiggsSector.barH_equivariant g _ n l]
    exact h.barH_mem_sector l _
  | F n l μ ν j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isGaugeSector.repGauge_F g l μ ν _]
    exact h.F_mem_sector l μ ν _
  | d i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_d g i l _]
    exact h.d_mem_sector i l _
  | bard i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_bard g i l _]
    exact h.bard_mem_sector i l _
  | u i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_u g i l _]
    exact h.u_mem_sector i l _
  | baru i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_baru g i l _]
    exact h.baru_mem_sector i l _
  | Q i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_Q g i l _]
    exact h.Q_mem_sector i l _
  | barQ i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_barQ g i l _]
    exact h.barQ_mem_sector i l _
  | L i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_L g i l _]
    exact h.L_mem_sector i l _
  | barL i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_barL g i l _]
    exact h.barL_mem_sector i l _
  | e i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_e g i l _]
    exact h.e_mem_sector i l _
  | bare i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repGauge_bare g i l _]
    exact h.bare_mem_sector i l _

/-- The Lorentz action carries a covariant generator into the sector of its
  class. -/
lemma repLorentz_generatorVal_mem_sector (Λ : SL(2,ℂ)) (a : Generators) :
    repLorentz Λ (h.generatorVal a) ∈ h.sector {a.kind} := by
  cases a with
  | H n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isHiggsSector.repLorentz_H Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.H_mem_sector p _)
  | barH n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isHiggsSector.repLorentz_barH Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.barH_mem_sector p _)
  | F n l μ ν j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isGaugeSector.repLorentz_F Λ n l μ ν _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _
      (sum_mem fun a _ => SMulMemClass.smul_mem _
        (sum_mem fun b _ => SMulMemClass.smul_mem _ (h.F_mem_sector p a b _)))
  | d i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_d i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.d_mem_sector i p _)
  | bard i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_bard i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.bard_mem_sector i p _)
  | u i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_u i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.u_mem_sector i p _)
  | baru i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_baru i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.baru_mem_sector i p _)
  | Q i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_Q i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.Q_mem_sector i p _)
  | barQ i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_barQ i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.barQ_mem_sector i p _)
  | L i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_L i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.L_mem_sector i p _)
  | barL i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_barL i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.barL_mem_sector i p _)
  | e i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_e i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.e_mem_sector i p _)
  | bare i n l j =>
    simp only [generatorVal, Generators.kind]
    rw [h.isFermionSector.repLorentz_bare i Λ n l _]
    exact sum_mem fun p _ => SMulMemClass.smul_mem _ (h.bare_mem_sector i p _)

/-- The action `repGauge` preserves every sector. -/
lemma repGauge_mem_sector {S : Finset GeneratorClass} {x : B} (g : GaugeGroupI)
    (hx : x ∈ h.sector S) : repGauge g x ∈ h.sector S := by
  rw [mem_sector, sectorSubmodule] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨gl, hgl, rfl⟩ := hy
    subst hgl
    induction gl with
    | nil =>
      simp only [List.map_nil, List.prod_nil]
      rw [h.repGauge_one g]
      simpa using h.list_prod_mem_sector ([] : List Generators)
    | cons a t ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [h.repGauge_mul g, wordClasses_cons, ← Finset.singleton_union]
      exact h.mul_mem_sector (h.repGauge_generatorVal_mem_sector g a) ih
  | zero => rw [map_zero]; exact zero_mem _
  | add a b ha hb iha ihb => rw [map_add]; exact add_mem iha ihb
  | smul c a ha iha => rw [map_smul]; exact SMulMemClass.smul_mem _ iha

/-- The action `repLorentz` preserves every sector. -/
lemma repLorentz_mem_sector {S : Finset GeneratorClass} {x : B} (Λ : SL(2,ℂ))
    (hx : x ∈ h.sector S) : repLorentz Λ x ∈ h.sector S := by
  rw [mem_sector, sectorSubmodule] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨gl, hgl, rfl⟩ := hy
    subst hgl
    induction gl with
    | nil =>
      simp only [List.map_nil, List.prod_nil]
      rw [h.repLorentz_one Λ]
      simpa using h.list_prod_mem_sector ([] : List Generators)
    | cons a t ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [h.repLorentz_mul Λ, wordClasses_cons, ← Finset.singleton_union]
      exact h.mul_mem_sector (h.repLorentz_generatorVal_mem_sector Λ a) ih
  | zero => rw [map_zero]; exact zero_mem _
  | add a b ha hb iha ihb => rw [map_add]; exact add_mem iha ihb
  | smul c a ha iha => rw [map_smul]; exact SMulMemClass.smul_mem _ iha

/-!

## Sectors at a fixed mass weight

-/

/-- The span of the words realising exactly the classes `S` of total mass weight
  `w`. -/
def sectorMassWeight (S : Finset GeneratorClass) (w : ℕ) : Submodule ℂ B :=
  Submodule.span ℂ
    {x | ∃ gl : List Generators, wordClasses gl = S ∧
      (gl.map Generators.weight).sum = w ∧ (gl.map h.generatorVal).prod = x}

lemma sectorMassWeight_le_sectorSubmodule (S : Finset GeneratorClass) (w : ℕ) :
    h.sectorMassWeight S w ≤ h.sectorSubmodule S := by
  rw [sectorMassWeight, Submodule.span_le]
  rintro x ⟨gl, hS, hw, rfl⟩
  exact Submodule.subset_span ⟨gl, hS, rfl⟩

lemma sectorMassWeight_le_massWeightSubmodule (S : Finset GeneratorClass) (w : ℕ) :
    h.sectorMassWeight S w ≤ h.massWeightSubmodule w := by
  rw [sectorMassWeight, Submodule.span_le]
  rintro x ⟨gl, hS, hw, rfl⟩
  exact h.list_prod_mem_massWeightSubmodule hw

/-- A word lies in the weight part of its sector given by its total weight. -/
lemma list_prod_mem_sectorMassWeight (gl : List Generators) :
    (gl.map h.generatorVal).prod
      ∈ h.sectorMassWeight (wordClasses gl) ((gl.map Generators.weight).sum) :=
  Submodule.subset_span ⟨gl, rfl, rfl, rfl⟩

/-- Multiplication carries the weight-`w` part of the sector of `S` and the
  weight-`w'` part of the sector of `T` into the weight-`w + w'` part of the sector
  of `S ∪ T`. -/
lemma mul_mem_sectorMassWeight {S T : Finset GeneratorClass} {w w' : ℕ} {x y : B}
    (hx : x ∈ h.sectorMassWeight S w) (hy : y ∈ h.sectorMassWeight T w') :
    x * y ∈ h.sectorMassWeight (S ∪ T) (w + w') := by
  induction hx using Submodule.span_induction with
  | mem x hxw =>
    obtain ⟨gl, hglS, hglw, rfl⟩ := hxw
    induction hy using Submodule.span_induction with
    | mem y hyw =>
      obtain ⟨gl', hglT, hglw', rfl⟩ := hyw
      refine Submodule.subset_span ⟨gl ++ gl', ?_, ?_, ?_⟩
      · rw [wordClasses_append, hglS, hglT]
      · rw [List.map_append, List.sum_append, hglw, hglw']
      · rw [List.map_append, List.prod_append]
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b ha hb iha ihb => rw [mul_add]; exact Submodule.add_mem _ iha ihb
    | smul c a ha iha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ iha
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b ha hb iha ihb => rw [add_mul]; exact Submodule.add_mem _ iha ihb
  | smul c a ha iha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ iha

/-- Reading off the `X ^ w` coefficient of `massWeightPoly` sends the sector of `S`
  into its weight-`w` part — the projection onto the weight-`w` component, with no
  independence argument needed. -/
lemma coeff_massWeightPoly_mem_sectorMassWeight {S : Finset GeneratorClass} {x : B}
    (hx : x ∈ h.sector S) (w : ℕ) :
    (massWeightPoly x).coeff w ∈ h.sectorMassWeight S w := by
  rw [mem_sector, sectorSubmodule] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨gl, hS, rfl⟩ := hy
    rw [h.massWeightPoly_generatorVal_list_prod, Polynomial.coeff_monomial]
    by_cases hw : (gl.map Generators.weight).sum = w
    · rw [if_pos hw]
      exact Submodule.subset_span ⟨gl, hS, hw, rfl⟩
    · rw [if_neg hw]
      exact Submodule.zero_mem _
  | zero =>
    rw [map_zero, Polynomial.coeff_zero]
    exact Submodule.zero_mem _
  | add a b ha hb iha ihb =>
    rw [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ iha ihb
  | smul c a ha iha =>
    rw [map_smul, Polynomial.coeff_smul]
    exact Submodule.smul_mem _ _ iha

/-- The weight-`w` part of the sector of `S` is exactly the intersection of the
  sector with the mass-weight submodule. -/
lemma sectorMassWeight_eq_inf (S : Finset GeneratorClass) (w : ℕ) :
    h.sectorMassWeight S w = h.sectorSubmodule S ⊓ h.massWeightSubmodule w := by
  refine le_antisymm (le_inf (h.sectorMassWeight_le_sectorSubmodule S w)
    (h.sectorMassWeight_le_massWeightSubmodule S w)) ?_
  intro x hx
  obtain ⟨hxS, hxw⟩ := Submodule.mem_inf.mp hx
  have h1 := h.massWeightPoly_of_mem_massWeightSubmodule hxw
  have h2 := h.coeff_massWeightPoly_mem_sectorMassWeight (h.mem_sector.mpr hxS) w
  rwa [h1, Polynomial.coeff_monomial, if_pos rfl] at h2

/-- **The decomposition of the mass-weight submodule into sectors**: the weight-`w`
  component of the field algebra is the join over the class sets `S` of the
  weight-`w` parts of the sectors, since every word realises exactly one class set.
  The empty class set contributes the scalars, at weight zero only. -/
lemma massWeightSubmodule_eq_iSup_sectorMassWeight (w : ℕ) :
    h.massWeightSubmodule w = ⨆ S : Finset GeneratorClass, h.sectorMassWeight S w := by
  refine le_antisymm ?_ (iSup_le fun S => h.sectorMassWeight_le_massWeightSubmodule S w)
  rw [h.massWeightSubmodule_eq_span, Submodule.span_le]
  rintro x ⟨gl, hw, rfl⟩
  exact Submodule.mem_iSup_of_mem (wordClasses gl)
    (Submodule.subset_span ⟨gl, rfl, hw, rfl⟩)

/-- The action `repGauge` preserves the weight parts of every sector. -/
lemma repGauge_mem_sectorMassWeight {S : Finset GeneratorClass} {w : ℕ} {x : B}
    (g : GaugeGroupI) (hx : x ∈ h.sectorMassWeight S w) :
    repGauge g x ∈ h.sectorMassWeight S w := by
  rw [sectorMassWeight_eq_inf] at hx ⊢
  obtain ⟨hxS, hxw⟩ := Submodule.mem_inf.mp hx
  exact Submodule.mem_inf.mpr
    ⟨h.mem_sector.mp (h.repGauge_mem_sector g (h.mem_sector.mpr hxS)),
      h.repGauge_mem_massWeightSubmodule g hxw⟩

/-- The action `repLorentz` preserves the weight parts of every sector. -/
lemma repLorentz_mem_sectorMassWeight {S : Finset GeneratorClass} {w : ℕ} {x : B}
    (Λ : SL(2,ℂ)) (hx : x ∈ h.sectorMassWeight S w) :
    repLorentz Λ x ∈ h.sectorMassWeight S w := by
  rw [sectorMassWeight_eq_inf] at hx ⊢
  obtain ⟨hxS, hxw⟩ := Submodule.mem_inf.mp hx
  exact Submodule.mem_inf.mpr
    ⟨h.mem_sector.mp (h.repLorentz_mem_sector Λ (h.mem_sector.mpr hxS)),
      h.repLorentz_mem_massWeightSubmodule Λ hxw⟩


/-!

## The Higgs sector and the Higgs-sector mass-weight submodules

The Higgs class-set piece of the sector decomposition matches the mass-weight
submodules of the Higgs sector `h.isHiggsSector`: at a non-zero weight `w` the two
agree exactly. At weight zero they differ only by the scalars, which the Higgs-sector
submodule contains (through the unit of `higgsAlgebra`) while the `{higgs}` sector,
being spanned by non-empty words, does not — the scalars are the `∅` sector.

-/

/-- At a non-zero weight the `∅` sector has no weight part: its only word is the
  empty word, of weight zero. -/
lemma sectorMassWeight_empty_of_ne_zero {w : ℕ} (hw : w ≠ 0) :
    h.sectorMassWeight ∅ w = ⊥ := by
  rw [sectorMassWeight, Submodule.span_eq_bot]
  rintro x ⟨gl, hS, hsum, rfl⟩
  rw [wordClasses, List.toFinset_eq_empty_iff, List.map_eq_nil_iff] at hS
  subst hS
  simp at hsum
  exact absurd hsum.symm hw

/-- The algebra generated by the Higgs towers decomposes into the `{higgs}` sector
  and the scalar `∅` sector. -/
lemma higgsAlgebra_le_sup_sectorSubmodule :
    Subalgebra.toSubmodule h.isHiggsSector.higgsAlgebra
      ≤ h.sectorSubmodule {GeneratorClass.higgs} ⊔ h.sectorSubmodule ∅ := by
  intro x hx
  rw [Subalgebra.mem_toSubmodule, IsHiggsSector.higgsAlgebra] at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    apply Submodule.mem_sup_left
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hy
    obtain ⟨k, dd, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩ := hy
    · exact h.mem_sector.mp (h.H_mem_sector dd φ)
    · exact h.mem_sector.mp (h.barH_mem_sector dd φ)
  | algebraMap r =>
    apply Submodule.mem_sup_right
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl, rfl⟩)
  | add a b ha hb iha ihb => exact Submodule.add_mem _ iha ihb
  | mul a b ha hb iha ihb =>
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp iha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp ihb
    rw [add_mul, mul_add, mul_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₁ hb₁)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₁ hb₂)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₂ hb₁)
    · exact Submodule.mem_sup_right (by simpa using h.mul_mem_sectorSubmodule ha₂ hb₂)

/-- The weight-`w` part of the `{higgs}` sector lies in the Higgs-sector mass-weight
  submodule: its words are products of Higgs towers of total weight `w`. -/
lemma sectorMassWeight_higgs_le (w : ℕ) :
    h.sectorMassWeight {GeneratorClass.higgs} w
      ≤ h.isHiggsSector.massWeightSubmodule w := by
  rw [sectorMassWeight, Submodule.span_le]
  rintro x ⟨gl, hS, hsum, rfl⟩
  have hmem : (gl.map h.generatorVal).prod ∈ h.isHiggsSector.higgsAlgebra := by
    refine Subalgebra.list_prod_mem _ fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
    have hk : g.kind = GeneratorClass.higgs := by
      have hmem' : g.kind ∈ wordClasses gl := by
        rw [wordClasses]
        exact List.mem_toFinset.mpr (List.mem_map_of_mem hg)
      rw [hS] at hmem'
      simpa using hmem'
    rw [IsHiggsSector.higgsAlgebra]
    cases g with
    | H n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
        ⟨l, Set.mem_union_left _ ⟨_, rfl⟩⟩⟩)
    | barH n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
        ⟨l, Set.mem_union_right _ ⟨_, rfl⟩⟩⟩)
    | F n l μ ν j => simp [Generators.kind] at hk
    | d i n l j => simp [Generators.kind] at hk
    | bard i n l j => simp [Generators.kind] at hk
    | u i n l j => simp [Generators.kind] at hk
    | baru i n l j => simp [Generators.kind] at hk
    | Q i n l j => simp [Generators.kind] at hk
    | barQ i n l j => simp [Generators.kind] at hk
    | L i n l j => simp [Generators.kind] at hk
    | barL i n l j => simp [Generators.kind] at hk
    | e i n l j => simp [Generators.kind] at hk
    | bare i n l j => simp [Generators.kind] at hk
  rw [IsHiggsSector.massWeightSubmodule]
  refine Submodule.mem_inf.mpr ⟨(Subalgebra.mem_toSubmodule _).mpr hmem, ?_⟩
  rw [LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    LinearMap.coe_restrictScalars, sub_eq_zero]
  rw [h.massWeightPoly_generatorVal_list_prod, hsum]

/-- **The Higgs-sector mass-weight submodules are the weight parts of the `{higgs}`
  sector**, at any non-zero weight. (At weight zero the Higgs-sector submodule also
  contains the scalars, which the sector decomposition files under the `∅` sector.) -/
lemma sectorMassWeight_higgs_eq {w : ℕ} (hw : w ≠ 0) :
    h.sectorMassWeight {GeneratorClass.higgs} w
      = h.isHiggsSector.massWeightSubmodule w := by
  refine le_antisymm (h.sectorMassWeight_higgs_le w) (fun x hx => ?_)
  have hxa := h.isHiggsSector.mem_higgsAlgebra_of_mem_massWeightSubmodule hx
  have hxe := h.isHiggsSector.massWeightPoly_of_mem_massWeightSubmodule hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp
    (h.higgsAlgebra_le_sup_sectorSubmodule ((Subalgebra.mem_toSubmodule _).mpr hxa))
  have hy' := h.coeff_massWeightPoly_mem_sectorMassWeight (h.mem_sector.mpr hy) w
  have hz' := h.coeff_massWeightPoly_mem_sectorMassWeight (h.mem_sector.mpr hz) w
  rw [h.sectorMassWeight_empty_of_ne_zero hw, Submodule.mem_bot] at hz'
  have hkey : y + z = (massWeightPoly y).coeff w + (massWeightPoly z).coeff w := by
    have hc := congrArg (fun p => Polynomial.coeff p w) hxe
    simpa [Polynomial.coeff_add, Polynomial.coeff_monomial] using hc.symm
  rw [hkey, hz', add_zero]
  exact hy'


/-!

## The gauge and fermion sectors and their mass-weight submodules

The same relation as for the Higgs sector: at a non-zero weight `w`, the `{gauge}`
and `{fermion}` pieces of the sector decomposition are exactly the mass-weight
submodules of `h.isGaugeSector` and `h.isFermionSector`; at weight zero the sector
submodules also contain the scalars, which the decomposition files under `∅`.

-/

/-- The algebra generated by the field-strength towers decomposes into the `{gauge}` sector
  and the scalar `∅` sector. -/
lemma gaugeAlgebra_le_sup_sectorSubmodule :
    Subalgebra.toSubmodule h.isGaugeSector.gaugeAlgebra
      ≤ h.sectorSubmodule {GeneratorClass.gauge} ⊔ h.sectorSubmodule ∅ := by
  intro x hx
  rw [Subalgebra.mem_toSubmodule, IsGaugeSector.gaugeAlgebra] at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    apply Submodule.mem_sup_left
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨n, l, μ, ν, φ, rfl⟩ := hy
    exact h.mem_sector.mp (h.F_mem_sector l μ ν φ)
  | algebraMap r =>
    apply Submodule.mem_sup_right
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl, rfl⟩)
  | add a b ha hb iha ihb => exact Submodule.add_mem _ iha ihb
  | mul a b ha hb iha ihb =>
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp iha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp ihb
    rw [add_mul, mul_add, mul_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₁ hb₁)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₁ hb₂)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₂ hb₁)
    · exact Submodule.mem_sup_right (by simpa using h.mul_mem_sectorSubmodule ha₂ hb₂)

/-- The weight-`w` part of the `{gauge}` sector lies in the gauge sector's
  mass-weight submodule. -/
lemma sectorMassWeight_gauge_le (w : ℕ) :
    h.sectorMassWeight {GeneratorClass.gauge} w
      ≤ h.isGaugeSector.massWeightSubmodule w := by
  rw [sectorMassWeight, Submodule.span_le]
  rintro x ⟨gl, hS, hsum, rfl⟩
  have hmem : (gl.map h.generatorVal).prod ∈ h.isGaugeSector.gaugeAlgebra := by
    refine Subalgebra.list_prod_mem _ fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
    have hk : g.kind = GeneratorClass.gauge := by
      have hmem' : g.kind ∈ wordClasses gl := by
        rw [wordClasses]
        exact List.mem_toFinset.mpr (List.mem_map_of_mem hg)
      rw [hS] at hmem'
      simpa using hmem'
    rw [IsGaugeSector.gaugeAlgebra]
    cases g with
    | F n l μ ν j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
        ⟨l, Set.mem_iUnion.mpr ⟨μ, Set.mem_iUnion.mpr ⟨ν, ⟨_, rfl⟩⟩⟩⟩⟩)
    | H n l j => simp [Generators.kind] at hk
    | barH n l j => simp [Generators.kind] at hk
    | d i n l j => simp [Generators.kind] at hk
    | bard i n l j => simp [Generators.kind] at hk
    | u i n l j => simp [Generators.kind] at hk
    | baru i n l j => simp [Generators.kind] at hk
    | Q i n l j => simp [Generators.kind] at hk
    | barQ i n l j => simp [Generators.kind] at hk
    | L i n l j => simp [Generators.kind] at hk
    | barL i n l j => simp [Generators.kind] at hk
    | e i n l j => simp [Generators.kind] at hk
    | bare i n l j => simp [Generators.kind] at hk
  rw [IsGaugeSector.massWeightSubmodule]
  refine Submodule.mem_inf.mpr ⟨(Subalgebra.mem_toSubmodule _).mpr hmem, ?_⟩
  rw [LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    LinearMap.coe_restrictScalars, sub_eq_zero]
  rw [h.massWeightPoly_generatorVal_list_prod, hsum]

/-- **The gauge sector's mass-weight submodules are the weight parts of the
  `{gauge}` sector**, at any non-zero weight. (At weight zero the sector's
  submodule also contains the scalars, which the sector decomposition files under the
  `∅` sector.) -/
lemma sectorMassWeight_gauge_eq {w : ℕ} (hw : w ≠ 0) :
    h.sectorMassWeight {GeneratorClass.gauge} w
      = h.isGaugeSector.massWeightSubmodule w := by
  refine le_antisymm (h.sectorMassWeight_gauge_le w) (fun x hx => ?_)
  have hxa := h.isGaugeSector.mem_gaugeAlgebra_of_mem_massWeightSubmodule hx
  have hxe := h.isGaugeSector.massWeightPoly_of_mem_massWeightSubmodule hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp
    (h.gaugeAlgebra_le_sup_sectorSubmodule ((Subalgebra.mem_toSubmodule _).mpr hxa))
  have hy' := h.coeff_massWeightPoly_mem_sectorMassWeight (h.mem_sector.mpr hy) w
  have hz' := h.coeff_massWeightPoly_mem_sectorMassWeight (h.mem_sector.mpr hz) w
  rw [h.sectorMassWeight_empty_of_ne_zero hw, Submodule.mem_bot] at hz'
  have hkey : y + z = (massWeightPoly y).coeff w + (massWeightPoly z).coeff w := by
    have hc := congrArg (fun p => Polynomial.coeff p w) hxe
    simpa [Polynomial.coeff_add, Polynomial.coeff_monomial] using hc.symm
  rw [hkey, hz', add_zero]
  exact hy'

/-- The algebra generated by the fermion towers decomposes into the `{fermion}` sector
  and the scalar `∅` sector. -/
lemma fermionAlgebra_le_sup_sectorSubmodule :
    Subalgebra.toSubmodule h.isFermionSector.fermionAlgebra
      ≤ h.sectorSubmodule {GeneratorClass.fermion} ⊔ h.sectorSubmodule ∅ := by
  intro x hx
  rw [Subalgebra.mem_toSubmodule, IsFermionSector.fermionAlgebra] at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    apply Submodule.mem_sup_left
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hy
    obtain ⟨i, k, dd, (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
      ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩)⟩ := hy
    · exact h.mem_sector.mp (h.d_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.bard_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.u_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.baru_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.Q_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.barQ_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.L_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.barL_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.e_mem_sector i dd φ)
    · exact h.mem_sector.mp (h.bare_mem_sector i dd φ)
  | algebraMap r =>
    apply Submodule.mem_sup_right
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl, rfl⟩)
  | add a b ha hb iha ihb => exact Submodule.add_mem _ iha ihb
  | mul a b ha hb iha ihb =>
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp iha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp ihb
    rw [add_mul, mul_add, mul_add]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (Submodule.add_mem _ ?_ ?_)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₁ hb₁)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₁ hb₂)
    · exact Submodule.mem_sup_left (by simpa using h.mul_mem_sectorSubmodule ha₂ hb₁)
    · exact Submodule.mem_sup_right (by simpa using h.mul_mem_sectorSubmodule ha₂ hb₂)

/-- The weight-`w` part of the `{fermion}` sector lies in the fermion sector's
  mass-weight submodule. -/
lemma sectorMassWeight_fermion_le (w : ℕ) :
    h.sectorMassWeight {GeneratorClass.fermion} w
      ≤ h.isFermionSector.massWeightSubmodule w := by
  rw [sectorMassWeight, Submodule.span_le]
  rintro x ⟨gl, hS, hsum, rfl⟩
  have hmem : (gl.map h.generatorVal).prod ∈ h.isFermionSector.fermionAlgebra := by
    refine Subalgebra.list_prod_mem _ fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hy
    have hk : g.kind = GeneratorClass.fermion := by
      have hmem' : g.kind ∈ wordClasses gl := by
        rw [wordClasses]
        exact List.mem_toFinset.mpr (List.mem_map_of_mem hg)
      rw [hS] at hmem'
      simpa using hmem'
    rw [IsFermionSector.fermionAlgebra]
    cases g with
    | d i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (⟨_, rfl⟩)))))))))⟩⟩⟩)
    | bard i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))))))))⟩⟩⟩)
    | u i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩)))))))⟩⟩⟩)
    | baru i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))))))⟩⟩⟩)
    | Q i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩)))))⟩⟩⟩)
    | barQ i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))))⟩⟩⟩)
    | L i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩)))⟩⟩⟩)
    | barL i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))⟩⟩⟩)
    | e i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩)⟩⟩⟩)
    | bare i n l j =>
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_right _ ⟨_, rfl⟩⟩⟩⟩)
    | H n l j => simp [Generators.kind] at hk
    | barH n l j => simp [Generators.kind] at hk
    | F n l μ ν j => simp [Generators.kind] at hk
  rw [IsFermionSector.massWeightSubmodule]
  refine Submodule.mem_inf.mpr ⟨(Subalgebra.mem_toSubmodule _).mpr hmem, ?_⟩
  rw [LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    LinearMap.coe_restrictScalars, sub_eq_zero]
  rw [h.massWeightPoly_generatorVal_list_prod, hsum]

/-- **The fermion sector's mass-weight submodules are the weight parts of the
  `{fermion}` sector**, at any non-zero weight. (At weight zero the sector's
  submodule also contains the scalars, which the sector decomposition files under the
  `∅` sector.) -/
lemma sectorMassWeight_fermion_eq {w : ℕ} (hw : w ≠ 0) :
    h.sectorMassWeight {GeneratorClass.fermion} w
      = h.isFermionSector.massWeightSubmodule w := by
  refine le_antisymm (h.sectorMassWeight_fermion_le w) (fun x hx => ?_)
  have hxa := h.isFermionSector.mem_fermionAlgebra_of_mem_massWeightSubmodule hx
  have hxe := h.isFermionSector.massWeightPoly_of_mem_massWeightSubmodule hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp
    (h.fermionAlgebra_le_sup_sectorSubmodule ((Subalgebra.mem_toSubmodule _).mpr hxa))
  have hy' := h.coeff_massWeightPoly_mem_sectorMassWeight (h.mem_sector.mpr hy) w
  have hz' := h.coeff_massWeightPoly_mem_sectorMassWeight (h.mem_sector.mpr hz) w
  rw [h.sectorMassWeight_empty_of_ne_zero hw, Submodule.mem_bot] at hz'
  have hkey : y + z = (massWeightPoly y).coeff w + (massWeightPoly z).coeff w := by
    have hc := congrArg (fun p => Polynomial.coeff p w) hxe
    simpa [Polynomial.coeff_add, Polynomial.coeff_monomial] using hc.symm
  rw [hkey, hz', add_zero]
  exact hy'

/-!

## Two-class sectors

A word realising exactly two classes splits, up to reordering, into the part of the
first class and the part of the second.  When the two classes' algebras commute, the
weight-`w` piece of the two-class sector is therefore contained in the join of the
products of the two sectors' own mass-weight submodules, over the splittings of `w`
into two non-zero parts.  The hypotheses are stated abstractly so that the three
pairs of sectors can each instantiate them.

-/

/-- A single generator's value lies in any family of submodules dominating its own
  class's sector. -/
lemma generatorVal_mem_of_kind {c : GeneratorClass} {M : ℕ → Submodule ℂ B}
    (hM : ∀ w, h.sectorMassWeight {c} w ≤ M w) {g : Generators} (hg : g.kind = c) :
    h.generatorVal g ∈ M g.weight := by
  refine hM _ ?_
  have h1 := h.list_prod_mem_sectorMassWeight [g]
  simpa [wordClasses_cons, hg] using h1

/-- **The two-class word decomposition.** A word all of whose generators lie in one of
  two classes is a product of an element of weight `classWeight c₁` from the first
  class's family and an element of weight `classWeight c₂` from the second. -/
lemma list_prod_mem_mul_of_forall_kind {c₁ c₂ : GeneratorClass} (hne : c₁ ≠ c₂)
    {M₁ M₂ : ℕ → Submodule ℂ B}
    (hM₁ : ∀ w, h.sectorMassWeight {c₁} w ≤ M₁ w)
    (hM₂ : ∀ w, h.sectorMassWeight {c₂} w ≤ M₂ w)
    (hone₁ : (1 : Submodule ℂ B) ≤ M₁ 0) (hone₂ : (1 : Submodule ℂ B) ≤ M₂ 0)
    (hmul₁ : ∀ a b, M₁ a * M₁ b ≤ M₁ (a + b))
    (hmul₂ : ∀ a b, M₂ a * M₂ b ≤ M₂ (a + b))
    (hcomm : ∀ a b, M₂ a * M₁ b ≤ M₁ b * M₂ a)
    (gl : List Generators) (hgl : ∀ g ∈ gl, g.kind = c₁ ∨ g.kind = c₂) :
    (gl.map h.generatorVal).prod
      ∈ M₁ (classWeight c₁ gl) * M₂ (classWeight c₂ gl) := by
  induction gl with
  | nil =>
    simp only [List.map_nil, List.prod_nil, classWeight_nil]
    have h1 : (1 : B) ∈ M₁ 0 := hone₁ (Submodule.mem_one.mpr ⟨1, by simp⟩)
    have h2 : (1 : B) ∈ M₂ 0 := hone₂ (Submodule.mem_one.mpr ⟨1, by simp⟩)
    simpa using Submodule.mul_mem_mul h1 h2
  | cons g t ih =>
    have ht : ∀ g' ∈ t, g'.kind = c₁ ∨ g'.kind = c₂ := fun g' hg' => hgl g' (by simp [hg'])
    have hIH := ih ht
    simp only [List.map_cons, List.prod_cons]
    rcases hgl g (by simp) with hg | hg
    · have hgm : h.generatorVal g ∈ M₁ g.weight := h.generatorVal_mem_of_kind hM₁ hg
      have hne2 : g.kind ≠ c₂ := by rw [hg]; exact hne
      rw [classWeight_cons_of_eq hg, classWeight_cons_of_ne hne2]
      refine (?_ : M₁ g.weight * (M₁ (classWeight c₁ t) * M₂ (classWeight c₂ t))
        ≤ M₁ (g.weight + classWeight c₁ t) * M₂ (classWeight c₂ t))
        (Submodule.mul_mem_mul hgm hIH)
      rw [← mul_assoc]
      exact mul_le_mul' (hmul₁ _ _) le_rfl
    · have hgm : h.generatorVal g ∈ M₂ g.weight := h.generatorVal_mem_of_kind hM₂ hg
      have hne1 : g.kind ≠ c₁ := by rw [hg]; exact hne.symm
      rw [classWeight_cons_of_eq hg, classWeight_cons_of_ne hne1]
      refine (?_ : M₂ g.weight * (M₁ (classWeight c₁ t) * M₂ (classWeight c₂ t))
        ≤ M₁ (classWeight c₁ t) * M₂ (g.weight + classWeight c₂ t))
        (Submodule.mul_mem_mul hgm hIH)
      calc M₂ g.weight * (M₁ (classWeight c₁ t) * M₂ (classWeight c₂ t))
          = M₂ g.weight * M₁ (classWeight c₁ t) * M₂ (classWeight c₂ t) :=
            (mul_assoc _ _ _).symm
        _ ≤ M₁ (classWeight c₁ t) * M₂ g.weight * M₂ (classWeight c₂ t) :=
            mul_le_mul' (hcomm _ _) le_rfl
        _ = M₁ (classWeight c₁ t) * (M₂ g.weight * M₂ (classWeight c₂ t)) := mul_assoc _ _ _
        _ ≤ M₁ (classWeight c₁ t) * M₂ (g.weight + classWeight c₂ t) :=
            mul_le_mul' le_rfl (hmul₂ _ _)

/-- **The two-class sector decomposition.** The weight-`w` piece of the sector of two
  classes is contained in the join, over the splittings of `w` into two non-zero
  parts, of the products of the two classes' mass-weight submodules. -/
lemma sectorMassWeight_pair_le {c₁ c₂ : GeneratorClass} (hne : c₁ ≠ c₂)
    {M₁ M₂ : ℕ → Submodule ℂ B}
    (hM₁ : ∀ w, h.sectorMassWeight {c₁} w ≤ M₁ w)
    (hM₂ : ∀ w, h.sectorMassWeight {c₂} w ≤ M₂ w)
    (hone₁ : (1 : Submodule ℂ B) ≤ M₁ 0) (hone₂ : (1 : Submodule ℂ B) ≤ M₂ 0)
    (hmul₁ : ∀ a b, M₁ a * M₁ b ≤ M₁ (a + b))
    (hmul₂ : ∀ a b, M₂ a * M₂ b ≤ M₂ (a + b))
    (hcomm : ∀ a b, M₂ a * M₁ b ≤ M₁ b * M₂ a) (w : ℕ) :
    h.sectorMassWeight {c₁, c₂} w
      ≤ ⨆ (p : ℕ × ℕ) (_ : p.1 + p.2 = w) (_ : p.1 ≠ 0) (_ : p.2 ≠ 0), M₁ p.1 * M₂ p.2 := by
  rw [sectorMassWeight, Submodule.span_le]
  rintro x ⟨gl, hS, hsum, rfl⟩
  have hgl : ∀ g ∈ gl, g.kind = c₁ ∨ g.kind = c₂ := by
    intro g hg
    have : g.kind ∈ wordClasses gl := List.mem_toFinset.mpr (List.mem_map_of_mem hg)
    rw [hS] at this
    simpa using this
  have h1 : c₁ ∈ wordClasses gl := by rw [hS]; simp
  have h2 : c₂ ∈ wordClasses gl := by rw [hS]; simp
  refine Submodule.mem_iSup_of_mem (classWeight c₁ gl, classWeight c₂ gl)
    (Submodule.mem_iSup_of_mem (by rw [classWeight_add hne hgl, hsum])
      (Submodule.mem_iSup_of_mem (classWeight_ne_zero h1)
        (Submodule.mem_iSup_of_mem (classWeight_ne_zero h2) ?_)))
  exact h.list_prod_mem_mul_of_forall_kind hne hM₁ hM₂ hone₁ hone₂ hmul₁ hmul₂ hcomm gl hgl

/-!

## Invariance in terms of sectors

Both actions preserve every weight part of every sector
(`repGauge_mem_sectorMassWeight`, `repLorentz_mem_sectorMassWeight`), and the
weight-`w` submodule is the join of those parts
(`massWeightSubmodule_eq_iSup_sectorMassWeight`), so an element of the weight-`w`
submodule is a sum of sector pieces and each action carries one such sum to
another. Reading off from that alone that the pieces are themselves invariant is
not possible: it needs the pieces to be determined by their sum, that is, needs
the family of weight parts to be independent, and that is the hypothesis of
`sector_invariant_of_iSupIndep`.

-/

/-- An element of the weight-`w` submodule fixed by both actions is a sum of
  weight-`w` sector pieces, each of them fixed by both actions, provided the weight
  parts of the sectors are independent. Independence is what turns the two
  decompositions `x = ∑ s, f s` and `x = ∑ s, repGauge g (f s)` into an equality
  piece by piece; without it the pieces are not determined by their sum. -/
lemma sector_invariant_of_iSupIndep {w : ℕ}
    (hind : iSupIndep fun S : Finset GeneratorClass => h.sectorMassWeight S w)
    (x : B) (x_gauge_invariant : ∀ g, repGauge g x = x)
    (x_lorentz_invariant : ∀ g, repLorentz g x = x)
    (x_mass_dim : x ∈ h.massWeightSubmodule w) :
    ∃ f : Finset GeneratorClass → B,
      x = ∑ s, f s ∧ (∀ s, f s ∈ h.sectorMassWeight s w ∧
      (∀ g, repGauge g (f s) = (f s)) ∧ (∀ g, repLorentz g (f s) = (f s))) := by
  rw [h.massWeightSubmodule_eq_iSup_sectorMassWeight w] at x_mass_dim
  obtain ⟨c, hc, hcx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp x_mass_dim
  have hsum : ∑ s, c s = x := by
    rw [← hcx, Finsupp.sum_fintype _ _ fun _ => rfl]
  have huniq := (iSupIndep_iff_finsetSum_eq_imp_eq
    fun S : Finset GeneratorClass => h.sectorMassWeight S w).mp hind
  have key : ∀ T : Module.End ℂ B, (∀ s, T (c s) ∈ h.sectorMassWeight s w) →
      T x = x → ∀ s, T (c s) = c s := by
    intro T hT hTx s
    refine huniq Finset.univ (fun t => T (c t)) (fun t => c t)
      (fun t _ => ⟨hT t, hc t⟩) ?_ s (Finset.mem_univ s)
    rw [← map_sum, hsum, hTx]
  exact ⟨fun s => c s, hsum.symm, fun s => ⟨hc s,
    fun g => key (repGauge g) (fun t => h.repGauge_mem_sectorMassWeight g (hc t))
      (x_gauge_invariant g) s,
    fun Λ => key (repLorentz Λ) (fun t => h.repLorentz_mem_sectorMassWeight Λ (hc t))
      (x_lorentz_invariant Λ) s⟩⟩

/-- An element of the field algebra of weight `w` fixed by both actions is a sum of
  weight-`w` sector pieces, each of them fixed by both actions. -/
lemma sector_invariant {w : ℕ} (x : B) (hx : x ∈ h.fieldAlgebra)
    (x_gauge_invariant : ∀ g, repGauge g x = x)
    (x_lorentz_invariant : ∀ g, repLorentz g x = x)
    (x_mass_dim : x ∈ h.massWeightSubmodule w) :
    ∃ f : Finset GeneratorClass → B,
      x = ∑ s, f s ∧  (∀ s, f s ∈ h.sectorMassWeight s w ∧
      (∀ g, repGauge g (f s) = (f s)) ∧ (∀ g, repLorentz g (f s) = (f s))) := by
  -- Open. `sector_invariant_of_iSupIndep` closes this given
  -- `iSupIndep fun S => h.sectorMassWeight S w`, and that independence is the whole
  -- of what is missing; it does not follow from `IsCovStandardModel`, whose axioms
  -- are all equations and so survive quotients that the independence does not.
  sorry

end IsCovStandardModel

end StandardModel
