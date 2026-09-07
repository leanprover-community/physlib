/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsCovStandardModel.YukawaSector.Basic
public import Physlib.Particles.StandardModel.IsHiggsSector.DerivSubmodule.BoostWeightDecomposition
public import Physlib.Relativity.LorentzGroup.Invariants.IsQuadLorentz
-- The fermion boost weights enter only inside the proofs below, so this import is kept
-- private: its public form is one character over the line-length limit.
import Physlib.Particles.StandardModel.IsFermionSector.DerivSubmodule.BoostWeightDecomposition
/-!
# The Yukawa invariants below mass weight eight

Mass weight eight is the first weight at which the Yukawa sector can carry an invariant:
it is the weight of `H ψ ψ`, one Higgs against two fermions. Below it the sector is nearly
empty — it vanishes outright below weight five and again at weight six — and the little
that survives, at weights five and seven, is barred from carrying an invariant by a parity
count.

The count is on boost weight, not on the number of covector indices as in the gauge
sector. Along a spatial axis every Higgs symbol carries even boost weight, its derivative
slots contributing `±2` or `0` and its value index nothing, while every fermion symbol
carries odd boost weight, the Weyl-spinor value index contributing the extra `±1`. Each of
the four products surviving at weights five and seven has exactly one fermion factor, so
its boost weight is odd along every axis; and an element of odd boost weight cannot be
Lorentz invariant, since invariance forces boost weight zero and zero is even.

Running that argument needs the product of two weight decompositions, and the general
construction in `WeightGrading.lean` asks for `IsBoostGraded`, which the Standard Model
algebra has no reason to satisfy: nothing says its boost weight spaces span. Yet
multiplicativity of the Lorentz representation is by itself enough to convolve two
decompositions, and section A rebuilds the product from that alone. Section B turns an odd
support into the absence of invariants, and does so modulo a Lorentz-stable submodule `S`
by passing to the quotient, where the weight-zero piece of the pushed-forward
decomposition is still trivial.

- A. Convolving weight decompositions without a grading
- B. Odd boost weight admits no invariant
- C. Even Higgs against odd fermion
- D. Mass weights five and seven
- E. The classification below mass weight eight

Unlike the gauge-sector statement, the final theorem needs no `0 < w`: the Yukawa sector
is a product of two non-empty sectors, so it already vanishes at weight zero and the
scalars never enter.

-/

@[expose] public section

namespace Lorentz.BoostWeight.WeightDecomposition

open MatrixGroups

/-!

## A. Convolving weight decompositions without a grading

The weight-`m` piece of a product is the join, over the splittings `k + l = m`, of the
products of the weight-`k` and weight-`l` pieces of the factors. That this is a weight
decomposition of the product submodule needs nothing of the representation beyond
multiplicativity: `mul_mem_boostWeightSubmodule` adds the two weights, and the pieces of
the factors join to the factors themselves. The general `mul` of `WeightGrading.lean`
instead routes through the projections `boostProj`, and so through `IsBoostGraded`, which
is more than is available here.

-/

variable {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [Ring A] [Algebra K A]
  {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {V W : Submodule K A}

omit [Algebra ℝ K] in
/-- The bound behind the convolution: a product of two joins of pieces is contained in the
  join, over the total weights, of the convolution. -/
lemma mul_le_iSup_convolution (p q : ℤ → Submodule K A) :
    (⨆ k, p k) * (⨆ l, q l) ≤ ⨆ (m : ℤ) (k : ℤ) (l : ℤ) (_ : k + l = m), p k * q l := by
  rw [Submodule.iSup_mul]
  refine iSup_le fun k => ?_
  rw [Submodule.mul_iSup]
  exact iSup_le fun l => le_iSup_of_le (k + l)
    (le_iSup_of_le k (le_iSup_of_le l (le_iSup_of_le rfl le_rfl)))

open scoped Pointwise in
/-- The convolution of two weight decompositions along the same axis, built from
  multiplicativity of the representation alone: the weight-`m` piece of the product is the
  join over the splittings `k + l = m` of the products of the pieces. -/
noncomputable def mulOfMul
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y)
    (d₁ : WeightDecomposition rep i V) (d₂ : WeightDecomposition rep i W) :
    WeightDecomposition rep i (V * W) where
  piece m := ⨆ (k : ℤ) (l : ℤ) (_ : k + l = m), d₁.piece k * d₂.piece l
  supp := d₁.supp + d₂.supp
  piece_le m := iSup_le fun k => iSup_le fun l => iSup_le fun hkl =>
    Submodule.mul_le.2 fun a ha b hb => by
      rw [← hkl]
      exact mul_mem_boostWeightSubmodule hmul (d₁.piece_le k ha) (d₂.piece_le l hb)
  piece_eq_bot m hm := by
    refine iSup_eq_bot.2 fun k => iSup_eq_bot.2 fun l => iSup_eq_bot.2 fun hkl => ?_
    by_cases hk : k ∈ d₁.supp
    · rw [d₂.piece_eq_bot l fun hl => hm (hkl ▸ Finset.add_mem_add hk hl), Submodule.mul_bot]
    · rw [d₁.piece_eq_bot k hk, Submodule.bot_mul]
  iSup_piece :=
    le_antisymm (iSup_le fun m => iSup_le fun k => iSup_le fun l => iSup_le fun _ =>
        Submodule.mul_le.2 fun a ha b hb => Submodule.mul_mem_mul
          (le_of_le_of_eq (le_iSup d₁.piece k) d₁.iSup_piece ha)
          (le_of_le_of_eq (le_iSup d₂.piece l) d₂.iSup_piece hb))
      (le_trans (le_of_eq (show V * W = (⨆ k, d₁.piece k) * ⨆ l, d₂.piece l by
        rw [d₁.iSup_piece, d₂.iSup_piece])) (mul_le_iSup_convolution _ _))

open scoped Pointwise in
/-- The weights occurring in a convolution are the sums of the weights occurring in the
  two factors. -/
@[simp]
lemma mulOfMul_supp
    (hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y)
    (d₁ : WeightDecomposition rep i V) (d₂ : WeightDecomposition rep i W) :
    (d₁.mulOfMul hmul d₂).supp = d₁.supp + d₂.supp := rfl

/-- A weight of a convolution splits as a weight of the left factor plus a weight of the
  right one. -/
lemma exists_add_eq_of_mem_mulOfMul_supp
    {hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y}
    {d₁ : WeightDecomposition rep i V} {d₂ : WeightDecomposition rep i W} {m : ℤ}
    (hm : m ∈ (d₁.mulOfMul hmul d₂).supp) :
    ∃ k ∈ d₁.supp, ∃ l ∈ d₂.supp, k + l = m := by
  rw [mulOfMul_supp] at hm
  exact Finset.mem_add.1 hm

/-- Even times even is even: a convolution of two decompositions of even support has even
  support. -/
lemma two_dvd_of_mem_mulOfMul_supp
    {hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y}
    {d₁ : WeightDecomposition rep i V} {d₂ : WeightDecomposition rep i W}
    (h₁ : ∀ k ∈ d₁.supp, (2 : ℤ) ∣ k) (h₂ : ∀ k ∈ d₂.supp, (2 : ℤ) ∣ k) {m : ℤ}
    (hm : m ∈ (d₁.mulOfMul hmul d₂).supp) : (2 : ℤ) ∣ m := by
  obtain ⟨k, hk, l, hl, rfl⟩ := exists_add_eq_of_mem_mulOfMul_supp hm
  exact dvd_add (h₁ k hk) (h₂ l hl)

/-- Even times odd is odd: a convolution of a decomposition of even support with one of odd
  support has odd support. -/
lemma not_two_dvd_of_mem_mulOfMul_supp
    {hmul : ∀ (Λ : SL(2,ℂ)) (x y : A), rep Λ (x * y) = rep Λ x * rep Λ y}
    {d₁ : WeightDecomposition rep i V} {d₂ : WeightDecomposition rep i W}
    (h₁ : ∀ k ∈ d₁.supp, (2 : ℤ) ∣ k) (h₂ : ∀ k ∈ d₂.supp, ¬ (2 : ℤ) ∣ k) {m : ℤ}
    (hm : m ∈ (d₁.mulOfMul hmul d₂).supp) : ¬ (2 : ℤ) ∣ m := by
  obtain ⟨k, hk, l, hl, rfl⟩ := exists_add_eq_of_mem_mulOfMul_supp hm
  exact fun hdvd => h₂ l hl ((dvd_add_right (h₁ k hk)).1 hdvd)

/-- The weights of a join of two decompositions are the weights of the two. -/
@[simp]
lemma sup_supp (d₁ : WeightDecomposition rep i V) (d₂ : WeightDecomposition rep i W) :
    (d₁.sup d₂).supp = d₁.supp ∪ d₂.supp := rfl

/-!

## B. Odd boost weight admits no invariant

A Lorentz invariant has boost weight zero along every axis, and zero is even. So a
submodule all of whose weights are odd contains no invariant but `0`. The statement is
wanted modulo a Lorentz-stable submodule `S`, and stability is exactly what is needed to
divide `S` out: the quotient carries a representation intertwined by `S.mkQ`, the images
of the pieces are again of pure weight, they join to the image of the submodule, and the
weight-zero image is the image of the trivial weight-zero piece. So the invariant dies in
the quotient, which is to say it lies in `S`.

-/

/-- An equivariant linear map carries boost weight `m` to boost weight `m`: it commutes
  with the boosts, and scaling is preserved. -/
lemma map_boostWeightSubmodule_le {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {repM : Representation K SL(2,ℂ) M}
    {repN : Representation K SL(2,ℂ) N} (f : M →ₗ[K] N)
    (hf : ∀ (g : SL(2,ℂ)) (y : M), f (repM g y) = repN g (f y)) (j : Fin 3) (m : ℤ) :
    (boostWeightSubmodule repM j m).map f ≤ boostWeightSubmodule repN j m := by
  rintro _ ⟨y, hy, rfl⟩
  intro t ht
  rw [← hf, hy t ht, map_smul]

/-- A submodule whose boost weights are all odd carries no Lorentz invariant beyond a
  Lorentz-stable submodule `S`: an invariant of the join with `S` already lies in `S`.
  Invariance forces boost weight zero, and zero is not among the weights on offer. -/
lemma mem_of_invariant_of_mem_sup_of_odd_supp {M : Type*} [AddCommGroup M] [Module ℂ M]
    {repLorentz : Representation ℂ SL(2,ℂ) M} {j : Fin 3} {V : Submodule ℂ M}
    (d : WeightDecomposition repLorentz j V) (hodd : ∀ k ∈ d.supp, ¬ (2 : ℤ) ∣ k)
    (S : Submodule ℂ M) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : M}
    (hx : x ∈ V ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hzero : d.piece 0 = ⊥ := d.piece_eq_bot 0 fun hmem => hodd 0 hmem ⟨0, rfl⟩
  have hle : ∀ m : ℤ, (d.piece m).map S.mkQ
      ≤ boostWeightSubmodule (IsQuadLorentz.quotRep (repLorentz := repLorentz) S hS) j m :=
    fun m => le_trans (Submodule.map_mono (d.piece_le m))
      (map_boostWeightSubmodule_le S.mkQ (fun _ _ => rfl) j m)
  have hmem : S.mkQ x ∈ ⨆ m : ℤ, (d.piece m).map S.mkQ := by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz, add_zero,
      ← Submodule.map_iSup]
    exact Submodule.mem_map_of_mem (le_of_eq d.iSup_piece.symm hy)
  have hinv' : ∀ g : SL(2,ℂ),
      IsQuadLorentz.quotRep (repLorentz := repLorentz) S hS g (S.mkQ x) = S.mkQ x :=
    fun g => by rw [IsQuadLorentz.quotRep_mkQ, hinv g]
  have hx0 := mem_of_mem_iSup_of_boostWeight_zero hle hmem
    (mem_boostWeightSubmodule_zero_of_invariant hinv' j)
  rw [hzero, Submodule.map_bot, Submodule.mem_bot] at hx0
  rwa [← Submodule.ker_mkQ S, LinearMap.mem_ker]

end Lorentz.BoostWeight.WeightDecomposition

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz Lorentz.BoostWeight

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
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsCovStandardModel B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
    massWeightPoly H barH F d bard u baru Q barQ L barL e bare)

/-!

## C. Even Higgs against odd fermion

The two boost weight decompositions of the factors are already proved: the Higgs
derivative submodules carry even weights, their derivative slots contributing `±2` or `0`
and their value index nothing, and the fermion ones carry odd weights, the Weyl-spinor
value index adding `±1`. Convolving them along section A gives a decomposition of each
product surviving below weight eight, and the parity bookkeeping of that section makes
every weight of such a product odd, since each carries exactly one fermion factor. The
term with two Higgs factors is convolved twice, even against even staying even before the
fermion turns the total odd.

-/

/-- The boost weight decomposition of a product of a Higgs and a fermion derivative
  submodule, obtained by convolving the two factors' decompositions. -/
private noncomputable def higgsFermionBoostWeight (a b : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (h.isHiggsSector.derivSubmodule a * h.isFermionSector.derivSubmodule b) :=
  WeightDecomposition.mulOfMul hrepLorentz_mul
    (h.isHiggsSector.derivSubmoduleBoostWeight a i)
    (h.isFermionSector.derivSubmoduleBoostWeight b i)

/-- One Higgs factor against one fermion factor is odd: even plus odd. -/
private lemma odd_higgsFermionBoostWeight_supp (a b : ℕ) (i : Fin 3) :
    ∀ k ∈ (h.higgsFermionBoostWeight a b i).supp, ¬ (2 : ℤ) ∣ k :=
  fun _ hk => WeightDecomposition.not_two_dvd_of_mem_mulOfMul_supp
    (fun _ hp => h.isHiggsSector.two_dvd_of_mem_derivSubmoduleBoostWeight_supp a i hp)
    (fun _ hq => h.isFermionSector.not_two_dvd_of_mem_derivSubmoduleBoostWeight_supp b i hq) hk

/-- The boost weight decomposition of a product of two Higgs and one fermion derivative
  submodule, obtained by convolving the Higgs pair first. -/
private noncomputable def higgsSqFermionBoostWeight (a b c : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (h.isHiggsSector.derivSubmodule a * h.isHiggsSector.derivSubmodule b
        * h.isFermionSector.derivSubmodule c) :=
  WeightDecomposition.mulOfMul hrepLorentz_mul
    (WeightDecomposition.mulOfMul hrepLorentz_mul
      (h.isHiggsSector.derivSubmoduleBoostWeight a i)
      (h.isHiggsSector.derivSubmoduleBoostWeight b i))
    (h.isFermionSector.derivSubmoduleBoostWeight c i)

/-- Two Higgs factors against one fermion factor is odd: even plus even plus odd. -/
private lemma odd_higgsSqFermionBoostWeight_supp (a b c : ℕ) (i : Fin 3) :
    ∀ k ∈ (h.higgsSqFermionBoostWeight a b c i).supp, ¬ (2 : ℤ) ∣ k :=
  fun _ hk => WeightDecomposition.not_two_dvd_of_mem_mulOfMul_supp
    (fun _ hp => WeightDecomposition.two_dvd_of_mem_mulOfMul_supp
      (fun _ hp' => h.isHiggsSector.two_dvd_of_mem_derivSubmoduleBoostWeight_supp a i hp')
      (fun _ hp' => h.isHiggsSector.two_dvd_of_mem_derivSubmoduleBoostWeight_supp b i hp') hp)
    (fun _ hq => h.isFermionSector.not_two_dvd_of_mem_derivSubmoduleBoostWeight_supp c i hq) hk

/-!

## D. Mass weights five and seven

Weight five is a single product, the Higgs field against the underived fermion towers.
Weight seven is a join of three: the Higgs field against the once-derived towers, the
once-derived Higgs field against the underived ones, and two Higgs fields against the
underived ones. Each of the four has exactly one fermion factor, so section C makes all of
their boost weights odd, the join included, and section B leaves the invariant in `S`. The
axis is immaterial; the first one will do.

-/

/-- Mass weight five carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `sectorMassWeight {higgs, fermion} 5 ⊔ S` lies in `S`. The weight is
  one Higgs field against the underived fermion towers, of odd boost weight. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 5 ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rw [h.sectorMassWeight_higgs_fermion_five] at hx
  exact WeightDecomposition.mem_of_invariant_of_mem_sup_of_odd_supp
    (h.higgsFermionBoostWeight 0 0 0) (h.odd_higgsFermionBoostWeight_supp 0 0 0) S hSL hx hL

/-- Mass weight seven carries no Lorentz invariant modulo a Lorentz-stable submodule: a
  Lorentz invariant of `sectorMassWeight {higgs, fermion} 7 ⊔ S` lies in `S`. Each of the
  three products making up the weight has a single fermion factor, so each is of odd boost
  weight and so is their join. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_seven_sup
    (S : Submodule ℂ B) (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} 7 ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rw [h.sectorMassWeight_higgs_fermion_seven] at hx
  refine WeightDecomposition.mem_of_invariant_of_mem_sup_of_odd_supp
    (((h.higgsFermionBoostWeight 0 1 0).sup (h.higgsFermionBoostWeight 1 0 0)).sup
      (h.higgsSqFermionBoostWeight 0 0 0 0)) ?_ S hSL hx hL
  intro k hk
  simp only [WeightDecomposition.sup_supp, Finset.mem_union] at hk
  rcases hk with (hk | hk) | hk
  · exact h.odd_higgsFermionBoostWeight_supp 0 1 0 k hk
  · exact h.odd_higgsFermionBoostWeight_supp 1 0 0 k hk
  · exact h.odd_higgsSqFermionBoostWeight_supp 0 0 0 0 k hk

/-!

## E. The classification below mass weight eight

The eight weights below eight are now settled: the sector vanishes below weight five and
at weight six, and weights five and seven are section D. So below weight eight the Yukawa
sector supplies no invariant beyond what `S` already carries, and the equivalences record
it.

No lower bound on the weight is needed, unlike the gauge-sector statement. The Yukawa
sector is the two-class sector of the Higgs and fermion generators, so both classes must
be present with a non-zero weight and the sector is already trivial at weight zero; the
scalars, which are what force `0 < w` there, never appear.

-/

/-- Below mass weight eight the Yukawa sector carries no Lorentz invariant: a Lorentz
  invariant of `sectorMassWeight {higgs, fermion} w ⊔ S` for `w < 8` lies in `S`. Weights
  below five and weight six are trivial submodules, and weights five and seven are section
  D. -/
theorem mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup (w : ℕ)
    (hw : w < 8) (S : Submodule ℂ B)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} w ⊔ S)
    (hL : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  rcases lt_or_ge w 5 with hw5 | hw5
  · rwa [h.sectorMassWeight_higgs_fermion_eq_bot_of_lt_five hw5, bot_sup_eq] at hx
  interval_cases w
  · exact h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_five_sup S hSL hx hL
  · rwa [h.sectorMassWeight_higgs_fermion_six, bot_sup_eq] at hx
  · exact h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_seven_sup S hSL hx hL

set_option linter.unusedVariables false in
/-- The classification below mass weight eight as an equivalence, in the shape of the
  gauge-sector statement `mem_massWeightSubmodule_lt_eight_sup_and_gauge_lorentz_invariant_iff`:
  an element of `sectorMassWeight {higgs, fermion} w ⊔ S` for `w < 8` is fixed by both
  groups exactly when it is itself an element of `S` fixed by both groups. Gauge stability
  of `S` is not needed, and neither is gauge invariance of `x`: the forward direction is
  the boost-weight parity argument, which uses the Lorentz group alone. -/
theorem mem_sectorMassWeight_higgs_fermion_lt_eight_sup_and_gauge_lorentz_invariant_iff
    (w : ℕ) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ ∃ y ∈ S, (∀ g : GaugeGroupI, repGauge g y = y)
          ∧ (∀ g : SL(2,ℂ), repLorentz g y = y)
          ∧ x = y := by
  constructor
  · rintro ⟨hx, hG, hL⟩
    exact ⟨x, h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw S
      hSL hx hL, hG, hL, rfl⟩
  · rintro ⟨y, hyS, hyG, hyL, rfl⟩
    exact ⟨Submodule.mem_sup_right hyS, hyG, hyL⟩

set_option linter.unusedVariables false in
/-- The same classification without the existential: below mass weight eight an element of
  `sectorMassWeight {higgs, fermion} w ⊔ S` fixed by both groups is an element of `S` fixed
  by both groups, and conversely. -/
theorem mem_sectorMassWeight_higgs_fermion_lt_eight_sup_and_gauge_lorentz_invariant_iff_mem
    (w : ℕ) (hw : w < 8) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hSL : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) (x : B) :
    (x ∈ h.sectorMassWeight {GeneratorClass.higgs, GeneratorClass.fermion} w ⊔ S
        ∧ (∀ g : GaugeGroupI, repGauge g x = x) ∧ ∀ g : SL(2,ℂ), repLorentz g x = x)
      ↔ (x ∈ S ∧ (∀ g : GaugeGroupI, repGauge g x = x)
          ∧ ∀ g : SL(2,ℂ), repLorentz g x = x) :=
  ⟨fun hx => ⟨h.mem_of_lorentz_invariant_sectorMassWeight_higgs_fermion_lt_eight_sup w hw S
    hSL hx.1 hx.2.2, hx.2⟩, fun hx => ⟨Submodule.mem_sup_right hx.1, hx.2⟩⟩

end IsCovStandardModel

end StandardModel
