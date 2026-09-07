/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.Basic
public import Physlib.Relativity.Fermions.Weyl.BoostWeight
public import Physlib.Particles.StandardModel.IsHiggsSector.Basic
/-!
# The boost weight decomposition of the fermion sector

The boost-weight analogue of `GaugeWeightDecomposition.lean`.  There the fermion symbols
were split by their *gauge* weight, the value index doing all the work; here they are split
by their *boost* weight along a spatial axis, the derivative slots and the Weyl-spinor value
index sharing the work.

Two things differ from the gauge and Higgs sectors.  First, the fermion symbols `d i l φ`,
`bard i l φ`, … carry only the `n` covariant-derivative slots, with no extra Lorentz index
to pack alongside them, so `IsLorentzCovDerivTransforms` is literally `RotatesIndices` for
each species.  Second — and this is the real difference — the value space is *not* Lorentz
trivial: a fermion symbol pairs with the dual (for the barred species the conjugate dual) of
a genuine Lorentz representation, and that dual carries boost weight of its own.  So the
`hw` fed to `boostDecomp` cannot be the trivial decomposition; it has to be an honest
decomposition of the value space.

That decomposition is built here.  Along the `z`-axis the `SL(2,ℂ)` boost is the diagonal
matrix `diag (t, t⁻¹)`, so the standard Weyl basis is a weight basis with weights `±1`
(`weylWeight`); the colour and isospin factors are inert, so the same holds for all five
value spaces.  Dualising flips the sign of a weight (`coord_mem_boostWeightSubmodule_dual`)
and conjugating leaves it alone, because the boost scales by a *real* number
(`conj_coord_mem_boostWeightSubmodule_conj_dual`).  The result is transported off the
`z`-axis by `WeightDecomposition.ofAxisTwo`, the axis boosts being conjugate.

Feeding these into `boostDecomp` gives, for each family and species, a boost weight
decomposition of the span of that species' symbols; joining the ten species and the three
families gives `derivSubmoduleBoostWeight`, a `Lorentz.BoostWeight.WeightDecomposition` of
`h.derivSubmodule n` along every axis.  The weights that occur are a light-cone slot total —
`+2` for `D₀ - Dᵢ`, `-2` for `D₀ + Dᵢ`, `0` for the two transverse directions — shifted by
the spinor weight `±1`.  In particular every fermion boost weight is **odd**
(`not_two_dvd_of_mem_derivSubmoduleBoostWeight_supp`), where the gauge and Higgs weights are
even, and its absolute value is at most `2 * n + 1`.

-/

@[expose] public section

namespace Lorentz.BoostWeight.WeightDecomposition

open MatrixGroups

variable {K : Type*} [Field K] [Algebra ℝ K] {M : Type*} [AddCommGroup M] [Module K M]

/-- **A basis of weight vectors decomposes the whole space.**  The weight-`k` piece is the
  join of the lines through those basis vectors whose weight is `k`; the support is supplied,
  any finite set containing the weights that occur. -/
noncomputable def ofWeightBasis {ι : Type*} [Fintype ι] {rep : Representation K SL(2,ℂ) M}
    {i : Fin 3} (b : Module.Basis ι K M) (wt : ι → ℤ) (s : Finset ℤ)
    (hs : ∀ j, wt j ∈ s) (hb : ∀ j, b j ∈ boostWeightSubmodule rep i (wt j)) :
    WeightDecomposition rep i ⊤ where
  piece k := ⨆ (j : ι) (_ : wt j = k), Submodule.span K {b j}
  supp := s
  piece_le k := iSup₂_le fun j hj =>
    (Submodule.span_singleton_le_iff_mem _ _).2 (hj ▸ hb j)
  piece_eq_bot k hk := iSup_eq_bot.2 fun j => iSup_eq_bot.2 fun hj =>
    absurd (hj ▸ hs j) hk
  iSup_piece := by
    refine le_antisymm le_top ?_
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (wt j) (Submodule.mem_iSup_of_mem j
      (Submodule.mem_iSup_of_mem rfl (Submodule.mem_span_singleton_self _)))

/-- **The join of a finite family of weight decompositions** along one axis: the weight-`k`
  piece of the join is the join of the weight-`k` pieces, and the support is the union of
  the supports. -/
noncomputable def iSupFintype {ι : Type*} [Fintype ι] {rep : Representation K SL(2,ℂ) M}
    {i : Fin 3} {V : ι → Submodule K M} (d : (a : ι) → WeightDecomposition rep i (V a)) :
    WeightDecomposition rep i (⨆ a, V a) where
  piece k := ⨆ a, (d a).piece k
  supp := Finset.univ.biUnion fun a => (d a).supp
  piece_le k := iSup_le fun a => (d a).piece_le k
  piece_eq_bot k hk := iSup_eq_bot.mpr fun a => (d a).piece_eq_bot k fun hm =>
    hk (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hm⟩)
  iSup_piece := by
    rw [iSup_comm]
    exact iSup_congr fun a => (d a).iSup_piece

/-- The pieces of a finite indexed join are the joins of the pieces. -/
@[simp]
lemma iSupFintype_piece {ι : Type*} [Fintype ι] {rep : Representation K SL(2,ℂ) M}
    {i : Fin 3} {V : ι → Submodule K M} (d : (a : ι) → WeightDecomposition rep i (V a))
    (k : ℤ) : (iSupFintype d).piece k = ⨆ a, (d a).piece k := rfl

/-- **Transporting a weight decomposition of the whole space from the `z`-axis to any
  axis.**  The axis boosts are conjugate, so applying the conjugating rotation carries the
  weight-`k` space of the `z`-axis onto that of the `i`-th axis. -/
noncomputable def ofAxisTwo {rep : Representation K SL(2,ℂ) M}
    (d : WeightDecomposition rep 2 ⊤) (i : Fin 3) : WeightDecomposition rep i ⊤ where
  piece k := (d.piece k).map (rep (Lorentz.SL2C.rotationZToAxis i))
  supp := d.supp
  piece_le k := by
    rintro _ ⟨u, hu, rfl⟩ t ht
    rw [← Module.End.mul_apply, ← map_mul, Lorentz.SL2C.boostAxis_eq_conj i t ht,
      inv_mul_cancel_right, map_mul, Module.End.mul_apply, d.piece_le k hu t ht, map_smul]
  piece_eq_bot k hk := by rw [d.piece_eq_bot k hk, Submodule.map_bot]
  iSup_piece := by
    rw [← Submodule.map_iSup, d.iSup_piece, Submodule.map_top]
    refine LinearMap.range_eq_top.2 fun x => ⟨rep (Lorentz.SL2C.rotationZToAxis i)⁻¹ x, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end Lorentz.BoostWeight.WeightDecomposition

namespace StandardModel

open Matrix MatrixGroups Lorentz Lorentz.BoostWeight

/-!

## A. The boost weights of the fermion value spaces

-/

/-- **The dual of a weight basis is a weight basis of the opposite weights.**  If the boost
  along the `i`-th axis scales `b j` by `t ^ wt j`, then it scales the dual coordinate
  `b.coord j` by `t ^ (-wt j)`. -/
lemma coord_mem_boostWeightSubmodule_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℂ V] {rep : Representation ℂ SL(2,ℂ) V}
    (b : Module.Basis ι ℂ V) (wt : ι → ℤ) (i : Fin 3)
    (hb : ∀ (t : ℝ) (ht : t ≠ 0) (j : ι),
      rep (SL2C.boostAxis i t ht) (b j) = ((t : ℝ) : ℂ) ^ (wt j) • b j) (j : ι) :
    b.coord j ∈ boostWeightSubmodule rep.dual i (-(wt j)) := by
  intro t ht
  refine b.ext fun k => ?_
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    SL2C.boostAxis_inv, hb _ (inv_ne_zero ht) k, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Complex.ofReal_inv,
    show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl]
  by_cases hjk : j = k
  · rw [hjk]
    simp
  · simp only [Finsupp.single_eq_of_ne hjk, mul_zero]

/-- **The conjugate-dual of a weight basis is a weight basis of the opposite weights.**  The
  axis boosts scale by a real number, so conjugating the value space leaves the weights
  alone and only dualising flips their sign. -/
lemma conj_coord_mem_boostWeightSubmodule_conj_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℂ V] {rep : Representation ℂ SL(2,ℂ) V}
    (b : Module.Basis ι ℂ V) (wt : ι → ℤ) (i : Fin 3)
    (hb : ∀ (t : ℝ) (ht : t ≠ 0) (j : ι),
      rep (SL2C.boostAxis i t ht) (b j) = ((t : ℝ) : ℂ) ^ (wt j) • b j) (j : ι) :
    b.conj.coord j ∈ boostWeightSubmodule rep.conj.dual i (-(wt j)) := by
  intro t ht
  refine b.conj.ext fun k => ?_
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    SL2C.boostAxis_inv, Representation.conj_apply, Module.Basis.conj_apply,
    LinearEquiv.symm_apply_apply, hb _ (inv_ne_zero ht) k, LinearEquiv.map_smulₛₗ,
    ← Module.Basis.conj_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, map_zpow₀,
    Complex.ofReal_inv, show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl]
  by_cases hjk : j = k
  · rw [hjk]
    simp
  · simp only [Finsupp.single_eq_of_ne hjk, mul_zero]











/-!

## B. The weight decompositions of the dual value spaces

-/

/-- **The boost weight decomposition of the dual of a value space with a weight basis.**
  The dual coordinates carry the opposite weights, and the `z`-axis decomposition is carried
  to every axis by `ofAxisTwo`. -/
noncomputable def dualBoostWeightOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (rep : Representation ℂ SL(2,ℂ) V)
    (b : Module.Basis ι ℂ V) (wt : ι → ℤ)
    (hb : ∀ (t : ℝ) (ht : t ≠ 0) (j : ι),
      rep (SL2C.boostAxis 2 t ht) (b j) = ((t : ℝ) : ℂ) ^ (wt j) • b j)
    (s : Finset ℤ) (hs : ∀ j, -(wt j) ∈ s) (i : Fin 3) :
    WeightDecomposition rep.dual i ⊤ :=
  (WeightDecomposition.ofWeightBasis (i := 2) b.dualBasis (fun j => -(wt j)) s hs
    (fun j => by
      rw [Module.Basis.coe_dualBasis]
      exact coord_mem_boostWeightSubmodule_dual b wt 2 hb j)).ofAxisTwo i

/-- **The boost weight decomposition of the conjugate-dual of a value space with a weight
  basis.**  The axis boosts scale by real numbers, so conjugating leaves the weights alone
  and only dualising flips their sign. -/
noncomputable def conjDualBoostWeightOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (rep : Representation ℂ SL(2,ℂ) V)
    (b : Module.Basis ι ℂ V) (wt : ι → ℤ)
    (hb : ∀ (t : ℝ) (ht : t ≠ 0) (j : ι),
      rep (SL2C.boostAxis 2 t ht) (b j) = ((t : ℝ) : ℂ) ^ (wt j) • b j)
    (s : Finset ℤ) (hs : ∀ j, -(wt j) ∈ s) (i : Fin 3) :
    WeightDecomposition rep.conj.dual i ⊤ :=
  (WeightDecomposition.ofWeightBasis (i := 2) b.conj.dualBasis (fun j => -(wt j)) s hs
    (fun j => by
      rw [Module.Basis.coe_dualBasis]
      exact conj_coord_mem_boostWeightSubmodule_conj_dual b wt 2 hb j)).ofAxisTwo i

/-!

## C. The fermion symbols rotate their derivative indices

-/

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) →
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

include h in
/-- Every derivative slot of a `d` symbol is a Lorentz vector index. -/
lemma rotatesIndices_d (f : Fin 3) (n : ℕ) :
    RotatesIndices DownSinglet.repLorentzGroup.dual repLorentz (d (n := n) f) :=
  fun g l φ => h.repLorentz_d f g n l φ

include h in
/-- Every derivative slot of a `bard` symbol is a Lorentz vector index. -/
lemma rotatesIndices_bard (f : Fin 3) (n : ℕ) :
    RotatesIndices DownSinglet.repLorentzGroup.conj.dual repLorentz (bard (n := n) f) :=
  fun g l φ => h.repLorentz_bard f g n l φ

include h in
/-- Every derivative slot of a `u` symbol is a Lorentz vector index. -/
lemma rotatesIndices_u (f : Fin 3) (n : ℕ) :
    RotatesIndices UpSinglet.repLorentzGroup.dual repLorentz (u (n := n) f) :=
  fun g l φ => h.repLorentz_u f g n l φ

include h in
/-- Every derivative slot of a `baru` symbol is a Lorentz vector index. -/
lemma rotatesIndices_baru (f : Fin 3) (n : ℕ) :
    RotatesIndices UpSinglet.repLorentzGroup.conj.dual repLorentz (baru (n := n) f) :=
  fun g l φ => h.repLorentz_baru f g n l φ

include h in
/-- Every derivative slot of a `Q` symbol is a Lorentz vector index. -/
lemma rotatesIndices_Q (f : Fin 3) (n : ℕ) :
    RotatesIndices QuarkDoublet.repLorentzGroup.dual repLorentz (Q (n := n) f) :=
  fun g l φ => h.repLorentz_Q f g n l φ

include h in
/-- Every derivative slot of a `barQ` symbol is a Lorentz vector index. -/
lemma rotatesIndices_barQ (f : Fin 3) (n : ℕ) :
    RotatesIndices QuarkDoublet.repLorentzGroup.conj.dual repLorentz (barQ (n := n) f) :=
  fun g l φ => h.repLorentz_barQ f g n l φ

include h in
/-- Every derivative slot of an `L` symbol is a Lorentz vector index. -/
lemma rotatesIndices_L (f : Fin 3) (n : ℕ) :
    RotatesIndices LeptonDoublet.repLorentzGroup.dual repLorentz (L (n := n) f) :=
  fun g l φ => h.repLorentz_L f g n l φ

include h in
/-- Every derivative slot of a `barL` symbol is a Lorentz vector index. -/
lemma rotatesIndices_barL (f : Fin 3) (n : ℕ) :
    RotatesIndices LeptonDoublet.repLorentzGroup.conj.dual repLorentz (barL (n := n) f) :=
  fun g l φ => h.repLorentz_barL f g n l φ

include h in
/-- Every derivative slot of an `e` symbol is a Lorentz vector index. -/
lemma rotatesIndices_e (f : Fin 3) (n : ℕ) :
    RotatesIndices LeptonSinglet.repLorentzGroup.dual repLorentz (e (n := n) f) :=
  fun g l φ => h.repLorentz_e f g n l φ

include h in
/-- Every derivative slot of a `bare` symbol is a Lorentz vector index. -/
lemma rotatesIndices_bare (f : Fin 3) (n : ℕ) :
    RotatesIndices LeptonSinglet.repLorentzGroup.conj.dual repLorentz (bare (n := n) f) :=
  fun g l φ => h.repLorentz_bare f g n l φ

/-!

## D. The boost weight decomposition of each species

-/

/-- **The boost weight decomposition of the span of the `d` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_d (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (d f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (d (n := n) f)
    (h.rotatesIndices_d f n) i
    (dualBoostWeightOfBasis DownSinglet.repLorentzGroup DownSinglet.basis
      (fun j : Fin 2 × Fin 3 => weylWeight j.1) downSinglet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `bard` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_bard (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (bard f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (bard (n := n) f)
    (h.rotatesIndices_bard f n) i
    (conjDualBoostWeightOfBasis DownSinglet.repLorentzGroup DownSinglet.basis
      (fun j : Fin 2 × Fin 3 => weylWeight j.1) downSinglet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `u` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_u (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (u f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (u (n := n) f)
    (h.rotatesIndices_u f n) i
    (dualBoostWeightOfBasis UpSinglet.repLorentzGroup UpSinglet.basis
      (fun j : Fin 2 × Fin 3 => weylWeight j.1) upSinglet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `baru` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_baru (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (baru f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (baru (n := n) f)
    (h.rotatesIndices_baru f n) i
    (conjDualBoostWeightOfBasis UpSinglet.repLorentzGroup UpSinglet.basis
      (fun j : Fin 2 × Fin 3 => weylWeight j.1) upSinglet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `Q` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_Q (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (Q f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (Q (n := n) f)
    (h.rotatesIndices_Q f n) i
    (dualBoostWeightOfBasis QuarkDoublet.repLorentzGroup QuarkDoublet.basis
      (fun j : Fin 2 × Fin 3 × Fin 2 => weylWeight j.1)
      quarkDoublet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `barQ` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_barQ (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (barQ f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (barQ (n := n) f)
    (h.rotatesIndices_barQ f n) i
    (conjDualBoostWeightOfBasis QuarkDoublet.repLorentzGroup QuarkDoublet.basis
      (fun j : Fin 2 × Fin 3 × Fin 2 => weylWeight j.1)
      quarkDoublet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `L` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_L (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (L f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (L (n := n) f)
    (h.rotatesIndices_L f n) i
    (dualBoostWeightOfBasis LeptonDoublet.repLorentzGroup LeptonDoublet.basis
      (fun j : Fin 2 × Fin 2 => weylWeight j.1) leptonDoublet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `barL` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_barL (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (barL f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (barL (n := n) f)
    (h.rotatesIndices_barL f n) i
    (conjDualBoostWeightOfBasis LeptonDoublet.repLorentzGroup LeptonDoublet.basis
      (fun j : Fin 2 × Fin 2 => weylWeight j.1) leptonDoublet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `e` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_e (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (e f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (e (n := n) f)
    (h.rotatesIndices_e f n) i
    (dualBoostWeightOfBasis LeptonSinglet.repLorentzGroup LeptonSinglet.basis
      (fun j : Fin 2 => weylWeight j) leptonSinglet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-- **The boost weight decomposition of the span of the `bare` symbols** of one family and a
  fixed number of covariant derivatives: each derivative slot contributes the weight of its
  light-cone direction, on top of the `±1` carried by the Weyl-spinor value index. -/
noncomputable def boostWeight_bare (f : Fin 3) (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i
      (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (bare f l)) :=
  IsHiggsSector.IsDerivativeCollection.boostDecomp (bare (n := n) f)
    (h.rotatesIndices_bare f n) i
    (conjDualBoostWeightOfBasis LeptonSinglet.repLorentzGroup LeptonSinglet.basis
      (fun j : Fin 2 => weylWeight j) leptonSinglet_repLorentzGroup_boostAxis_two_basis
      ({-1, 1} : Finset ℤ) (fun _ => neg_weylWeight_mem _) i)

/-!

## E. The boost weight decomposition of the fermion derivative submodules

-/

/-- Reassociating the join: taking each species' symbols over all derivative slots first and
  joining the ten species afterwards recovers the fermion derivative submodule. -/
lemma iSup_iSup_range_eq_derivSubmodule (n : ℕ) :
    (⨆ f : Fin 3,
      ((((((((((⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (d f l)) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (bard f l))) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (u f l))) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (baru f l))) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (Q f l))) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (barQ f l))) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (L f l))) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (barL f l))) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (e f l))) ⊔
        (⨆ l : Fin n → Fin 1 ⊕ Fin 3, LinearMap.range (bare f l)))) = h.derivSubmodule n := by
  rw [derivSubmodule]
  exact iSup_congr fun f => by simp only [iSup_sup_eq]

/-- **The boost weight decomposition of the fermion derivative submodules**, along any
  spatial axis and for any number of covariant derivatives.  The weight-`k` piece is the
  join, over the three families, the ten species and the light-cone multi-indices, of the
  images of the value weight spaces: a derivative slot of light-cone type `c j` contributes
  `lightConeWeight (c j)` and the Weyl-spinor value index contributes `±1`. -/
noncomputable def derivSubmoduleBoostWeight (n : ℕ) (i : Fin 3) :
    WeightDecomposition repLorentz i (h.derivSubmodule n) :=
  (WeightDecomposition.iSupFintype fun f : Fin 3 =>
    (((((((((h.boostWeight_d f n i).sup (h.boostWeight_bard f n i)).sup
      (h.boostWeight_u f n i)).sup (h.boostWeight_baru f n i)).sup
      (h.boostWeight_Q f n i)).sup (h.boostWeight_barQ f n i)).sup
      (h.boostWeight_L f n i)).sup (h.boostWeight_barL f n i)).sup
      (h.boostWeight_e f n i)).sup
      (h.boostWeight_bare f n i)).copy (h.iSup_iSup_range_eq_derivSubmodule n)

/-!

## F. The boost weights that occur

-/

/-- **The boost weights carried by the fermion symbols with `n` covariant derivatives**: a
  total of light-cone slot weights — `+2`, `-2` or `0` per slot — shifted by the `±1` of the
  Weyl-spinor value index. -/
def fermionBoostWeights (n : ℕ) : Finset ℤ :=
  (Finset.univ ×ˢ ({-1, 1} : Finset ℤ)).image
    fun p : (Fin n → Fin 4) × ℤ => (∑ j, lightConeWeight (p.1 j)) + p.2

/-- Every fermion boost weight is odd: the derivative slots contribute an even total and the
  spinor index contributes `±1`. -/
lemma not_two_dvd_of_mem_fermionBoostWeights {n : ℕ} {k : ℤ}
    (hk : k ∈ fermionBoostWeights n) : ¬ (2 : ℤ) ∣ k := by
  rw [fermionBoostWeights, Finset.mem_image] at hk
  obtain ⟨⟨c, b⟩, hb, rfl⟩ := hk
  dsimp only
  have hbmem : b ∈ ({-1, 1} : Finset ℤ) := (Finset.mem_product.1 hb).2
  have heven : (2 : ℤ) ∣ ∑ j, lightConeWeight (c j) :=
    Finset.dvd_sum fun j _ => by
      simp only [lightConeWeight]
      split_ifs <;> norm_num
  obtain ⟨m, hm⟩ := heven
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
  rcases hbmem with rfl | rfl <;> rw [hm] <;> omega

/-- Every fermion boost weight has absolute value at most `2 * n + 1`: each of the `n`
  derivative slots contributes at most `2`, and the spinor index one more. -/
lemma abs_le_of_mem_fermionBoostWeights {n : ℕ} {k : ℤ}
    (hk : k ∈ fermionBoostWeights n) : |k| ≤ 2 * n + 1 := by
  rw [fermionBoostWeights, Finset.mem_image] at hk
  obtain ⟨⟨c, b⟩, hb, rfl⟩ := hk
  dsimp only
  have hbmem : b ∈ ({-1, 1} : Finset ℤ) := (Finset.mem_product.1 hb).2
  have hsum : |∑ j, lightConeWeight (c j)| ≤ 2 * n :=
    calc |∑ j, lightConeWeight (c j)|
        ≤ ∑ j, |lightConeWeight (c j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, (2 : ℤ) := Finset.sum_le_sum fun j _ => by
          simp only [lightConeWeight]
          split_ifs <;> norm_num
      _ = 2 * n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
  rw [abs_le] at hsum
  rcases hbmem with rfl | rfl <;> rw [abs_le] <;> omega

/-- The support of the d decomposition. -/
lemma boostWeight_d_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_d f n i).supp = fermionBoostWeights n := rfl

/-- The support of the bard decomposition. -/
lemma boostWeight_bard_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_bard f n i).supp = fermionBoostWeights n := rfl

/-- The support of the u decomposition. -/
lemma boostWeight_u_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_u f n i).supp = fermionBoostWeights n := rfl

/-- The support of the baru decomposition. -/
lemma boostWeight_baru_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_baru f n i).supp = fermionBoostWeights n := rfl

/-- The support of the Q decomposition. -/
lemma boostWeight_Q_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_Q f n i).supp = fermionBoostWeights n := rfl

/-- The support of the barQ decomposition. -/
lemma boostWeight_barQ_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_barQ f n i).supp = fermionBoostWeights n := rfl

/-- The support of the L decomposition. -/
lemma boostWeight_L_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_L f n i).supp = fermionBoostWeights n := rfl

/-- The support of the barL decomposition. -/
lemma boostWeight_barL_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_barL f n i).supp = fermionBoostWeights n := rfl

/-- The support of the e decomposition. -/
lemma boostWeight_e_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_e f n i).supp = fermionBoostWeights n := rfl

/-- The support of the bare decomposition. -/
lemma boostWeight_bare_supp (f : Fin 3) (n : ℕ) (i : Fin 3) :
    (h.boostWeight_bare f n i).supp = fermionBoostWeights n := rfl

/-- **The support of the boost weight decomposition of the fermion derivative
  submodules**: the light-cone slot totals shifted by the spinor weight `±1`.  It does not
  depend on the axis or on the family. -/
lemma derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) :
    (h.derivSubmoduleBoostWeight n i).supp = fermionBoostWeights n := by
  have hconst : ∀ t : Finset ℤ, (Finset.univ.biUnion fun _ : Fin 3 => t) = t := by
    intro t
    ext x
    simp
  show (Finset.univ.biUnion fun _ : Fin 3 =>
    ((((((((fermionBoostWeights n ∪ fermionBoostWeights n) ∪ fermionBoostWeights n) ∪
      fermionBoostWeights n) ∪ fermionBoostWeights n) ∪ fermionBoostWeights n) ∪
      fermionBoostWeights n) ∪ fermionBoostWeights n) ∪ fermionBoostWeights n) ∪
      fermionBoostWeights n) = fermionBoostWeights n
  simp only [Finset.union_self]
  exact hconst _

/-- **Every boost weight occurring in a fermion derivative submodule is odd.**  This is the
  boost-weight shadow of the spin-statistics split: the bosonic sectors carry even weights,
  the fermionic ones odd. -/
lemma not_two_dvd_of_mem_derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) {k : ℤ}
    (hk : k ∈ (h.derivSubmoduleBoostWeight n i).supp) : ¬ (2 : ℤ) ∣ k :=
  not_two_dvd_of_mem_fermionBoostWeights ((h.derivSubmoduleBoostWeight_supp n i) ▸ hk)

/-- **Every boost weight occurring in a fermion derivative submodule has absolute value at
  most `2 * n + 1`**: `2` from each of the `n` derivative slots and `1` from the spinor
  index. -/
lemma abs_le_of_mem_derivSubmoduleBoostWeight_supp (n : ℕ) (i : Fin 3) {k : ℤ}
    (hk : k ∈ (h.derivSubmoduleBoostWeight n i).supp) : |k| ≤ 2 * n + 1 :=
  abs_le_of_mem_fermionBoostWeights ((h.derivSubmoduleBoostWeight_supp n i) ▸ hk)

/-!

## G. The light-cone fermion symbols and their boost weights

The unconditional decomposition above is assembled from the following pointwise statement:
a light-cone symbol evaluated at a value vector of definite boost weight `b` is a boost
eigenvector, of weight `(∑ j, lightConeWeight (c j)) + b`.

-/

include h in
/-- **The light-cone `d` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_d_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ DownSinglet}
    (hφ : φ ∈ boostWeightSubmodule DownSinglet.repLorentzGroup.dual i b) :
    lightConeDeriv (d (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_d f n) i c hφ

include h in
/-- **The light-cone `bard` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_bard_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ (ConjModule DownSinglet)}
    (hφ : φ ∈ boostWeightSubmodule DownSinglet.repLorentzGroup.conj.dual i b) :
    lightConeDeriv (bard (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_bard f n) i c hφ

include h in
/-- **The light-cone `u` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_u_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ UpSinglet}
    (hφ : φ ∈ boostWeightSubmodule UpSinglet.repLorentzGroup.dual i b) :
    lightConeDeriv (u (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_u f n) i c hφ

include h in
/-- **The light-cone `baru` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_baru_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ (ConjModule UpSinglet)}
    (hφ : φ ∈ boostWeightSubmodule UpSinglet.repLorentzGroup.conj.dual i b) :
    lightConeDeriv (baru (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_baru f n) i c hφ

include h in
/-- **The light-cone `Q` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_Q_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ QuarkDoublet}
    (hφ : φ ∈ boostWeightSubmodule QuarkDoublet.repLorentzGroup.dual i b) :
    lightConeDeriv (Q (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_Q f n) i c hφ

include h in
/-- **The light-cone `barQ` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_barQ_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ (ConjModule QuarkDoublet)}
    (hφ : φ ∈ boostWeightSubmodule QuarkDoublet.repLorentzGroup.conj.dual i b) :
    lightConeDeriv (barQ (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_barQ f n) i c hφ

include h in
/-- **The light-cone `L` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_L_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ LeptonDoublet}
    (hφ : φ ∈ boostWeightSubmodule LeptonDoublet.repLorentzGroup.dual i b) :
    lightConeDeriv (L (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_L f n) i c hφ

include h in
/-- **The light-cone `barL` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_barL_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ (ConjModule LeptonDoublet)}
    (hφ : φ ∈ boostWeightSubmodule LeptonDoublet.repLorentzGroup.conj.dual i b) :
    lightConeDeriv (barL (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_barL f n) i c hφ

include h in
/-- **The light-cone `e` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_e_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ LeptonSinglet}
    (hφ : φ ∈ boostWeightSubmodule LeptonSinglet.repLorentzGroup.dual i b) :
    lightConeDeriv (e (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_e f n) i c hφ

include h in
/-- **The light-cone `bare` symbols have definite boost weight.**  Each derivative slot
  contributes the weight of its light-cone direction — `+2` for `D₀ - Dᵢ`, `-2` for
  `D₀ + Dᵢ`, `0` for the two transverse directions — on top of the weight `b` carried by the
  value index. -/
lemma lightConeDeriv_bare_mem (f : Fin 3) {n : ℕ} (i : Fin 3) (c : Fin n → Fin 4) {b : ℤ}
    {φ : Module.Dual ℂ (ConjModule LeptonSinglet)}
    (hφ : φ ∈ boostWeightSubmodule LeptonSinglet.repLorentzGroup.conj.dual i b) :
    lightConeDeriv (bare (n := n) f) i c φ ∈
      boostWeightSubmodule repLorentz i ((∑ j, lightConeWeight (c j)) + b) :=
  lightConeDeriv_mem _ (h.rotatesIndices_bare f n) i c hφ

end IsFermionSector

end StandardModel

end
