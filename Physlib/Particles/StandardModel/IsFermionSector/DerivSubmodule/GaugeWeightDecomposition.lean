/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
/-!
# The gauge weight decomposition of the fermion sector

The gauge torus acts diagonally on the basis of each fermion value space, with
weights given by the colour and isospin weights of the fundamental representations
and the species' hypercharge. Through the dual (and, for the barred species, the
conjugate-dual) this makes every symbol component a simultaneous eigenvector, and the
derivative submodules of the fermion sector decompose by gauge weight
(`derivSubmoduleGaugeWeight`), for every number of covariant derivatives.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

/-!

## A. The torus weights of the fermion value spaces

-/

/-!

## B. The torus action on the value-space bases

-/

/-!

## C. Ranges of symbol maps

-/

section Bridges

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]


lemma range_eq_iSup_span {M : Type} [AddCommGroup M] [Module ℂ M]
    (b : Module.Basis ι ℂ V) (f : Module.Dual ℂ V →ₗ[ℂ] M) :
    LinearMap.range f = ⨆ j, Submodule.span ℂ {f (b.coord j)} := by
  rw [LinearMap.range_eq_map, ← b.dualBasis.span_eq, Submodule.map_span, ← Set.range_comp]
  rw [show (⇑f ∘ ⇑b.dualBasis) = fun j => f (b.coord j) from funext fun j => by
    simp [Module.Basis.coe_dualBasis]]
  rw [Submodule.span_range_eq_iSup]

end Bridges

/-!

## D. The gauge weight decomposition of the derivative submodules

-/

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
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
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

include h in
/-- The gauge torus acts diagonally on the `d` symbol components. -/
lemma repGauge_gaugeTorusGen_d (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (d f l ((DownSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(DownSinglet.valueGaugeWeight j)) i) • d f l ((DownSinglet.basis).coord j) := by
  rw [h.repGauge_d, DownSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `bard` symbol components. -/
lemma repGauge_gaugeTorusGen_bard (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (bard f l ((DownSinglet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) • bard f l ((DownSinglet.basis.conj).coord j) := by
  rw [h.repGauge_bard, DownSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

include h in
/-- The gauge torus acts diagonally on the `u` symbol components. -/
lemma repGauge_gaugeTorusGen_u (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (u f l ((UpSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(UpSinglet.valueGaugeWeight j)) i) • u f l ((UpSinglet.basis).coord j) := by
  rw [h.repGauge_u, UpSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `baru` symbol components. -/
lemma repGauge_gaugeTorusGen_baru (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (baru f l ((UpSinglet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) • baru f l ((UpSinglet.basis.conj).coord j) := by
  rw [h.repGauge_baru, UpSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

include h in
/-- The gauge torus acts diagonally on the `Q` symbol components. -/
lemma repGauge_gaugeTorusGen_Q (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen i) (Q f l ((QuarkDoublet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(QuarkDoublet.valueGaugeWeight j)) i) • Q f l ((QuarkDoublet.basis).coord j) := by
  rw [h.repGauge_Q, QuarkDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `barQ` symbol components. -/
lemma repGauge_gaugeTorusGen_barQ (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen i) (barQ f l ((QuarkDoublet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) • barQ f l ((QuarkDoublet.basis.conj).coord j) := by
  rw [h.repGauge_barQ, QuarkDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

include h in
/-- The gauge torus acts diagonally on the `L` symbol components. -/
lemma repGauge_gaugeTorusGen_L (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen i) (L f l ((LeptonDoublet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonDoublet.valueGaugeWeight j)) i) • L f l ((LeptonDoublet.basis).coord j) := by
  rw [h.repGauge_L, LeptonDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `barL` symbol components. -/
lemma repGauge_gaugeTorusGen_barL (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen i) (barL f l ((LeptonDoublet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) i) • barL f l ((LeptonDoublet.basis.conj).coord j) := by
  rw [h.repGauge_barL, LeptonDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

include h in
/-- The gauge torus acts diagonally on the `e` symbol components. -/
lemma repGauge_gaugeTorusGen_e (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen i) (e f l ((LeptonSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonSinglet.valueGaugeWeight j)) i) • e f l ((LeptonSinglet.basis).coord j) := by
  rw [h.repGauge_e, LeptonSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `bare` symbol components. -/
lemma repGauge_gaugeTorusGen_bare (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen i) (bare f l ((LeptonSinglet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) • bare f l ((LeptonSinglet.basis.conj).coord j) := by
  rw [h.repGauge_bare, LeptonSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

/-- The gauge weight decomposition of the range of the `d` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_d (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (d f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(DownSinglet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_d i f l j))
    _ (range_eq_iSup_span (DownSinglet.basis) (d f l))

/-- The gauge weight decomposition of the range of the `bard` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_bard (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (bard f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (DownSinglet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_bard i f l j))
    _ (range_eq_iSup_span (DownSinglet.basis.conj) (bard f l))

/-- The gauge weight decomposition of the range of the `u` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_u (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (u f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(UpSinglet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_u i f l j))
    _ (range_eq_iSup_span (UpSinglet.basis) (u f l))

/-- The gauge weight decomposition of the range of the `baru` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_baru (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (baru f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (UpSinglet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_baru i f l j))
    _ (range_eq_iSup_span (UpSinglet.basis.conj) (baru f l))

/-- The gauge weight decomposition of the range of the `Q` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_Q (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (Q f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(QuarkDoublet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_Q i f l j))
    _ (range_eq_iSup_span (QuarkDoublet.basis) (Q f l))

/-- The gauge weight decomposition of the range of the `barQ` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_barQ (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (barQ f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (QuarkDoublet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_barQ i f l j))
    _ (range_eq_iSup_span (QuarkDoublet.basis.conj) (barQ f l))

/-- The gauge weight decomposition of the range of the `L` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_L (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (L f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(LeptonDoublet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_L i f l j))
    _ (range_eq_iSup_span (LeptonDoublet.basis) (L f l))

/-- The gauge weight decomposition of the range of the `barL` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_barL (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (barL f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (LeptonDoublet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_barL i f l j))
    _ (range_eq_iSup_span (LeptonDoublet.basis.conj) (barL f l))

/-- The gauge weight decomposition of the range of the `e` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_e (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (e f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(LeptonSinglet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_e i f l j))
    _ (range_eq_iSup_span (LeptonSinglet.basis) (e f l))

/-- The gauge weight decomposition of the range of the `bare` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_bare (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (bare f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (LeptonSinglet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_bare i f l j))
    _ (range_eq_iSup_span (LeptonSinglet.basis.conj) (bare f l))

/-- **The gauge weight decomposition of the fermion derivative submodules**, for any
  number of covariant derivatives: the join, over families, derivative slots and the
  ten species, of the spans of the symbol components, each of pure gauge weight.

  This is an instance: its statement mentions `h`, so unification against the goal
  recovers the sector and with it all the implicit data of `IsFermionSector`.  The
  `rangeGaugeWeight_*` decompositions above cannot be instances for exactly that
  reason — their statements name only the symbol maps, leaving the rest of the
  structure's parameters undetermined. -/
@[implicit_reducible]
noncomputable instance derivSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition repGauge (h.derivSubmodule n) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun f : Fin 3 =>
      GaugeWeightDecomposition.iSup hrepGauge_mul fun l : Fin n → Fin 1 ⊕ Fin 3 =>
      GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := h.rangeGaugeWeight_d f l)
        (d' := h.rangeGaugeWeight_bard f l))
        (d' := h.rangeGaugeWeight_u f l))
        (d' := h.rangeGaugeWeight_baru f l))
        (d' := h.rangeGaugeWeight_Q f l))
        (d' := h.rangeGaugeWeight_barQ f l))
        (d' := h.rangeGaugeWeight_L f l))
        (d' := h.rangeGaugeWeight_barL f l))
        (d' := h.rangeGaugeWeight_e f l))
        (d' := h.rangeGaugeWeight_bare f l))
    _ (by rw [derivSubmodule])


/-!

## The support of the decomposition

-/

/-- The gauge weights carried by the fermion symbols: for each species the image of
  its value weights, negated for the unbarred species (the symbols pair with the dual
  of the value space) and taken as they are for the barred ones. -/
def fermionGaugeWeights : Finset GaugeWeight :=
  Finset.univ.image (fun j : Fin 2 × Fin 3 => -(DownSinglet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 => DownSinglet.valueGaugeWeight j)
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 => -(UpSinglet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 => UpSinglet.valueGaugeWeight j)
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 × Fin 2 => -(QuarkDoublet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 3 × Fin 2 => QuarkDoublet.valueGaugeWeight j)
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 2 => -(LeptonDoublet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 × Fin 2 => LeptonDoublet.valueGaugeWeight j)
    ∪ Finset.univ.image (fun j : Fin 2 => -(LeptonSinglet.valueGaugeWeight j))
    ∪ Finset.univ.image (fun j : Fin 2 => LeptonSinglet.valueGaugeWeight j)

/-- The support of the `d` range decomposition. -/
lemma rangeGaugeWeight_d_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_d f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 => -(DownSinglet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `bard` range decomposition. -/
lemma rangeGaugeWeight_bard_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_bard f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 => DownSinglet.valueGaugeWeight j) :=
  Finset.biUnion_singleton
/-- The support of the `u` range decomposition. -/
lemma rangeGaugeWeight_u_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_u f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 => -(UpSinglet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `baru` range decomposition. -/
lemma rangeGaugeWeight_baru_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_baru f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 => UpSinglet.valueGaugeWeight j) :=
  Finset.biUnion_singleton
/-- The support of the `Q` range decomposition. -/
lemma rangeGaugeWeight_Q_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_Q f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 × Fin 2 => -(QuarkDoublet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `barQ` range decomposition. -/
lemma rangeGaugeWeight_barQ_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_barQ f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 3 × Fin 2 => QuarkDoublet.valueGaugeWeight j) :=
  Finset.biUnion_singleton
/-- The support of the `L` range decomposition. -/
lemma rangeGaugeWeight_L_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_L f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 2 => -(LeptonDoublet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `barL` range decomposition. -/
lemma rangeGaugeWeight_barL_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_barL f l).supp
      = Finset.univ.image (fun j : Fin 2 × Fin 2 => LeptonDoublet.valueGaugeWeight j) :=
  Finset.biUnion_singleton
/-- The support of the `e` range decomposition. -/
lemma rangeGaugeWeight_e_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_e f l).supp
      = Finset.univ.image (fun j : Fin 2 => -(LeptonSinglet.valueGaugeWeight j)) :=
  Finset.biUnion_singleton
/-- The support of the `bare` range decomposition. -/
lemma rangeGaugeWeight_bare_supp (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    (h.rangeGaugeWeight_bare f l).supp
      = Finset.univ.image (fun j : Fin 2 => LeptonSinglet.valueGaugeWeight j) :=
  Finset.biUnion_singleton

/-- **The support of the gauge weight decomposition of the fermion derivative
  submodules**: the gauge weights of the ten species, independent of the number of
  covariant derivatives. -/
lemma derivSubmoduleGaugeWeight_supp (n : ℕ) :
    (h.derivSubmoduleGaugeWeight n).supp = fermionGaugeWeights := by
  have hconst : ∀ (t : Finset GaugeWeight),
      (Finset.univ.biUnion fun _ : Fin 3 =>
        Finset.univ.biUnion fun _ : Fin n → Fin 1 ⊕ Fin 3 => t) = t := by
    intro t
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨_, _, hx⟩ => hx, fun hx => ⟨0, fun _ => Sum.inl 0, hx⟩⟩
  show (Finset.univ.biUnion fun _ : Fin 3 =>
    Finset.univ.biUnion fun _ : Fin n → Fin 1 ⊕ Fin 3 => fermionGaugeWeights)
      = fermionGaugeWeights
  exact hconst _

end IsFermionSector

end StandardModel
