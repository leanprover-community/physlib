/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.Basic
public import Physlib.Relativity.LorentzGroup.Invariants.Centre
/-!
# The centre of `SL(2,ℂ)` on the fermion sector

The fermion symbols are the only Standard Model generators of half-integer spin, and this
file records what that costs them: the element `-1` of `SL(2,ℂ)` acts on every fermion
derivative submodule by `-1`, where it acts on the Higgs and gauge ones by `+1`.

The mechanism is uniform across the ten species. A fermion symbol `d i l φ` carries `n`
covariant-derivative slots, each a four-vector index, and one value index in the dual of a
Weyl-based representation. The derivative slots see `-1` through the Lorentz matrix, which is
the identity there (`SL2C.toLorentzGroup_neg_one`), so they do not move at all; the value
index sees it through `rep.dual`, and `repLorentzGroup_neg_one` says that the Weyl factor
turns it into a sign. `Invariants.range_le_centreEigenspace_neg_one` does this once for an
arbitrary symbol family; section A applies it to the ten species and section B joins them.

This is the half-integer-spin obstruction of `Invariants/Centre.lean` in the form the Yukawa
and gauge-fermion classifications need: a product with an odd number of fermion factors
inherits the sign, and a subspace of sign `-1` carries no Lorentz invariant.

- A. The ten species
- B. The fermion derivative submodules

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz Lorentz.Invariants

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

/-!

## A. The ten species

Each species feeds `range_le_centreEigenspace_neg_one` with its own Lorentz law and the sign
of its value space. The five unbarred species are Weyl-valued and the five barred ones are
conjugate Weyl-valued; conjugation does not move a real sign, so all ten carry `-1`.

-/

include h in
/-- The `d` symbols carry the sign `-1`. -/
lemma range_d_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (d f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_d f)
    DownSinglet.repLorentzGroup_neg_one l

include h in
/-- The `bard` symbols carry the sign `-1`. -/
lemma range_bard_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bard f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_bard f)
    DownSinglet.repLorentzGroup_conj_neg_one l

include h in
/-- The `u` symbols carry the sign `-1`. -/
lemma range_u_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (u f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_u f)
    UpSinglet.repLorentzGroup_neg_one l

include h in
/-- The `baru` symbols carry the sign `-1`. -/
lemma range_baru_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (baru f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_baru f)
    UpSinglet.repLorentzGroup_conj_neg_one l

include h in
/-- The `Q` symbols carry the sign `-1`. -/
lemma range_Q_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (Q f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_Q f)
    QuarkDoublet.repLorentzGroup_neg_one l

include h in
/-- The `barQ` symbols carry the sign `-1`. -/
lemma range_barQ_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barQ f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_barQ f)
    QuarkDoublet.repLorentzGroup_conj_neg_one l

include h in
/-- The `L` symbols carry the sign `-1`. -/
lemma range_L_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (L f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_L f)
    LeptonDoublet.repLorentzGroup_neg_one l

include h in
/-- The `barL` symbols carry the sign `-1`. -/
lemma range_barL_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (barL f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_barL f)
    LeptonDoublet.repLorentzGroup_conj_neg_one l

include h in
/-- The `e` symbols carry the sign `-1`. -/
lemma range_e_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (e f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_e f)
    LeptonSinglet.repLorentzGroup_neg_one l

include h in
/-- The `bare` symbols carry the sign `-1`. -/
lemma range_bare_le_centreEigenspace (f : Fin 3) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) :
    LinearMap.range (bare f l) ≤ centreEigenspace repLorentz (-1) :=
  range_le_centreEigenspace_neg_one (h.repLorentz_bare f)
    LeptonSinglet.repLorentzGroup_conj_neg_one l

/-!

## B. The fermion derivative submodules

The derivative submodule is the join over the three families, the derivative slots and the ten
species of the ranges of section A, and an eigenspace is closed under joins.

-/

include h in
/-- **The centre of `SL(2,ℂ)` acts on the fermion derivative submodules by `-1`**, for any
  number of covariant derivatives: every fermion symbol carries one Weyl-spinor value index,
  and the derivative slots are inert at the centre. -/
theorem derivSubmodule_le_centreEigenspace (n : ℕ) :
    h.derivSubmodule n ≤ centreEigenspace repLorentz (-1) := by
  rw [derivSubmodule]
  refine iSup_le fun f => iSup_le fun l => ?_
  refine sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le (sup_le
    (h.range_d_le_centreEigenspace f l) (h.range_bard_le_centreEigenspace f l))
    (h.range_u_le_centreEigenspace f l)) (h.range_baru_le_centreEigenspace f l))
    (h.range_Q_le_centreEigenspace f l)) (h.range_barQ_le_centreEigenspace f l))
    (h.range_L_le_centreEigenspace f l)) (h.range_barL_le_centreEigenspace f l))
    (h.range_e_le_centreEigenspace f l)) (h.range_bare_le_centreEigenspace f l)

end IsFermionSector

end StandardModel
