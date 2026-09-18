/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D6_Fiedler
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathGap.D7_Niven
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.DimUncertainty.D8_Szego
public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.DimUncertainty.D9_Monotonia

/-!
# D10 — Joint certificate: Fiedler + Niven + Szegő in `H_d`

Gathers, in a single citable certificate, the three pillars that rest on
the common habitat `H_d = ℂ^d` (`D0_Habitat.lean`): the Fiedler spectral
decomposition (`D6_Fiedler.lean`), the Niven theorem (`D7_Niven.lean`),
and the Szegő limit with gap positivity (`D8_Szego.lean`). This is the
terminal theorem of the package: the mathematics proved in this
repository ends here.

# Shielding `δ_geom(d)` in the finite Hilbert space `H_d`

**Habitat:** \(H_d=\mathtt{EuclideanSpace}\,\mathbb{C}\,(\mathtt{Fin}\,d)\).
This space is never left: it is where the framework derivation lives.

**Shield triad** (all on the discrete setting):

| Shield | Lean content |
|--------|-------------|
| **Fiedler** | fundamental mode / `KdOp` / spectral radius in \(H_d\) |
| **Niven** | `saturacion_iff` + `no_reposición_saturacion_camino` + `deltaGeom_pos_of_four_le` |
| **Szegő** | `limite_szego_CNava` + `deltaInf_pos` + ∞ is not a dimension |
| **Monotonicity** | `deltaGeom_four_le`: `δ_geom(4)` is the global floor for all `d ≥ 4` |

Reading: the simultaneously rational trigonometric products of path
saturation **only** exist at \(d\in\{2,3\}\). There are no more seeds;
that is why **nothing restores the unit bound** after \(d=4\).
Moreover, certified monotonicity pins \(d=4\) as the smallest realized
defect: any measurement in a physical \(H_d\) with \(d\ge4\) is
separated from zero by at least \(\delta_{\rm geom}(4)\). As the finite
family grows, the defect does not vanish: it converges to
\(\delta_\infty>0\).

**Habitat closure:** \(H_d = \mathbb{C}^d \cong \mathbb{R}^{2d}\), finite.
Period. For continuous infinite, this is not a hotel — \(d=\infty\) is not
hosted in this package; at most one sees it arriving through the window as
a limit (`D8_Szego.lean`), but it never crosses the door.
-/

@[expose] public section

noncomputable section

open Real
open Filter
open scoped Topology

namespace BlindajeHd

open TransportePosicion
open Gnomon

/-! ## Habitat: stays within \(H_d\) -/

/-- Predicate recording that the entire construction remains in the finite Hilbert space `Hd d`. -/
def HabitatHilbertFinito (d : ℕ) : Prop :=
  Hd d = EuclideanSpace ℂ (Fin d)

theorem habitatHilbertFinito (d : ℕ) : HabitatHilbertFinito d :=
  Hd_eq_euclidean d

theorem infinito_no_es_habitat :
    Tendsto deltaGeom atTop (𝓝 deltaInf) ∧
      deltaInf = Cinf - 1 ∧
      0 < deltaInf :=
  infinito_no_es_dimension_sino_limite

/-! ## Niven: the unit bound does not recover -/

theorem niven_saturacion_solo_semillas (d : ℕ) (hd : 2 ≤ d) :
    cos (π / (d + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3 :=
  saturacion_iff d hd

/-- **Nothing restores the bound** after \(d=4\). -/
theorem niven_cota_unitaria_no_se_repone (d : ℕ) (hd : 4 ≤ d) :
    cos (π / (d + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4 :=
  no_reposición_saturacion_camino d hd

theorem niven_deltaGeom_pos_en_Hd (d : ℕ) (hd : 4 ≤ d) :
    0 < deltaGeom d :=
  deltaGeom_pos_of_four_le d hd

theorem piso_precision_deltaGeom_d4_en_Hd (d : ℕ) (hd : 4 ≤ d) :
    deltaGeom 4 ≤ deltaGeom d :=
  deltaGeom_four_le d hd

/-- In the finite physical regime `H_d`, `d ≥ 4`, no reading has defect
below the elementary floor `δ_geom(4)`. -/
theorem no_medicion_absoluta_bajo_piso_d4_en_Hd
    (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : ε < deltaGeom 4) :
    ε < deltaGeom d :=
  lt_of_lt_of_le hε (piso_precision_deltaGeom_d4_en_Hd d hd)

/-! ## Fiedler: spectrum and band in \(H_d\) -/

theorem fiedler_autovector_en_Hd (d : ℕ) (hd : 2 ≤ d) :
    KdOp d (vectorFiedlerExplicito d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • vectorFiedlerExplicito d :=
  KdOp_vectorFiedlerExplicito d hd

theorem fiedler_radio_banda (d : ℕ) (hd : 2 ≤ d) :
    letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    letI : Nontrivial (Hd d) := inferInstance
    ConstructorEspectralTP.radioEspectral (KdOp d) (KdOp_simetrico d) =
      2 / ((d : ℝ) - 1) := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  letI : Nontrivial (Hd d) := inferInstance
  exact radioEspectral_KdOp_eq_paso d hd

/-! ## Szegő: asymptotics of the finite family -/

theorem szego_limite_familia_finita :
    Tendsto CNava atTop (𝓝 Cinf) :=
  limite_szego_CNava

theorem szego_deltaInf_pos : 0 < deltaInf :=
  deltaInf_pos

theorem defecto_real_positivo_desde_Hd4_hasta_limite :
    (∀ d : ℕ, 4 ≤ d → 0 < deltaGeom d) ∧
      Tendsto deltaGeom atTop (𝓝 deltaInf) ∧
      0 < deltaInf :=
  ⟨niven_deltaGeom_pos_en_Hd, limite_defecto_geometrico, szego_deltaInf_pos⟩

/-! ## Joint citable certificate -/

/-- Joint certificate collecting the finite habitat, saturation classification, and positive gap. -/
structure CertificadoBlindajeHd where
  habitat : ∀ d : ℕ, HabitatHilbertFinito d
  niven_iff :
    ∀ d : ℕ, 2 ≤ d →
      (cos (π / ((d : ℝ) + 1)) ^ 2 = ((d : ℝ) - 1) / 4 ↔ d = 2 ∨ d = 3)
  niven_no_reposición :
    ∀ d : ℕ, 4 ≤ d →
      cos (π / ((d : ℝ) + 1)) ^ 2 ≠ ((d : ℝ) - 1) / 4
  deltaGeom_pos : ∀ d : ℕ, 4 ≤ d → 0 < deltaGeom d
  deltaGeom_piso_d4 : ∀ d : ℕ, 4 ≤ d → deltaGeom 4 ≤ deltaGeom d
  fiedler_autovector :
    ∀ d : ℕ, 2 ≤ d →
      KdOp d (vectorFiedlerExplicito d) =
        ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • vectorFiedlerExplicito d
  szego_limite : Tendsto CNava atTop (𝓝 Cinf)
  szego_deltaInf : 0 < deltaInf
  defecto_real_positivo :
    (∀ d : ℕ, 4 ≤ d → 0 < deltaGeom d) ∧
      Tendsto deltaGeom atTop (𝓝 deltaInf) ∧
      0 < deltaInf
  infinito_limite :
    Tendsto deltaGeom atTop (𝓝 deltaInf) ∧
      deltaInf = Cinf - 1 ∧ 0 < deltaInf

theorem certificadoBlindajeHd_OK : Nonempty CertificadoBlindajeHd :=
  ⟨{ habitat := habitatHilbertFinito
     niven_iff := fun d hd => niven_saturacion_solo_semillas d hd
     niven_no_reposición := fun d hd => niven_cota_unitaria_no_se_repone d hd
     deltaGeom_pos := fun d hd => niven_deltaGeom_pos_en_Hd d hd
     deltaGeom_piso_d4 := fun d hd => piso_precision_deltaGeom_d4_en_Hd d hd
     fiedler_autovector := fun d hd => fiedler_autovector_en_Hd d hd
     szego_limite := szego_limite_familia_finita
     szego_deltaInf := szego_deltaInf_pos
     defecto_real_positivo := defecto_real_positivo_desde_Hd4_hasta_limite
     infinito_limite := infinito_no_es_habitat }⟩

end BlindajeHd
