/-
Copyright (c) 2026 Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathSpectralGap.D3_GrafoCamino

@[expose] public section

/-!
# D4 — Por qué no un paso diagonal

`D3_GrafoCamino.lean` fija el soporte de `T_d` en los pasos mínimos
(vecino a vecino) del camino `pathGraph d`. Este archivo cierra, con dos
argumentos independientes, la pregunta de por qué nunca se considera un
paso "diagonal" (cambiar más de una coordenada a la vez) como alternativa:

1. **Si hubiera ≥ 2 ejes genuinos** (el modelo se generalizara a una malla
   cúbica `Fin dx × Fin dy × Fin dz`), Pitágoras decide: el paso ortogonal
   (un solo eje) tiene distancia euclidiana exactamente `1`; el paso
   diagonal doble, exactamente `√2`; el triple, exactamente `√3`. Como
   `1 < √2` y `1 < √3`, el paso ortogonal es siempre estrictamente más
   corto. No es una preferencia de diseño: es la adyacencia mínima que
   Pitágoras obliga.
2. **En el caso efectivamente usado por `T_d/P_d`** (un solo eje, `dy = dz = 1`),
   la pregunta ni siquiera se plantea: con un único eje genuino la propia
   relación "paso diagonal" es la relación **vacía** — no existe ningún par
   de sitios que la satisfaga, porque un eje trivial (`Fin 1`) no tiene
   ningún paso mínimo posible. La diagonal presupone, para poder
   enunciarse de forma no vacía, dos ejes ya distinguidos entre sí.
-/

noncomputable section

namespace PathGraph3D

/-- Sitio de una malla cúbica: producto de tres mallas 1D. -/
abbrev Sitio3D (dx dy dz : ℕ) := Fin dx × Fin dy × Fin dz

/-- Adyacencia ortogonal del cubo: cambia una sola coordenada a la vez, por
un paso mínimo en ese eje. -/
def Adj3D {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : Prop :=
  (TransportePosicion.PasoMinimo p.1 q.1 ∧ p.2 = q.2) ∨
    (p.1 = q.1 ∧ TransportePosicion.PasoMinimo p.2.1 q.2.1 ∧ p.2.2 = q.2.2) ∨
    (p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ TransportePosicion.PasoMinimo p.2.2 q.2.2)

end PathGraph3D

/-! ## 1. Pitágoras: el paso ortogonal es siempre estrictamente más corto -/

namespace OrtogonalidadMinimalPitagoras

open PathGraph3D
open TransportePosicion

/-- Distancia euclidiana entre dos sitios del cubo, viendo cada coordenada
`Fin` como un real vía el casteo natural. -/
noncomputable def dist3D {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : ℝ :=
  Real.sqrt (
    ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 +
    ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
    ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2)

/-- Dos coordenadas a un `PasoMinimo` difieren, como reales, en exactamente
`±1`; su diferencia al cuadrado es `1`. -/
theorem pasoMinimo_sq_diff_eq_one {d : ℕ} {i j : Fin d} (h : PasoMinimo i j) :
    ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = 1 := by
  rcases h with h | h
  · have hij : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast h.symm
    rw [hij]; ring
  · have hji : (i.val : ℝ) = (j.val : ℝ) + 1 := by exact_mod_cast h.symm
    rw [hji]; ring

theorem eq_sq_diff_eq_zero {d : ℕ} {i j : Fin d} (h : i = j) :
    ((i.val : ℝ) - (j.val : ℝ)) ^ 2 = 0 := by
  rw [h]; ring

/-! ### Paso ortogonal: distancia exactamente `1` -/

theorem dist3D_eq_one_of_Adj3D
    {dx dy dz : ℕ} {p q : Sitio3D dx dy dz} (h : Adj3D p q) :
    dist3D p q = 1 := by
  unfold dist3D
  rcases h with ⟨hx, hyz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 :=
      eq_sq_diff_eq_zero (congrArg Prod.fst hyz)
    have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 :=
      eq_sq_diff_eq_zero (congrArg Prod.snd hyz)
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [pasoMinimo_sq_diff_eq_one hx, hy0, hz0]; ring
    rw [hsum, Real.sqrt_one]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hz
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [hx0, pasoMinimo_sq_diff_eq_one hy, hz0]; ring
    rw [hsum, Real.sqrt_one]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hy
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 1 := by
      rw [hx0, hy0, pasoMinimo_sq_diff_eq_one hz]; ring
    rw [hsum, Real.sqrt_one]

/-! ### Paso diagonal doble: distancia exactamente `√2` -/

/-- Vecino diagonal en dos ejes: dos coordenadas cambian por `PasoMinimo`
simultáneamente, la tercera queda fija. `Adj3D` nunca produce este caso. -/
def PasoDiagonalDoble {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : Prop :=
  (PasoMinimo p.1 q.1 ∧ PasoMinimo p.2.1 q.2.1 ∧ p.2.2 = q.2.2) ∨
  (PasoMinimo p.1 q.1 ∧ p.2.1 = q.2.1 ∧ PasoMinimo p.2.2 q.2.2) ∨
  (p.1 = q.1 ∧ PasoMinimo p.2.1 q.2.1 ∧ PasoMinimo p.2.2 q.2.2)

theorem dist3D_eq_sqrt_two_of_PasoDiagonalDoble
    {dx dy dz : ℕ} {p q : Sitio3D dx dy dz} (h : PasoDiagonalDoble p q) :
    dist3D p q = Real.sqrt 2 := by
  unfold dist3D
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · have hz0 : ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hz
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [pasoMinimo_sq_diff_eq_one hx, pasoMinimo_sq_diff_eq_one hy, hz0]; ring
    rw [hsum]
  · have hy0 : ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hy
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [pasoMinimo_sq_diff_eq_one hx, hy0, pasoMinimo_sq_diff_eq_one hz]; ring
    rw [hsum]
  · have hx0 : ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 = 0 := eq_sq_diff_eq_zero hx
    have hsum :
        ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
            ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 2 := by
      rw [hx0, pasoMinimo_sq_diff_eq_one hy, pasoMinimo_sq_diff_eq_one hz]; ring
    rw [hsum]

/-! ### Paso diagonal triple: distancia exactamente `√3` -/

/-- Vecino diagonal en los tres ejes (la esquina del cubo unitario). -/
def PasoDiagonalTriple {dx dy dz : ℕ} (p q : Sitio3D dx dy dz) : Prop :=
  PasoMinimo p.1 q.1 ∧ PasoMinimo p.2.1 q.2.1 ∧ PasoMinimo p.2.2 q.2.2

theorem dist3D_eq_sqrt_three_of_PasoDiagonalTriple
    {dx dy dz : ℕ} {p q : Sitio3D dx dy dz} (h : PasoDiagonalTriple p q) :
    dist3D p q = Real.sqrt 3 := by
  obtain ⟨hx, hy, hz⟩ := h
  unfold dist3D
  have hsum :
      ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2 + ((p.2.1 : ℝ) - (q.2.1 : ℝ)) ^ 2 +
          ((p.2.2 : ℝ) - (q.2.2 : ℝ)) ^ 2 = 3 := by
    rw [pasoMinimo_sq_diff_eq_one hx, pasoMinimo_sq_diff_eq_one hy,
      pasoMinimo_sq_diff_eq_one hz]; ring
  rw [hsum]

/-! ### Cierre Pitágoras: el ortogonal gana siempre -/

theorem uno_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ), h2]

theorem uno_lt_sqrt_three : (1 : ℝ) < Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (3 : ℝ), h3]

/-- El paso ortogonal (el único que admite `Adj3D`) es estrictamente más
corto que cualquier paso diagonal doble. -/
theorem ortogonal_mas_corto_que_diagonal_doble
    {dx dy dz : ℕ} {p q p' q' : Sitio3D dx dy dz}
    (hOrt : Adj3D p q) (hDiag : PasoDiagonalDoble p' q') :
    dist3D p q < dist3D p' q' := by
  rw [dist3D_eq_one_of_Adj3D hOrt, dist3D_eq_sqrt_two_of_PasoDiagonalDoble hDiag]
  exact uno_lt_sqrt_two

/-- El paso ortogonal es estrictamente más corto que cualquier paso
diagonal triple (la esquina del cubo). -/
theorem ortogonal_mas_corto_que_diagonal_triple
    {dx dy dz : ℕ} {p q p' q' : Sitio3D dx dy dz}
    (hOrt : Adj3D p q) (hDiag : PasoDiagonalTriple p' q') :
    dist3D p q < dist3D p' q' := by
  rw [dist3D_eq_one_of_Adj3D hOrt, dist3D_eq_sqrt_three_of_PasoDiagonalTriple hDiag]
  exact uno_lt_sqrt_three

/-- CIERRE. Ninguna diagonal (doble o triple) puede empatar o vencer en
distancia al paso ortogonal: la adyacencia mínima del cubo (`Adj3D`) es la
única compatible con minimalidad de distancia euclidiana. No es una
elección arbitraria: es la que Pitágoras obliga. -/
theorem adyacencia_minima_es_ortogonal
    {dx dy dz : ℕ} {p q p' q' : Sitio3D dx dy dz}
    (hOrt : Adj3D p q)
    (hDiag : PasoDiagonalDoble p' q' ∨ PasoDiagonalTriple p' q') :
    dist3D p q < dist3D p' q' := by
  rcases hDiag with hD | hD
  · exact ortogonal_mas_corto_que_diagonal_doble hOrt hD
  · exact ortogonal_mas_corto_que_diagonal_triple hOrt hD

end OrtogonalidadMinimalPitagoras

/-! ## 2. Con un solo eje, la diagonal es la relación vacía -/

namespace DiagonalPresuponeDosPd

open PathGraph3D
open OrtogonalidadMinimalPitagoras

/-- En un eje trivial (`Fin 1`, un único punto) no hay ningún paso mínimo:
`PasoMinimo` es la relación vacía. -/
theorem pasoMinimo_vacio_en_eje_trivial (i j : Fin 1) :
    ¬ TransportePosicion.PasoMinimo i j := by
  unfold TransportePosicion.PasoMinimo
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- Con un solo eje genuino (`dy = dz = 1`), `PasoDiagonalDoble` es la
relación vacía: no hay ningún par de sitios que la satisfaga. -/
theorem diagonalDoble_vacia_con_un_solo_eje
    {dx : ℕ} (p q : Sitio3D dx 1 1) : ¬ PasoDiagonalDoble p q := by
  unfold PasoDiagonalDoble
  rintro (⟨_, hy, _⟩ | ⟨_, _, hz⟩ | ⟨_, hy, _⟩)
  · exact pasoMinimo_vacio_en_eje_trivial p.2.1 q.2.1 hy
  · exact pasoMinimo_vacio_en_eje_trivial p.2.2 q.2.2 hz
  · exact pasoMinimo_vacio_en_eje_trivial p.2.1 q.2.1 hy

/-- Con un solo eje genuino, `PasoDiagonalTriple` (la esquina del cubo)
tampoco existe: también es la relación vacía. -/
theorem diagonalTriple_vacia_con_un_solo_eje
    {dx : ℕ} (p q : Sitio3D dx 1 1) : ¬ PasoDiagonalTriple p q := by
  unfold PasoDiagonalTriple
  rintro ⟨_, hy, _⟩
  exact pasoMinimo_vacio_en_eje_trivial p.2.1 q.2.1 hy

/-- CIERRE. Con un solo eje, ninguna diagonal —doble ni triple— existe. La
diagonal es, en sentido literal de teoría de conjuntos, posterior a la
existencia de dos ejes distinguidos entre sí: no anterior, no simultánea,
no elemental. El modelo `T_d/P_d` (un único eje) nunca necesita excluirla
por decreto: no hay nada que excluir. -/
theorem diagonal_no_existe_con_un_solo_eje
    {dx : ℕ} (p q : Sitio3D dx 1 1) :
    ¬ (PasoDiagonalDoble p q ∨ PasoDiagonalTriple p q) := by
  rintro (h | h)
  · exact diagonalDoble_vacia_con_un_solo_eje p q h
  · exact diagonalTriple_vacia_con_un_solo_eje p q h

end DiagonalPresuponeDosPd

end
