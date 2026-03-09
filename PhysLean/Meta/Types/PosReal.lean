/-
Copyright (c) 2026 Trong-Nghia Be. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be
-/
import Mathlib.Data.Real.Basic

/-- The type of strictly positive real numbers. -/
abbrev PosReal := { x : ℝ // 0 < x }

notation "ℝ>0" => PosReal

/-- The type of extended strictly positive real numbers (ℝ>0 ∪ {∞}). -/
abbrev EPosReal := WithTop PosReal

notation "ℝ>0∞" => EPosReal
