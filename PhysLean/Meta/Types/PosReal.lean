import Mathlib.Data.Real.Basic

/-- The type of strictly positive real numbers. -/
abbrev PosReal := { x : ℝ // 0 < x }

notation "ℝ>0" => PosReal

/-- The type of extended strictly positive real numbers (ℝ>0 ∪ {∞}). -/
abbrev EPosReal := WithTop PosReal

notation "ℝ>0∞" => EPosReal
