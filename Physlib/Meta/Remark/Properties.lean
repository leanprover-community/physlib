/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Remark.Basic
/-!

## Underlying structure for remarks
-/

@[expose] public section

namespace Physlib
open Lean
variable {m} [Monad m] [MonadEnv m] [MonadError m]

/-- All remarks in the environment. -/
meta def allRemarkInfo : m (Array RemarkInfo) := do
  let env ← getEnv
  return remarkExtension.getState env

/-- The full name of a remark (name and namespace). -/
meta def RemarkInfo.toFullName (r : RemarkInfo) : Name :=
  if r.nameSpace != .anonymous then
    .str r.nameSpace r.name.toString
  else
    r.name

/-- A Bool which is true if a name corresponds to a remark. -/
meta def RemarkInfo.IsRemark (n : Name) : m Bool := do
  let allRemarks ← allRemarkInfo
  let r := allRemarks.find? fun r => r.toFullName == n
  return r.isSome

/-- Gets the remarkInfo from a name corresponding to a remark.. -/
meta def RemarkInfo.getRemarkInfo (n : Name) : m RemarkInfo := do
  let allRemarks ← allRemarkInfo
  match allRemarks.find? fun r => r.toFullName == n with
  | some r => return r
  | none => throwError s!"No remark named {n}"

end Physlib
