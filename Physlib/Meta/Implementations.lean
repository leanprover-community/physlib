/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Lean.Elab.Command
/-!

## Other Implementations

This provides a way to reference other implementations.

-/
@[expose] public section

open Lean

/-- The structure containing the information of an implementation
  of a result from physics into an ITP elsewhere. -/
structure Implementation where
  /-- The reference for the implementation. -/
  ref : String
  /-- The description of the implementation. -/
  description : String

/-- Environment extension to store `other_implementation ...`. -/
meta initialize implementationExtension :
    SimplePersistentEnvExtension Implementation (Array Implementation) ←
  registerSimplePersistentEnvExtension {
    name := `implementationExtension
    addEntryFn := fun arr impl => arr.push impl
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Syntax for the `other_implementation ...` command. -/
syntax (name := other_implementation_comment) "other_implementation " str str : command

/-- Elaborator for the `other_implementation ...` command -/
@[command_elab other_implementation_comment]
meta def elabImplementation : Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(other_implementation $s1 $s2) => do
    let ref : String := s1.getString
    let description : String := s2.getString
    let impl : Implementation := { ref := ref, description := description}
    modifyEnv fun env => implementationExtension.addEntry env impl
    Elab.Command.liftTermElabM <| Lean.Elab.Term.addTermInfo' stx
        (Lean.mkStrLit s!"An implementation of results elsewhere.") (expectedType? := none)
  | _ => throwError "Invalid syntax for `other_implementation` command"
