/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Init.System.IO
import Std.Time.Zoned
/-!

# Making tags

This file returns tags which can be used for TODO items, informal lemmas,
informal definitions and semiformal results.

Run it with `lake exe make_tag`.

## Attributes

The `digit` part of this file is modified from the module

`Mathlib.Data.Nat.Digits`

released under the Apache 2.0 license, Copyright (c) 2020 Kim Morrison,
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro

-/
open Std.Time
/-!

# digit

-/

/- The RFC 4648 Base32 -/
def digitChar (n : Nat) : Char :=
  if n = 0 then 'A' else
  if n = 1 then 'B' else
  if n = 2 then 'C' else
  if n = 3 then 'D' else
  if n = 4 then 'E' else
  if n = 5 then 'F' else
  if n = 6 then 'G' else
  if n = 7 then 'H' else
  if n = 8 then 'I' else
  if n = 9 then 'J' else
  if n = 10 then 'K' else
  if n = 11 then 'L' else
  if n = 12 then 'M' else
  if n = 13 then 'N' else
  if n = 14 then 'O' else
  if n = 15 then 'P' else
  if n = 16 then 'Q' else
  if n = 17 then 'R' else
  if n = 18 then 'S' else
  if n = 19 then 'T' else
  if n = 20 then 'U' else
  if n = 21 then 'V' else
  if n = 22 then 'W' else
  if n = 23 then 'X' else
  if n = 24 then 'Y' else
  if n = 25 then 'Z' else
  if n = 26 then '2' else
  if n = 27 then '3' else
  if n = 28 then '4' else
  if n = 29 then '5' else
  if n = 30 then '6' else
  if n = 31 then '7' else
  '*'

def toDigitsCore (base : Nat) : Nat → Nat → List Char → List Char
  | 0,      _, ds => ds
  | fuel+1, n, ds =>
    let d  := digitChar <| n % base;
    let n' := n / base;
    if n' = 0 then d::ds
    else toDigitsCore base fuel n' (d::ds)

def toDigits (base : Nat) (n : Nat) : List Char :=
  toDigitsCore base (n+1) n []

/-!

## Main function

-/
unsafe def main (_ : List String) : IO Unit := do
  let timeNow ← Timestamp.now
  let timeString := toString timeNow
  let timeNat := match timeString.toNat? with
    | some n => n
    | none => panic! "Failed to convert timeString to Nat"
  let digits := toDigits 32 timeNat
  let tag := String.ofList (digits.drop 2)
  println! tag
  pure ()
