/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Data.Fin.Basic
public import Physlib.Meta.Linters.Sorry

@[expose] public section

--Classical capacity
-- * Define "code"
-- * Define (Shannon) capacity of a (iid, memoryless) channel
-- * Prove Shannon's capacity theorems

variable (A I O : Type*)

/-- Here we define a *Code* by an encdoder and a decoder. The encoder is a function that takes
 strings (`List`s) of any length over an alphabet `A`, and returns strings over `I`;
 the decoder takes `O` and gives back strings over `A`. The idea is that a channel
 would map from strings of `I` to `O`. Important special cases are where `I=O` (the channel doesn't
 change the symbol set), and `FixedLengthCode` where the output lengths only depend on input
 lengths. -/
structure Code where
  encoder : List A → List I
  decoder : List O → List A

/-- A `FixedLengthCode` is a `Code` whose output lengths don't depend on the input content, only
 the input length. -/
structure FixedLengthCode extends Code A I O where
  enc_length : ℕ → ℕ
  enc_maps_length : ∀ as, (encoder as).length = enc_length (as.length)
  dec_length : ℕ → ℕ
  dec_maps_length : ∀ is, (decoder is).length = dec_length (is.length)

/-- A `BlockCode` is a `FixedLengthCode` that (1) maps symbols in discrete blocks of fixed length,
 (2) the encoded alphabet `I` has a canonical injection into `O`, and (3) has encoder and decoders
 that are inverses of each other. This is well-suited to describing noise and erasure channels. If
 the channel merely "corrupts" the data then this `O = I`; the erasure channel might for instance
 take `O = I ⊕ Unit` or `Option I`.

 We define the behavior of a block code to "fail" if the input is not a multiple of the block size,
 by having it return an empty list.

 The string encoder, the decoder and the two length lemmas are left as `sorry` in the
 field defaults. -/
@[sorryful]
structure BlockCode (io : I → O) extends FixedLengthCode A I O where
  block_in : ℕ
  block_out : ℕ
  block_enc : (Fin block_in → A) → (Fin block_out → I)
  block_dec : (Fin block_out → O) → (Fin block_in → A)
  block_enc_dec_inv : ∀ as, block_dec (io ∘ (block_enc as)) = as
  enc_length na := if na % block_in != 0 then 0 else (na / block_in) * block_out
  dec_length no := if no % block_out != 0 then 0 else (no / block_out) * block_in
  encoder as := if as.length % block_in != 0 then [] else
    sorry
  decoder os := if os.length % block_out != 0 then [] else
    sorry
  enc_maps_length := sorry
  dec_maps_length := sorry
