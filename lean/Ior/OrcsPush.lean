-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/OrcsPush.lean: the oracles of a shape whose verifier messages are drawn through samplers
(Iop/Pull.lean) are those of the shape itself.

A sampler (`Sampler`, Iop/Pull.lean) makes a verifier message as the value of a map at a uniform
element of another set.
One definition, used for the compiled argument's named extractor (`extractorK`, CompileK/Main.lean)
and in Ior/Sub.lean (the verifier draws from a subset). `Orcs.push` only re-types the family of
symbols: positions and alphabets of a pulled round are those of the round.
Terms: lean/GLOSSARY.md.
-/
import Iop.Pull
import Ior.Batch

set_option autoImplicit false

namespace Iop

/-- The oracles do not change when verifier messages are made from other values. -/
def Orcs.push : {s : Shape} → (σ : Samplers s) → Orcs (s.pull σ) → Orcs s
  | [], _, _ => fun p => nomatch p
  | _ :: _, (_, σs), o => fun p => match p with
    | .inl p => o (.inl p)
    | .inr p => Orcs.push σs (fun q => o (.inr q)) p

end Iop
