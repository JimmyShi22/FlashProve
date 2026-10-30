-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Enc.lean: an encoding with randomness and a decoding, for oracles of a kind.

Definitions only.

Main name: `Enc E`: a type of messages, a type of randomness, an encoding `enc` into a string of the
kind E, and a decoding `dec`.

Terms: lean/GLOSSARY.md.
-/
import Ior.Batch
import Ior.ToProto

set_option autoImplicit false

namespace Hiop
open Iop Prob

/-- An encoding with randomness and a decoding, for oracles of the kind E. -/
structure Enc (E : ExtSpec) where
  Msg : Type
  Rnd : Type
  [finRnd : Fintype Rnd]
  [neRnd  : Nonempty Rnd]
  enc : Msg → Rnd → E.Str
  dec : E.Str → Option (Msg × Rnd)

attribute [instance] Enc.finRnd Enc.neRnd

end Hiop
