-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GBitsLe.lean: two conditions on a list of numbers of proof-of-work bits (`GBits`,
Iop/GBits.lean): `GBits.AllLe n g` (every round has at most n) and `GBits.LateFree g n` (round n has
none). (Words of this library: lean/GLOSSARY.md.) Definitions only, in a separate file so that files
on the protocols and on the codes can use them without the wire records.
Where they are asked as hypotheses.
`AllLe`: in Iop/GrindWire.lean, as `g.AllLe n` with n ≤ λ: the wire record with proof-of-work bits
  reads the bits of a round from one hash block of λ bits.
`LateFree`: no other declaration of this library names it. A record of protocols `BatchProtocol` may name a
  round `late`, into whose query the compiler puts the whole request (Iop/Batch.lean, (D11)). The
  soundness theorems do not ask whether that round has proof-of-work bits, but for what
  `soundKG_recut` (CompileK/GrindKRecut.lean) and `soundKGT_recut` (CompileK/KnowWidePass.lean) ask
  of every round (`GBits.UnitFree`, Ior/GrindKLists.lean): a round whose verifier message has one
  value has none. The implementation's call at that place holds no nonce; so a model that is to
  follow it has `LateFree` at its round `late`.
Notation: `n : ℕ`: a number of bits in `GBits.AllLe n g`; the number of a round, counted from 0
(`GBits.get`), in `GBits.LateFree g n`; λ (in Lean `lam : ℕ`): a hash block is `Dig lam`
(Iop/Wire.lean): lam bits; `late : Option ℕ`: a field of `BatchProtocol` (Iop/Batch.lean): the round of Batch
(counted from 0) into whose query layer 1 writes the whole instance; none: there is no such round;
layer 1 (lean/GLOSSARY.md, layer): the numbered layers are the parts of the construction: the lowest
is the compiler.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Iop.GBits

namespace Iop

/-- Every round has at most n proof-of-work bits. -/
def GBits.AllLe (n : ℕ) : {s : Shape} → GBits s → Prop
  | [], _ => True
  | _ :: _, (b, g) => b ≤ n ∧ GBits.AllLe n g

/-- The number of proof-of-work bits of round i, counted from 0; 0 beyond the last round. -/
def GBits.get : {s : Shape} → GBits s → ℕ → ℕ
  | [], _, _ => 0
  | _ :: _, (b, _), 0 => b
  | _ :: _, (_, g), i + 1 => GBits.get g i

/-- Round n has no proof-of-work bits. -/
def GBits.LateFree {s : Shape} (g : GBits s) (n : ℕ) : Prop := g.get n = 0

end Iop
