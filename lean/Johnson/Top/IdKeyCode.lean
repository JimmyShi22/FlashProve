-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/IdKeyCode.lean: a code of a part of a verifier's key: the commitment ID's string without
the record's seed.

The front makes a scheme's commitment from its verifier's key: the hash function's answer at a code
of the key (`ZKCP.Arg.digestKey`, ZKCP/DigestKey.lean). Its theorems ask of the code that no bit
string is the code of two keys (`ZKCP.CodeIsOneToOne`). The byte format's commitment ID is the hash,
under the call number 179, of a string that holds the configuration's digest, the first table's name
(its root, the digest again, the six words of the tables' shape), the seed of the table's record,
the record's answers and a closing list, empty by the format's page (R4.11). `OnBytes.Tie.idCode` is
the string of such a call WITHOUT THE SEED and without that list, as a bit string, and it is one to
one (`OnBytes.Tie.idCode_oneToOne`). Here it is carried to the types of the compiled verifier with a
record (Johnson/RecCompile/Cms.lean). The string with the seed in it, as the code of a key (root,
record): OnBytes/Tie/IdKeySeed.lean, Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean; that it is
`Fmt.publishedBytes` (Fmt/Rules4.lean) at the key's parts: `idBytesS_fmt`,
OnBytes/Tie/IdKeySeedFmt.lean.

1. What the file contains.
   `KeyId L`: a root and the answers of its record: what the string without the seed holds, beside
   what is public. `IdSpell L`: the tables' shape, the configuration's digest, and how answers are
   spelled.
   `idCodeOf S`: the code of a `KeyId L`.
2. What is checked when the file compiles. The proofs.
3. Theorems. `digToBytes_injective`. `idCodeOf_oneToOne`: no bit string is the code of two keys, if
   the spelling of the answers is one to one.
4. What is not claimed.
   THIS CODE IS NOT THE STRING OF THE FORMAT's RULE FOR THE ID (R4.11; `Fmt.publishedBytes`,
   Fmt/Rules4.lean): it leaves the seed and the closing list out. No theorem here speaks of the
   format's commitment ID. The key of the compiled verifier (`FullKey`) holds more than a `KeyId`: the
   seed of the record, the argument string of the test, the further roots with their records and
   links. This code holds none of these; the string of the format's rule holds, of these, the seed
   alone. The seed: by R4.8 the seeds of a table's record are sampled from a chain over the table's
   name alone, and no file holds them, and no string of a call but that of the call 179; in `FullKey` a
   record is a seed with answers, and the verifier tests the seed against the oracle at every call.
   So over `FullKey`, and over a root with a whole record, this code is not one to one.
   A key has a code only within `OnBytes.Tie.idOk`. That honest keys have codes is not shown here.
   How answers are spelled is a letter; no description's answers are spelled here.

Terms: lean/GLOSSARY.md.


-/
import Johnson.RecCompile.Front
import OnBytes.Tie.IdKey
import Run.CodingPage160

set_option autoImplicit false

namespace VerifiableInference.Rec
open Iop

/-- The spelling of a digest as 32 bytes is one to one. -/
theorem digToBytes_injective : Function.Injective Run.digToBytes := fun a b h =>
  List.ofFn_injective (by rw [← Run.bits_digToBytes a, ← Run.bits_digToBytes b, h])

variable {I X : Type}

/-- What the commitment ID's string without the record's seed holds of a verifier's key: the first
root and the answers of its record. -/
structure KeyId (L : HolographicProtocol I X) where
  /-- the root of the hash tree over the first encoding of the index -/
  cm  : Dig 256
  /-- the answers of its record -/
  ans : L.OutOfDomainAnswer

/-- What is public in a commitment ID, and how the answers of a record are spelled. -/
structure IdSpell (L : HolographicProtocol I X) where
  /-- the tables' shape: the six words of a table's name -/
  shape   : OnBytes.Params.IndexShape
  /-- the configuration's digest -/
  cfg     : ByteArray
  /-- the answers of a record, as the list of elements that a key file holds -/
  answers : L.OutOfDomainAnswer → List OnBytes.E

variable {L : HolographicProtocol I X}

/-- The key as OnBytes/Tie/IdKey.lean has it: the shape, the digest, the root with the answers. -/
def IdSpell.key (S : IdSpell L) (k : KeyId L) : OnBytes.Tie.IdKey :=
  (S.shape, S.cfg, ⟨Run.digToBytes k.cm, S.answers k.ans⟩)

/-- The code of a key: the string of a call 179 without the record's seed, as bits; none outside
`OnBytes.Tie.idOk`. -/
def idCodeOf (S : IdSpell L) (k : KeyId L) : Option ZKCP.Str := OnBytes.Tie.idCode (S.key k)

/-- No bit string is the code of two keys. -/
theorem idCodeOf_oneToOne (S : IdSpell L) (h : Function.Injective S.answers) :
    ZKCP.CodeIsOneToOne (idCodeOf S) := by
  intro k k' code e e'
  have q := OnBytes.Tie.idCode_oneToOne _ _ code e e'
  have q2 : (⟨Run.digToBytes k.cm, S.answers k.ans⟩ : OnBytes.Params.TableName) =
      ⟨Run.digToBytes k'.cm, S.answers k'.ans⟩ := congrArg (fun x => x.2.2) q
  obtain ⟨c, a⟩ := k
  obtain ⟨c', a'⟩ := k'
  have r := OnBytes.Params.TableName.mk.inj q2
  have e1 : c = c' := digToBytes_injective r.1
  have e2 : a = a' := h r.2
  subst e1 e2
  rfl

end VerifiableInference.Rec

#print axioms VerifiableInference.Rec.idCodeOf_oneToOne
