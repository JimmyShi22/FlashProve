-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecSide.lean: the verifier's side of an object with records, as a record of its own.

An object with records (`HolographicProtocol`, Hiop/RecInterface.lean) holds in one record three protocols, with the
types over which they are typed, and, among others, an encoder, a decoder and three honest provers.
Lean's compiler produces no executable code for a definition that passes a constant without
executable code as an argument: not even if the argument is implicit, or if it is a record of which
few fields are read. (What stands in types and proofs alone is erased and does not count.) A decoder
need not have code: `ConfigurationWithOutOfDomainSample.D` (Hiop/RecConf.lean), which `Files.withProvers` (OnBytes/Flat/Object.lean)
lays in as `decodeIndex`, decides a proposition by classical logic. So ten of the fields are repeated
here in a record of their own, called the verifier's side. Definitions only.

Main names.
  `LHV X`: ten fields, with the names and types that they have in `HolographicProtocol`: the word length `n` and the
    symbols `Sg` of an encoded index; the types `Seed` and `Ans` of the two parts of a record; the
    protocols `test`, `link` and `bat`; the number of slots `N`; `early`: the part of an instance
    that is written into a chain's first query; `late`: the round, if there is one, at which the
    whole instance is written (so the fields of these names of `BatchProtocol`, Iop/Batch.lean). It has no
    type-class instance: those of `HolographicProtocol` on `OutOfDomainSeed` are not among the ten.
  `LHV.Rec`, `LHV.XC`: a record; what a chain's first query holds of an instance.
  `HolographicProtocol.v L`: the ten fields of the object L, as an `LHV`.

Limits. The types of the ten fields are written twice, here and in `HolographicProtocol`, so a later change of a
field's type must be made in both places. `HolographicProtocol.v`, written field by field, type-checks only while
the two texts agree: it is what keeps them one, so it must stay even where nothing calls it. It
still type-checks if `HolographicProtocol` gains a field: this record then lacks it. That the three protocols'
verifiers read no other field of `HolographicProtocol` is not stated. Whether a value of `LHV` has executable code
depends on its ten fields.
Terms: lean/GLOSSARY.md.

-/
import Hiop.RecInterface

set_option autoImplicit false

namespace Iop

/-- The verifier's side of an object with records: ten of the fields of `HolographicProtocol`. -/
structure LHV (X : Type) where
  n    : ℕ
  Sg   : Type
  /-- the record phase: the verifier's seed -/
  Seed : Type
  /-- the prover's answer -/
  Ans  : Type
  test : InteractiveOracleProof (Seed × Ans) (oneExternalString n Sg)
  link : InteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings n Sg)
  /-- the number of slots -/
  N    : ℕ
  bat  : BatchInteractiveOracleProof (X × (Seed × Ans)) (oneExternalString n Sg)
  early : X → X
  late  : Option ℕ

variable {I X : Type}

namespace LHV

/-- A record: the seed and the answer. -/
abbrev Rec (L : LHV X) : Type := L.Seed × L.Ans

/-- What the first query of a chain holds of an instance: Test: (none, rec, rec); Link: (none, first
record, further record); a session: (x, rec, rec). -/
abbrev XC (L : LHV X) : Type := Option X × L.Rec × L.Rec

end LHV

/-- The verifier's side of an object. -/
@[reducible] def HolographicProtocol.v (L : HolographicProtocol I X) : LHV X where
  n := L.wordLength
  Sg := L.Symbol
  Seed := L.OutOfDomainSeed
  Ans := L.OutOfDomainAnswer
  test := L.offline
  link := L.link
  N := L.maxBatchSize
  bat := L.onlineBatch
  early := L.early
  late := L.late

end Iop
