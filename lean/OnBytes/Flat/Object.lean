-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/Object.lean: from three protocols, one for each file of the prover, to the object with
records that the compiler takes (`Iop.HolographicProtocol`, Hiop/RecInterface.lean).

Definitions and one lemma. No protocol occurs here. `F.withProvers P` lays the three protocols of `F :
Files C` (OnBytes/Flat/Frame.lean) as they are: the key file's as `offline`, the entry file's as
`link`, the proof file's with its annotation as `onlineBatch`. The encoder, the record and the decoder are
those of the configuration C. Nothing stands between the three and the compiler: no preamble, no
sampler, no added proof of work. SO THE THREE MUST THEMSELVES BE WRITTEN AS THE COMPILER NEEDS THEM:
a round's verifier message is blocks of digests (the compiler's law on wires asks that uniform hash
answers give an exactly uniform message: the number of a round's messages must be a power of two),
what the decision reads is made from the blocks inside the decision, and a round's proof of work
stands in the round. OnBytes/Flat/FilesAt.lean lays them so.

Main names:
  `F.Provers`: honest provers of the three protocols. No statement on soundness asks anything of
    them.
  `F.withProvers P : HolographicProtocol C.I C.X`.
  `obj_noneColl`: the decoder gives no index where the word has a collision at the record's seed (by
    the definition of `ConfigurationWithOutOfDomainSample.D`).

Limits: nothing on the soundness of the three protocols. `F.annT` and `F.annL` are not read here:
the library's object has an annotation for the proof file alone.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.Frame
import Hiop.RecInterface

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Hiop

namespace Files
variable {C : ConfigurationWithOutOfDomainSample} (F : Files C)

/-- The proof file's protocol with its annotation. -/
def batch : BatchInteractiveOracleProof (C.X × C.Rec) C.E0 := ⟨F.proof, F.ann⟩

/-- Honest provers of the three protocols. -/
structure Provers where
  hT : Honest F.key (C.I × (C.Pad × C.Rnd) × C.Seed)
  hL : Honest F.entry (C.I × ((C.Pad × C.Rnd) × C.Seed) × ((C.Pad × C.Rnd) × C.Seed))
  hB : BatchHonestProver F.batch (C.I × (C.Pad × C.Rnd) × C.Seed)

/-- The object with records. -/
noncomputable def withProvers (P : F.Provers) : HolographicProtocol C.I C.X where
  wordLength := C.n
  Symbol := C.Sg
  EncodingRandomness := C.Pad × C.Rnd
  encodeIndex := fun i r => C.enc (C.hold i r.1) r.2
  OutOfDomainSeed := C.Seed
  OutOfDomainAnswer := C.Ans
  honestOutOfDomainAnswer := fun i r s => C.smp s (C.hold i r.1)
  hasCollisionAt := C.coll
  decodeIndex := C.D
  offline := F.key
  link := F.entry
  maxBatchSize := F.N
  onlineBatch := F.batch
  honestOfflineProver := P.hT
  honestLinkProver := P.hL
  honestOnlineBatchProver := P.hB
  early := F.early
  late := F.late

theorem obj_noneColl (P : F.Provers) (y : Fin C.n → C.Sg) (rec : C.Rec) (h : C.coll y rec.1) :
    (F.withProvers P).decodeIndex y rec = none := by
  show C.D y rec = none
  unfold ConfigurationWithOutOfDomainSample.D
  rw [if_pos h]

end Files
end OnBytes.Flat

#print axioms OnBytes.Flat.Files.obj_noneColl
