-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/RestSib.lean: A TWIN OF Johnson/Flat/RestSib.lean, WITH THE ENTRY FILE's THREE LETTERS FREE: ds (its rounds' data), xs (its openings of stored tables), dec (its decision),
in that order behind runP.

Why. The frame in the library lays the entry file's protocol as the written link at written rounds' data, written openings and THE DECISION OF
`verify-on-bytes` (`fun rr => decFullX (recX rr)` | `decSmallX`). A verifier whose entry file's decision is another text is then no
member of the frame, and neither the tie from what runs nor the conditional soundness theorem can speak of it.
How it was made. Every declared name of the original has a D behind it; `ds xs dec` stand behind `runP` in every list of letters;
`linkSibFull` | `linkSibSmall` became `linkFullD ds xs dec` | `linkSmallD ds xs dec`; `dsFull` | `dsSmall` became ds, `frD.xs` | `srD.xs`
xs. All else is the original's text, docstrings too: WHERE A DOCSTRING SAYS «written» OR NAMES A FILE IT SPEAKS OF THE TEXT OF WHICH
THIS IS A TWIN. Added: `linkFullD`, `linkSmallD`.
Limits: those of the original's head. That at the original's three letters the twins are the
original's terms is not proved in this library.
Nothing on soundness is gained: in the conditional theorem `entrySound` becomes a
named hypothesis, in the
place of the theorem on codes, from which the text in the library (Johnson/Flat/TwoSizesAt.lean) proves it for the written letters alone; and four tests on the numbers of ds
become premises, which the text in the library proves of the written data.

-/
import OnBytes.Flat.Object
import OnBytes.Flat.LinkSibAt
import OnBytes.Flat.EntryTerm
import Johnson.EntryRec.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat

open Hiop Cb Cb.Ood OnBytes.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.RunA (RestR LrG)

/-- The written link's make at the full size, its three letters free. -/
abbrev linkFullD (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
    (dec : RecFull × RecFull → _root_.Run.PQ.View → Bool) :
    InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX) :=
  linkProtocolOfRoundData (_root_.Run.ckP .two) ds frS.P.T.a xs dec

/-- The same at the small size. -/
abbrev linkSmallD (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
    (dec : RecSmall × RecSmall → _root_.Run.PQ.View → Bool) :
    InteractiveOracleProof (RecSmall × RecSmall) (twoExternalStrings (2 ^ srS.P.T.a) _root_.Run.PQ.SgX) :=
  linkProtocolOfRoundData (_root_.Run.ckP .two) ds srS.P.T.a xs dec

/-! ## The full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → _root_.Run.PQ.View → Bool)
  (hL : Honest (linkFullD ds xs dec) ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))

/-- What the object holds beside its word length, its symbols and its link, where the link is
`(linkFullD ds xs dec)`. -/
def restSibFullD : RestR (DecR.configurationOfStoredTable A R).I X ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a
    (linkFullD ds xs dec) where
  enc := (F.withProvers P).encodeIndex
  ans := (F.withProvers P).honestOutOfDomainAnswer
  coll := (DecR.configurationOfStoredTable A R).coll
  dcd := (DecR.configurationOfStoredTable A R).D
  test := (F.withProvers P).offline
  N := (F.withProvers P).maxBatchSize
  bat := (F.withProvers P).onlineBatch
  hT := (F.withProvers P).honestOfflineProver
  hL := hL
  hB := (F.withProvers P).honestOnlineBatchProver
  early := (F.withProvers P).early
  late := none

/-- Its decoder is the configuration's. -/
theorem restSibFull_dcdD : (restSibFullD A R F P ds xs dec hL).dcd = (DecR.configurationOfStoredTable A R).D := rfl

/-- Its collisions are the configuration's. -/
theorem restSibFull_collD : (restSibFullD A R F P ds xs dec hL).coll = (DecR.configurationOfStoredTable A R).coll := rfl

/-- No part of an instance comes late. -/
theorem restSibFull_lateD : (LrG (restSibFullD A R F P ds xs dec hL)).late = none := rfl

/-- The link of the object is `(linkFullD ds xs dec)`. -/
theorem restSibFull_linkD : (LrG (restSibFullD A R F P ds xs dec hL)).link = (linkFullD ds xs dec) := rfl

/-- All else is the three files' object's: the encoding, the answers, the collisions, the decoder,
the key file's protocol, the number of slots, the proof file's protocol, and what of an instance
comes early. -/
theorem restSibFull_restD :
    (LrG (restSibFullD A R F P ds xs dec hL)).encodeIndex = (F.withProvers P).encodeIndex ∧
      (LrG (restSibFullD A R F P ds xs dec hL)).honestOutOfDomainAnswer = (F.withProvers P).honestOutOfDomainAnswer ∧
      (LrG (restSibFullD A R F P ds xs dec hL)).hasCollisionAt = (F.withProvers P).hasCollisionAt ∧
      (LrG (restSibFullD A R F P ds xs dec hL)).decodeIndex = (F.withProvers P).decodeIndex ∧
      (LrG (restSibFullD A R F P ds xs dec hL)).offline = (F.withProvers P).offline ∧
      (LrG (restSibFullD A R F P ds xs dec hL)).maxBatchSize = (F.withProvers P).maxBatchSize ∧
      (LrG (restSibFullD A R F P ds xs dec hL)).onlineBatch = (F.withProvers P).onlineBatch ∧
      (LrG (restSibFullD A R F P ds xs dec hL)).early = (F.withProvers P).early :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

/-! ## The small size -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (R : (srS.toDecR srZ 524285).RelationsAndEncoding A)
  (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecSmall × RecSmall → _root_.Run.PQ.View → Bool)
  (hL : Honest (linkSmallD ds xs dec) ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))

/-- What the object holds beside its word length, its symbols and its link, where the link is
`(linkSmallD ds xs dec)`. -/
def restSibSmallD : RestR (DecR.configurationOfStoredTable A R).I X ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (Fin 1 → (Fin 19 → GE) × NZ) ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a
    (linkSmallD ds xs dec) where
  enc := (F.withProvers P).encodeIndex
  ans := (F.withProvers P).honestOutOfDomainAnswer
  coll := (DecR.configurationOfStoredTable A R).coll
  dcd := (DecR.configurationOfStoredTable A R).D
  test := (F.withProvers P).offline
  N := (F.withProvers P).maxBatchSize
  bat := (F.withProvers P).onlineBatch
  hT := (F.withProvers P).honestOfflineProver
  hL := hL
  hB := (F.withProvers P).honestOnlineBatchProver
  early := (F.withProvers P).early
  late := none

/-- Its decoder is the configuration's. -/
theorem restSibSmall_dcdD : (restSibSmallD A R F P ds xs dec hL).dcd = (DecR.configurationOfStoredTable A R).D := rfl

/-- Its collisions are the configuration's. -/
theorem restSibSmall_collD : (restSibSmallD A R F P ds xs dec hL).coll = (DecR.configurationOfStoredTable A R).coll := rfl

/-- No part of an instance comes late. -/
theorem restSibSmall_lateD : (LrG (restSibSmallD A R F P ds xs dec hL)).late = none := rfl

/-- The link of the object is `(linkSmallD ds xs dec)`. -/
theorem restSibSmall_linkD : (LrG (restSibSmallD A R F P ds xs dec hL)).link = (linkSmallD ds xs dec) := rfl

/-- All else is the three files' object's: the encoding, the answers, the collisions, the decoder,
the key file's protocol, the number of slots, the proof file's protocol, and what of an instance
comes early. -/
theorem restSibSmall_restD :
    (LrG (restSibSmallD A R F P ds xs dec hL)).encodeIndex = (F.withProvers P).encodeIndex ∧
      (LrG (restSibSmallD A R F P ds xs dec hL)).honestOutOfDomainAnswer = (F.withProvers P).honestOutOfDomainAnswer ∧
      (LrG (restSibSmallD A R F P ds xs dec hL)).hasCollisionAt = (F.withProvers P).hasCollisionAt ∧
      (LrG (restSibSmallD A R F P ds xs dec hL)).decodeIndex = (F.withProvers P).decodeIndex ∧
      (LrG (restSibSmallD A R F P ds xs dec hL)).offline = (F.withProvers P).offline ∧
      (LrG (restSibSmallD A R F P ds xs dec hL)).maxBatchSize = (F.withProvers P).maxBatchSize ∧
      (LrG (restSibSmallD A R F P ds xs dec hL)).onlineBatch = (F.withProvers P).onlineBatch ∧
      (LrG (restSibSmallD A R F P ds xs dec hL)).early = (F.withProvers P).early :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end OnBytes.Flat
