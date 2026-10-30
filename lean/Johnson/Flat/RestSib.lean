-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/RestSib.lean: the object with records whose link is `linkSibFull` | `linkSibSmall`, as
a written value.

Johnson/Flat/ArmSibAt.lean shows that the entry's arm is sound at an object
`LrG T` (Johnson/EntryRec/Defs.lean) whose link is `linkSibFull` | `linkSibSmall`
(OnBytes/Flat/LinkSibAt.lean), for every T whose decoder and collisions are those of the
configuration of a stored table with a record. This is said under the hypotheses that stand in the
statement itself, which this comment does not list; it is no claim that they hold. Here T is
written: `restSibFull` | `restSibSmall` takes every field from the object of three files' protocols
F over that configuration
(`Files.withProvers`, OnBytes/Flat/Object.lean), but three: the link, which the type names; the link's
honest prover, which is a parameter; and `late`, which is `none`. It is meant at F := `threeProtocolsFromDryRunAtFullSize` |
`threeProtocolsFromDryRunAtSmallSize` (OnBytes/Flat/FilesAt.lean); nothing here reads which F it is.

Main definitions: `restSibFull`, `restSibSmall`.
Main theorems, each by the definitions: `restSibFull_dcd`, `restSibFull_coll` (the two equations
that Johnson/Flat/ArmSibAt.lean asks), `restSibFull_late`, `restSibFull_link`,
`restSibFull_rest`;
and the like at the small size.

Not claimed here: soundness or hiding. The honest provers are data that the object's type asks;
nothing is asked of them, and no statement here reads them. The claims A, the rest R, the three
files' protocols F and the provers P are parameters. `late` is `none` because the field goes into
Link's compiled verifier too (Johnson/EntryRec/Defs.lean), while `early` stays F's: so the session
of this object is F's only where F's own `late` is `none`. F's own entry protocol is dropped. At a
general F the object differs from F's own in the link, the link's honest prover and `late`. Where
F's own entry protocol is this link, its `late` is `none` and hL is F's own prover, it is F's
object. For proofs only; no program imports this file.


-/
import OnBytes.Flat.Object
import OnBytes.Flat.LinkSibAt
import Johnson.EntryRec.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat

open Hiop Cb Cb.Ood OnBytes.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.RunA (RestR LrG)

/-! ## The full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))

/-- What the object holds beside its word length, its symbols and its link, where the link is
`linkSibFull`. -/
def restSibFull : RestR (DecR.configurationOfStoredTable A R).I X ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a
    linkSibFull where
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
theorem restSibFull_dcd : (restSibFull A R F P hL).dcd = (DecR.configurationOfStoredTable A R).D := rfl

/-- Its collisions are the configuration's. -/
theorem restSibFull_coll : (restSibFull A R F P hL).coll = (DecR.configurationOfStoredTable A R).coll := rfl

/-- No part of an instance comes late. -/
theorem restSibFull_late : (LrG (restSibFull A R F P hL)).late = none := rfl

/-- The link of the object is `linkSibFull`. -/
theorem restSibFull_link : (LrG (restSibFull A R F P hL)).link = linkSibFull := rfl

/-- All else is the three files' object's: the encoding, the answers, the collisions, the decoder,
the key file's protocol, the number of slots, the proof file's protocol, and what of an instance
comes early. -/
theorem restSibFull_rest :
    (LrG (restSibFull A R F P hL)).encodeIndex = (F.withProvers P).encodeIndex ∧
      (LrG (restSibFull A R F P hL)).honestOutOfDomainAnswer = (F.withProvers P).honestOutOfDomainAnswer ∧
      (LrG (restSibFull A R F P hL)).hasCollisionAt = (F.withProvers P).hasCollisionAt ∧
      (LrG (restSibFull A R F P hL)).decodeIndex = (F.withProvers P).decodeIndex ∧
      (LrG (restSibFull A R F P hL)).offline = (F.withProvers P).offline ∧
      (LrG (restSibFull A R F P hL)).maxBatchSize = (F.withProvers P).maxBatchSize ∧
      (LrG (restSibFull A R F P hL)).onlineBatch = (F.withProvers P).onlineBatch ∧
      (LrG (restSibFull A R F P hL)).early = (F.withProvers P).early :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

/-! ## The small size -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (R : (srS.toDecR srZ 524285).RelationsAndEncoding A)
  (F : Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))

/-- What the object holds beside its word length, its symbols and its link, where the link is
`linkSibSmall`. -/
def restSibSmall : RestR (DecR.configurationOfStoredTable A R).I X ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (Fin 1 → (Fin 19 → GE) × NZ) ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a
    linkSibSmall where
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
theorem restSibSmall_dcd : (restSibSmall A R F P hL).dcd = (DecR.configurationOfStoredTable A R).D := rfl

/-- Its collisions are the configuration's. -/
theorem restSibSmall_coll : (restSibSmall A R F P hL).coll = (DecR.configurationOfStoredTable A R).coll := rfl

/-- No part of an instance comes late. -/
theorem restSibSmall_late : (LrG (restSibSmall A R F P hL)).late = none := rfl

/-- The link of the object is `linkSibSmall`. -/
theorem restSibSmall_link : (LrG (restSibSmall A R F P hL)).link = linkSibSmall := rfl

/-- All else is the three files' object's: the encoding, the answers, the collisions, the decoder,
the key file's protocol, the number of slots, the proof file's protocol, and what of an instance
comes early. -/
theorem restSibSmall_rest :
    (LrG (restSibSmall A R F P hL)).encodeIndex = (F.withProvers P).encodeIndex ∧
      (LrG (restSibSmall A R F P hL)).honestOutOfDomainAnswer = (F.withProvers P).honestOutOfDomainAnswer ∧
      (LrG (restSibSmall A R F P hL)).hasCollisionAt = (F.withProvers P).hasCollisionAt ∧
      (LrG (restSibSmall A R F P hL)).decodeIndex = (F.withProvers P).decodeIndex ∧
      (LrG (restSibSmall A R F P hL)).offline = (F.withProvers P).offline ∧
      (LrG (restSibSmall A R F P hL)).maxBatchSize = (F.withProvers P).maxBatchSize ∧
      (LrG (restSibSmall A R F P hL)).onlineBatch = (F.withProvers P).onlineBatch ∧
      (LrG (restSibSmall A R F P hL)).early = (F.withProvers P).early :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end OnBytes.Flat
