-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsAt.lean: an input of the top arm by arm (`InputArms`, Johnson/Top/OnFilesArms.lean)
and the tie's three letters (`TieArms`, Johnson/Top/TieOnFilesArms.lean), made from an input r of
the entry's arm (`ArmIn`, Johnson/Top/TieArm.lean); and, at these two, the fields `records` and
`entry` of `ArmTies`.

Definitions, statements and proofs; general in r. What it is for: `InputArms`, `TieArms` and
`ArmTies` are stated over letters. Here the object, the annotations, the entry file's arm and the
reading of a table as a record are r's own, so that the tie of the entry file (`EntryPart`,
OnBytes/K/Parts.lean) can be brought to the top's named hypotheses.

Main names (namespace `OnBytes.K`):
  `ArmsMore r`: what an `InputArms` holds beside r: the key file's and the proof file's arms, at
    r's object and annotations, and the scheme's letters.
  `r.inputArms M`: the `InputArms` with I, X, L, aT, aL := those of r, armE := `r.armE`
    (Johnson/Top/TieArmOver.lean), and the rest from M.
  `r.tieArms M Sv Ex`: the `TieArms` with Served := Sv, recOf := `r.recOf`, Excepted := Ex.
  `armTies_records`, `armTies_entry`: the two fields, from `EntryPart r.shape R₀`; asked: a served
    statement is served at r (hSv); the reading R reads the entry file as R₀ does (hent).
  `armTies_of`: `ArmTies (r.tieArms M Sv Ex) R`, from these two and the fields `key`, `proof` and
    `idHash` as premises, each in its own spelling. That the term has this type is Lean's check
    that the two theorems are the two fields.

Limits.
  1. No input is written here: r, M, Sv, Ex, R₀ and R are letters. That any r has `EntryPart` is
     shown in other files, at their inputs.
  2. `armTies_entry` ends in the first limb of "yes, or the files are excepted": the entry's part
     excepts no files. Ex is a free letter: at "every file" the premises hkey and hproof hold for
     nothing, and the tie is then silent on two of the three files. What is meant is the union of
     what the key file's and the proof file's own ties except; that is written nowhere here.
  3. The fields `key`, `proof` and `idHash` are premises. Nothing here says that they can hold
     together with `EntryPart` at one r, one Sv, one Ex and one R.
  4. Served is one predicate and R one reading for all five fields, while each arm's tie is stated
     at a shape and a reading of its own. hSv and hent carry the entry's; the like for the two other
     arms is owed where they are brought.
  5. The three arms may each go through a coding of their own. Nothing here compares the codings,
     and nothing shows that one function reads the words of all three off a log.
  6. No bound is in this file: nothing on `ArmBound`, on soundness or on a random function.
  For proofs only; no program imports this file.

-/
import Johnson.Top.TieOnFilesArms
import Johnson.Top.TieArmOver

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.K

open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open VerifiableInference (Token)
open VerifiableInference.OnPublicFiles

/-- What an input of the top arm by arm holds beside the entry's arm's own input r: the two other
arms, at r's object and annotations, and the letters of the scheme. -/
structure ArmsMore (r : ArmIn) where
  /-- the key file's arm -/
  armK : Dig 256 → r.L.Rec → OneProtocolProof 256 (batTC r.L r.aT) → Rom.OComp (rom 256) Bool
  /-- the proof file's arm -/
  armP : Dig 256 → r.X → r.L.Rec → ℕ → OneProtocolProof 256 r.L.onlineBatch → Rom.OComp (rom 256) Bool
  enc : KeyRoot 256 r.L → Option ZKCP.Str
  build : List Token × List Token → List Token → Option r.X
  nextToken : r.I → List Token → Option Token
  ISK : Type
  commit : r.I → Rom.OComp (rom 256) (KeyRoot 256 r.L × ISK)
  prove : ISK → (l : List (r.X × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 r.L r.aT r.aL) l)
  bound : ℕ
  π₀ : KeyRoot 256 r.L × OfflineLinkOnlineProof 256 r.L r.aT r.aL

/-- The input of the top arm by arm at r: its object and annotations are r's; its entry file's arm
is `r.armE`. -/
def ArmIn.inputArms (r : ArmIn) (M : ArmsMore r) : InputArms where
  I := r.I
  X := r.X
  L := r.L
  aT := r.aT
  aL := r.aL
  armK := M.armK
  armE := r.armE
  armP := M.armP
  enc := M.enc
  build := M.build
  nextToken := M.nextToken
  ISK := M.ISK
  commit := M.commit
  prove := M.prove
  bound := M.bound
  π₀ := M.π₀

/-- The tie's three letters at r: the served statements are those of Sv; a table is read as a record
as r reads it; the excepted files are those of Ex. -/
def ArmIn.tieArms (r : ArmIn) (M : ArmsMore r) (Sv : UserStm → Prop) (Ex : Files → Prop) :
    TieArms (r.inputArms M) :=
  ⟨Sv, r.recOf, Ex⟩

variable (r : ArmIn) (M : ArmsMore r) (Sv : UserStm → Prop) (Ex : Files → Prop)
  (hSv : ∀ x, Sv x → r.Served x) (R₀ : Reading5 r.shape) (A : EntryPart r.shape R₀)
  (R : Reading5 (shapeArms (r.tieArms M Sv Ex)))

include hSv A in
/-- The field `records` of `ArmTies` at these two. -/
theorem armTies_records :
    ∀ F o id table further, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (r.tieArms M Sv Ex).Served (stmOf F o) →
      (∃ c, (r.tieArms M Sv Ex).recOf (stmOf F o) table = some c) ∧
        ∃ cj, (r.tieArms M Sv Ex).recOf (stmOf F o) further = some cj :=
  fun F o id table further hi hb hp hs =>
    records_of_entryPart r R₀ A F o id table further hi hb hp (hSv _ hs)

include hSv A in
/-- The field `entry` of `ArmTies` at these two, at a reading whose reading of the entry file is
R₀'s. -/
theorem armTies_entry (hent : ∀ x key ent, R.ent x key ent = R₀.ent x key ent) :
    ∀ F o id table further c cj, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (r.tieArms M Sv Ex).Served (stmOf F o) →
      (r.tieArms M Sv Ex).recOf (stmOf F o) table = some c →
      (r.tieArms M Sv Ex).recOf (stmOf F o) further = some cj →
      (∃ πL, R.ent (stmOf F o) F.key F.ent = some (further, πL) ∧
        ((r.inputArms M).armE (bytesToDig table.root) (bytesToDig further.root) c cj πL).det
          (fun _ => oBits ()) = true) ∨ (r.tieArms M Sv Ex).Excepted F :=
  fun F o id table further c cj hi hb hp hs hc hcj => by
    obtain ⟨πL, he, hv⟩ :=
      entry_of_entryPart r R₀ A F o id table further c cj hi hb hp (hSv _ hs) hc hcj
    exact .inl ⟨πL, (hent _ _ _).trans he, hv⟩

include hSv A in
/-- `ArmTies` at these two, from the entry's part and the three other fields as premises, each in
its own spelling. That this term has the type `ArmTies` is Lean's check that `armTies_records` and
`armTies_entry` are the fields `records` and `entry`. -/
theorem armTies_of (hent : ∀ x key ent, R.ent x key ent = R₀.ent x key ent)
    (hkey : ∀ F o id table further c, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (r.tieArms M Sv Ex).Served (stmOf F o) →
      (r.tieArms M Sv Ex).recOf (stmOf F o) table = some c →
      (∃ πT, R.key (stmOf F o) F.key = some (table, πT) ∧
        ((r.inputArms M).armK (bytesToDig table.root) c πT).det (fun _ => oBits ()) = true) ∨
        (r.tieArms M Sv Ex).Excepted F)
    (hproof : ∀ F o id table further cj, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (r.tieArms M Sv Ex).Served (stmOf F o) →
      (r.tieArms M Sv Ex).recOf (stmOf F o) further = some cj →
      (∃ i πB, (r.inputArms M).build (promptOf (stmOf F o), outputOf (stmOf F o))
          (auxOf (stmOf F o)) = some i ∧
        R.prf (stmOf F o) F.ent F.proof F.entry = some πB ∧
        ((r.inputArms M).armP (bytesToDig further.root) i cj πB.1 πB.2).det
          (fun _ => oBits ()) = true) ∨ (r.tieArms M Sv Ex).Excepted F)
    (hid : ∀ F o id table further c pl, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (r.tieArms M Sv Ex).Served (stmOf F o) →
      Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl →
      (r.tieArms M Sv Ex).recOf (stmOf F o) table = some c →
      ∃ code, (r.inputArms M).enc ⟨bytesToDig table.root, c⟩ = some code ∧
        oBits () code = bytesToDig (Key.commitmentId pl.chains.tableShape pl.cfg table)) :
    ArmTies (r.tieArms M Sv Ex) R :=
  ⟨armTies_records r M Sv Ex hSv R₀ A, hkey, armTies_entry r M Sv Ex hSv R₀ A R hent, hproof,
    hid⟩

end OnBytes.K
