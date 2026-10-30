-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsAtSizes.lean: an input of the top arm by arm (`InputArms`,
Johnson/Top/OnFilesArms.lean), the tie's letters (`TieArms`) and one reading of the files, at the
form that the three files' own object and wiring have at the full size and at the small example,
with letters left (limit 1); and, at these, the fields `records` and `entry` of `ArmTies`
(Johnson/Top/TieOnFilesArms.lean).

Definitions, statements and proofs: Johnson/Top/ArmsAt.lean at r := `armTopFull` | `armTopSmall`
(Johnson/Top/ArmTopFull.lean, ArmTopSmall.lean). The same names with Small at the small example.

Main names (namespace `OnBytes.K.Arm`):
  `inputArmsFull A E G P Z sX num M`: `(armTopFull A E G P Z sX num).inputArms M`.
  `tieArmsFull … M SvK SvP Ex`: Served x := x is served at Z, and SvK x, and SvP x; recOf := the
    arm's own (`recOfArm`, OnBytes/K/ArmLetters.lean); Excepted := Ex.
  `readingFull … rdK rdP`: one reading for all three files: the entry file as `readTopFull` reads
    it; rdK, rdP: the key file's and the proof file's.
  `armTies_records_full`, `armTies_entry_full`: the two fields, in their own spelling, from
    `entryPart_topFull_tests` (Johnson/Top/ArmTopTests.lean). Asked: Z's parameter file says the
    ground's lines (hZ); two tests on the numbers of blocks that can be run (hK, hP).

Limits.
  1. Letters are left. M holds the key file's and the proof file's arms and the scheme's eight
     letters; SvK, SvP, Ex, rdK and rdP are letters too; so are A, E, G, P, sX, num and Z's bytes.
     So this is an input at the description's own object, wiring and entry arm, and not yet a
     written input of the top.
  2. The fields `key`, `proof` and `idHash` of `ArmTies` are not shown here, at any M. Ex is a free
     letter: see limit 2 of ArmsAt.lean.
  3. That any statement is served is not claimed. SvK and SvP are letters; whether the conditions
     that are meant there can hold of one real call together with "served at Z" is shown by nobody.
  4. The entry's arm is the lax one. Its coding is laid, not found: it writes the chain queries of
     the two big files behind an escape (the heads of ArmTopFull.lean and
     Johnson/Top/TieArmSibK.lean). The three arms may each go through a coding of their own; nothing
     shows that three codings exist that read one word off a log.
  5. All limits of the heads of ArmsAt.lean, ArmTopFull.lean and ArmTopTests.lean stand.
  6. No bound is in this file.
  For proofs only; no program imports this file.

-/
import Johnson.Top.ArmsAt
import Johnson.Top.ArmTopTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.K.Arm

open Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Tie Hiop Cb Cb.Ood OnBytes.K OnBytes.K.Left
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)

section Full
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers) (Z : Pub) (sX : Ser X)
  (num : ℕ → Plains (restFullAt A E G P).bat.loc.shape → Bool)
  (M : ArmsMore (armTopFull A E G P Z sX num)) (SvK SvP : UserStm → Prop) (Ex : Files → Prop)

/-- An input of the top arm by arm at the three files' own object and wiring; A, E, G, P, Z, sX, num
and M are letters. -/
def inputArmsFull : InputArms := (armTopFull A E G P Z sX num).inputArms M

/-- The tie's letters there: a statement is served if it is served at Z and meets the key's and the
proof's own conditions SvK and SvP. -/
def tieArmsFull : TieArms (inputArmsFull A E G P Z sX num M) :=
  (armTopFull A E G P Z sX num).tieArms M (fun x => servedArm Z x = true ∧ SvK x ∧ SvP x) Ex

variable
  (rdK : (x : UserStm) → ByteArray →
    Option (Params.TableName × (shapeArms (tieArmsFull A E G P Z sX num M SvK SvP Ex)).PiT x))
  (rdP : (x : UserStm) → ByteArray → ByteArray → ℕ →
    Option ((shapeArms (tieArmsFull A E G P Z sX num M SvK SvP Ex)).PiB x))

/-- One reading of the files: the entry file as `readTopFull` reads it; rdK, rdP: the key
file's and the proof file's. -/
def readingFull : Reading5 (shapeArms (tieArmsFull A E G P Z sX num M SvK SvP Ex)) where
  key := rdK
  ent := (readTopFull A E G P Z sX num).ent
  prf := rdP

variable (hZ : recordGround.SaysLines Z.pol) (hK : blocksFitB .two (dataKFull G) = true)
  (hP : blocksFitB .two (dataPFull G) = true)

include hZ hK hP in
/-- The field `records` of `ArmTies` at this input. -/
theorem armTies_records_full :
    ∀ F o id table further, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (tieArmsFull A E G P Z sX num M SvK SvP Ex).Served (stmOf F o)
          →
      (∃ c, (tieArmsFull A E G P Z sX num M SvK SvP Ex).recOf (stmOf F o) table = some c) ∧
        ∃ cj, (tieArmsFull A E G P Z sX num M SvK SvP Ex).recOf (stmOf F o) further = some cj :=
  armTies_records (armTopFull A E G P Z sX num) M _ Ex (fun _ h => h.1) (readTopFull A E G P Z sX
      num)
    (entryPart_topFull_tests A E G P Z sX num hZ hK hP)

include hZ hK hP in
/-- The field `entry` of `ArmTies` at this input and this reading. -/
theorem armTies_entry_full :
    ∀ F o id table further c cj, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (tieArmsFull A E G P Z sX num M SvK SvP Ex).Served (stmOf F o)
          →
      (tieArmsFull A E G P Z sX num M SvK SvP Ex).recOf (stmOf F o) table = some c →
      (tieArmsFull A E G P Z sX num M SvK SvP Ex).recOf (stmOf F o) further = some cj →
      (∃ πL, (readingFull A E G P Z sX num M SvK SvP Ex rdK rdP).ent (stmOf F o) F.key F.ent =
          some (further, πL) ∧
        ((inputArmsFull A E G P Z sX num M).armE (bytesToDig table.root) (bytesToDig further.root) c
            cj
          πL).det (fun _ => oBits ()) = true) ∨ (tieArmsFull A E G P Z sX num M SvK SvP Ex).Excepted
              F :=
  armTies_entry (armTopFull A E G P Z sX num) M _ Ex (fun _ h => h.1) (readTopFull A E G P Z sX num)
    (entryPart_topFull_tests A E G P Z sX num hZ hK hP) (readingFull A E G P Z sX num M SvK SvP Ex
        rdK rdP)
    fun _ _ _ => rfl

end Full

section Small
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers) (Z : Pub) (sX : Ser X)
  (num : ℕ → Plains (restSmallAt A E G P).bat.loc.shape → Bool)
  (M : ArmsMore (armTopSmall A E G P Z sX num)) (SvK SvP : UserStm → Prop) (Ex : Files → Prop)

/-- An input of the top arm by arm at the three files' own object and wiring; A, E, G, P, Z, sX, num
and M are letters. -/
def inputArmsSmall : InputArms := (armTopSmall A E G P Z sX num).inputArms M

/-- The tie's letters there: a statement is served if it is served at Z and meets the key's and the
proof's own conditions SvK and SvP. -/
def tieArmsSmall : TieArms (inputArmsSmall A E G P Z sX num M) :=
  (armTopSmall A E G P Z sX num).tieArms M (fun x => servedArm Z x = true ∧ SvK x ∧ SvP x) Ex

variable
  (rdK : (x : UserStm) → ByteArray →
    Option (Params.TableName × (shapeArms (tieArmsSmall A E G P Z sX num M SvK SvP Ex)).PiT x))
  (rdP : (x : UserStm) → ByteArray → ByteArray → ℕ →
    Option ((shapeArms (tieArmsSmall A E G P Z sX num M SvK SvP Ex)).PiB x))

/-- One reading of the files: the entry file as `readTopSmall` reads it; rdK, rdP: the key
file's and the proof file's. -/
def readingSmall : Reading5 (shapeArms (tieArmsSmall A E G P Z sX num M SvK SvP Ex)) where
  key := rdK
  ent := (readTopSmall A E G P Z sX num).ent
  prf := rdP

variable (hZ : smallRecordGround.SaysLines Z.pol) (hK : blocksFitB .two (dataKSmall G) = true)
  (hP : blocksFitB .two (dataPSmall G) = true)

include hZ hK hP in
/-- The field `records` of `ArmTies` at this input. -/
theorem armTies_records_small :
    ∀ F o id table further, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (tieArmsSmall A E G P Z sX num M SvK SvP Ex).Served (stmOf F o)
          →
      (∃ c, (tieArmsSmall A E G P Z sX num M SvK SvP Ex).recOf (stmOf F o) table = some c) ∧
        ∃ cj, (tieArmsSmall A E G P Z sX num M SvK SvP Ex).recOf (stmOf F o) further = some cj :=
  armTies_records (armTopSmall A E G P Z sX num) M _ Ex (fun _ h => h.1) (readTopSmall A E G P Z sX
      num)
    (entryPart_topSmall_tests A E G P Z sX num hZ hK hP)

include hZ hK hP in
/-- The field `entry` of `ArmTies` at this input and this reading. -/
theorem armTies_entry_small :
    ∀ F o id table further c cj, o.id = some id → o.bits = 128 →
      PortYesAt F id table further → (tieArmsSmall A E G P Z sX num M SvK SvP Ex).Served (stmOf F o)
          →
      (tieArmsSmall A E G P Z sX num M SvK SvP Ex).recOf (stmOf F o) table = some c →
      (tieArmsSmall A E G P Z sX num M SvK SvP Ex).recOf (stmOf F o) further = some cj →
      (∃ πL, (readingSmall A E G P Z sX num M SvK SvP Ex rdK rdP).ent (stmOf F o) F.key F.ent =
          some (further, πL) ∧
        ((inputArmsSmall A E G P Z sX num M).armE (bytesToDig table.root) (bytesToDig further.root)
            c cj
          πL).det (fun _ => oBits ()) = true) ∨ (tieArmsSmall A E G P Z sX num M SvK SvP
              Ex).Excepted F :=
  armTies_entry (armTopSmall A E G P Z sX num) M _ Ex (fun _ h => h.1) (readTopSmall A E G P Z sX
      num)
    (entryPart_topSmall_tests A E G P Z sX num hZ hK hP) (readingSmall A E G P Z sX num M SvK SvP Ex
        rdK rdP)
    fun _ _ _ => rfl

end Small

end OnBytes.K.Arm
