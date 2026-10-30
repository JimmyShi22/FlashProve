-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/SibLetters.lean: the lax verifier's yes at every yes of the program, with the three
numbers of a record (row variables, coordinates of a seed's point, answers) as written numbers.

`LaxAt` (OnBytes/K/Left/Top.lean) stands at the numbers that are read off the ground's parameters:
`G.q.link.table.v`, `.cubeBits`, `.answers`. The link over pairs of records
(`linkSibFull`, `linkSibSmall`, OnBytes/Flat/LinkSibAt.lean) stands at written numbers: 29 and 1, at
the small example 19 and 1. The number of coordinates is equal to the written one by a theorem. The
types of instances and of typed strings hang on these numbers, so the statement is said here as a
proposition in three letters and carried along the equations.

Main names:
  `LaxAtL`: `LaxAt` with the three numbers as letters; `laxAtL_at`: at the ground's own numbers it
    is `LaxAt`, by unfolding.
  `laxAll_full`, `laxAll_small`: `LaxAll` at the two grounds.
  `lax_full`, `lax_small`: at every yes of the program whose parameter file has the ground's lines,
    `LaxAtL` at the written numbers.
  `recX_full`, `recX_small`: there the instance is the instance made of the two records that are
    read off the two tables and seeds, at the written numbers.

Limits: values alone, at one fixed oracle. Nothing on soundness; no probability. That some files
meet `PortYesAt` is not shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxDone
import OnBytes.K.Left.SibFit
import OnBytes.Flat.LinkSibAt

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left

open OnBytes.Tie OnBytes.Slice OnBytes.Flat
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PQ (bodyS)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig)

section
variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- `LaxAt` with the three numbers of a record as letters. -/
def LaxAtL (c : ByteArray) (hc : c.size = 32) (table further : Params.TableName)
    (ent : ByteArray) (v lg s : ℕ) : Prop :=
  ∀ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
    (π : OneProtocolProof 256 (PSXE (entryXD G c) (decRun (linkAtCfg G.q c) v lg s)).up),
    Entry.read (linkAtCfg G.q c) table ent = .ok r → r.further = further →
    seedsUnder recordSeeds (linkAtCfg G.q c) table = some l0 →
    seedsUnder recordSeeds (linkAtCfg G.q c) further = some l1 →
    assembleS (entryXD G c) (decRun (linkAtCfg G.q c) v lg s) r.chain.out = some π →
    laxE (entryXD G c) (decRun (linkAtCfg G.q c) v lg s)
      (bodyS (entryXD G c).a (entryXD G c).base.plan.salt)
      (ownES (entryXD G c) (hok c hc)) (earlyTwo (d1Run lg s))
      (fun _ => TSE (entryXD G c) (seedEntry lg s))
      (EntryRunTop.famOf (entryXD G c) hc (d1Run lg s) G.q.link.table)
      [bytesToDig table.root, bytesToDig further.root]
      (xOfAskedC lg s ⟨table, further, l0, l1, r.chain.out⟩) π = true

/-- At the ground's own numbers it is `LaxAt`. -/
theorem laxAtL_at (c : ByteArray) (hc : c.size = 32) (table further : Params.TableName)
    (ent : ByteArray) (h : LaxAt G hok c hc table further ent) :
    LaxAtL G hok c hc table further ent G.q.link.table.v G.q.link.table.cubeBits
      G.q.link.table.answers := h

end

/-- `LaxAt` at every yes of the program, at the full size. -/
theorem laxAll_full : LaxAll recordGround record_ok := fun F id table further h hl =>
  laxAt_of recordGround record_ok (from_port_full h hl) (restAll_full F id table further h hl)

/-- The same at the small example. -/
theorem laxAll_small : LaxAll smallRecordGround small_record_ok := fun F id table further h hl =>
  laxAt_of smallRecordGround small_record_ok (from_port_small h hl)
    (restAll_small F id table further h hl)

/-- The full-size ground's three numbers. -/
theorem numbers_full : recordGround.q.link.table.v = frS.P.v ∧
    recordGround.q.link.table.cubeBits = 29 ∧ recordGround.q.link.table.answers = 1 :=
  ⟨by decide +kernel, Shapes.zFull_lg, by decide +kernel⟩

/-- The small ground's three numbers. -/
theorem numbers_small : smallRecordGround.q.link.table.v = srS.P.v ∧
    smallRecordGround.q.link.table.cubeBits = 19 ∧ smallRecordGround.q.link.table.answers = 1 :=
  ⟨by decide +kernel, Shapes.zSmall_lg, by decide +kernel⟩

section
variable {F : Files} {id : String} {table further : Params.TableName}
  (h : PortYesAt F id table further)

include h in
/-- The lax verifier's yes at the written numbers, at the full size. -/
theorem lax_full (hl : recordGround.SaysLines F.pol) :
    LaxAtL recordGround record_ok (Params.configurationDigest [F.pol, F.lay, F.KL])
      (Params.configurationDigest_size _) table further F.ent frS.P.v 29 1 := by
  have h1 := laxAtL_at recordGround record_ok _ _ table further F.ent
    (laxAll_full F id table further h hl)
  rw [numbers_full.1, numbers_full.2.1, numbers_full.2.2] at h1
  exact h1

include h in
/-- The same at the small example. -/
theorem lax_small (hl : smallRecordGround.SaysLines F.pol) :
    LaxAtL smallRecordGround small_record_ok (Params.configurationDigest [F.pol, F.lay, F.KL])
      (Params.configurationDigest_size _) table further F.ent srS.P.v 19 1 := by
  have h1 := laxAtL_at smallRecordGround small_record_ok _ _ table further F.ent
    (laxAll_small F id table further h hl)
  rw [numbers_small.1, numbers_small.2.1, numbers_small.2.2] at h1
  exact h1

include h in
/-- The instance is the instance made of the two records, at the written numbers. -/
theorem recX_full (hl : recordGround.SaysLines F.pol) (l0 l1 : List (List E × E))
    (o : Fmt.ChainOut) :
    recX (recsOf frS.P.v 29 1 ⟨table, further, l0, l1, o⟩) =
      xOfAskedC 29 1 ⟨table, further, l0, l1, o⟩ := by
  obtain ⟨h0, h1, k0, k1⟩ := answers_at recordGround record_answers record_field h hl
  rw [numbers_full.1, numbers_full.2.2] at h0 h1
  exact recX_recsOf _ _ _ _ h0 h1 k0 k1

include h in
/-- The same at the small example. -/
theorem recX_small (hl : smallRecordGround.SaysLines F.pol) (l0 l1 : List (List E × E))
    (o : Fmt.ChainOut) :
    recX (recsOf srS.P.v 19 1 ⟨table, further, l0, l1, o⟩) =
      xOfAskedC 19 1 ⟨table, further, l0, l1, o⟩ := by
  obtain ⟨h0, h1, k0, k1⟩ := answers_at smallRecordGround small_record_answers small_record_field
    h hl
  rw [numbers_small.1, numbers_small.2.2] at h0 h1
  exact recX_recsOf _ _ _ _ h0 h1 k0 k1

end

end OnBytes.K.Left
