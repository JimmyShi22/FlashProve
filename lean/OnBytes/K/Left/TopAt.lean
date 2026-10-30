-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/TopAt.lean: `entry_left` (OnBytes/K/Left/Top.lean) at the two grounds "record with
work": the full size and the small size.

Main theorems. `entryLeftAt_full`, `entryLeftAt_small`: from the yes of the Lean program
`verify-on-bytes` on a call's files, and the parameter file's lines being the ground's, to the
strict converter's value on these files and the yes of `verifyE` on it. The conditions on the ground
are paid here: the tables have a record (Conv.lean), the four conditions for the seeds
(SeedsAt.lean), the pins (Pins.lean), and the standard size's lines are the ground's (by rfl).

What is not claimed. `LaxAt` stays a hypothesis, asked at every yes of the program. It is proved at
both grounds in OnBytes/K/Left/LaxDone.lean (`restAll_full`, `restAll_small`, with `laxAt_of` of
OnBytes/K/Left/LaxEnd.lean). All that the head of OnBytes/K/Left/Top.lean does not claim. For proofs
only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Top
import OnBytes.TypedOracleCompiler.Slice.EntryDescOk

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left

open OnBytes.Tie
open TypedOracleCompiler.Slice

/-- What `entry_left` concludes, for all files, at a ground and a standard size. -/
def EntryLeftAt (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (z : Params.StdSize) : Prop :=
  ∀ (F : Files) (id : String) (table further : Params.TableName),
    PortYesAt F id table further → G.SaysLines F.pol →
    ∃ (a : AskedE) (nid : String), Model.Verify.idAsked id = some nid ∧ a.first = table ∧
      a.further = further ∧
      prepE G z false F.pol F.lay F.KL F.key F.ent =
        .ok ⟨Params.configurationDigest [F.pol, F.lay, F.KL], Params.configurationDigest_size _,
          linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]), a⟩ ∧
      verifyE G hok ⟨nid, Params.configurationDigest [F.pol, F.lay, F.KL],
        Params.configurationDigest_size _⟩ a = true

/-- `LaxAt` at every yes of the program. -/
def LaxAll (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true) : Prop :=
  ∀ (F : Files) (id : String) (table further : Params.TableName),
    PortYesAt F id table further → G.SaysLines F.pol →
    LaxAt G hok (Params.configurationDigest [F.pol, F.lay, F.KL])
      (Params.configurationDigest_size _) table further F.ent

/-- At the full size. -/
theorem entryLeftAt_full (hlax : LaxAll recordGround record_ok) :
    EntryLeftAt recordGround record_ok Params.stdFull := fun F id table further h hl =>
  entry_left recordGround record_ok record_answers record_fit record_pins Params.stdFull rfl h hl
    (hlax F id table further h hl)

/-- At the small size. -/
theorem entryLeftAt_small (hlax : LaxAll smallRecordGround small_record_ok) :
    EntryLeftAt smallRecordGround small_record_ok Params.stdSmall := fun F id table further h hl =>
  entry_left smallRecordGround small_record_ok small_record_answers small_record_fit
    small_record_pins Params.stdSmall rfl h hl (hlax F id table further h hl)

end OnBytes.K.Left
