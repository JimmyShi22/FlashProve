-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxDone.lean: the five fields of `LaxRest` at every yes of the program, at the two
grounds with a record, without a premise; and with them the left half at both grounds.

The last join. `restAll_of` (OnBytes/K/Left/LaxRestAll.lean) asks two things: the field "walks" and
the field "accept" at every yes of the program. The first is `walks_rest`
(OnBytes/K/Left/LaxWalksRest.lean) at what the exit code 0 gives (`ground`,
OnBytes/K/Left/LaxGround.lean): the reader's equation, and that the statement's items hold the two
roots. The second is `accept_port_full`, `accept_port_small` (OnBytes/K/Left/LaxAcceptPort.lean).

Main names:
  `walks_port`: the field "walks" at every yes of the program, at any ground.
  `restAll_full`, `restAll_small`: `RestAll` at `recordGround`, `smallRecordGround`.
  `left_full`, `left_small`: `EntryLeftAt` there (OnBytes/K/Left/TopAt.lean, LaxEnd.lean): from the
    yes of the Lean program `verify-on-bytes` on a call's files, whose parameter file has the
    ground's lines, to the strict converter's value on these files and the yes of `verifyE` on it.

Limits: every statement begins with "for all files with `PortYesAt` and `G.SaysLines`": that a file
meets them is not shown here. What `EntryLeftAt` does not say, it does not say here. Nothing on
soundness or on any hash's strength.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxWalksRest
import OnBytes.K.Left.LaxAcceptPort

set_option autoImplicit false

namespace OnBytes.K.Left
open TypedOracleCompiler.Slice
open OnBytes.Tie (EntryGround linkAtCfg AskedE recordGround smallRecordGround)

/-- The field "walks" at every yes of the program. hA, hb: two tests on the ground. -/
theorem walks_port (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (hA : (G.q.link.table.answers == 0) = false)
    (hb : (Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    (F : Files) (id : String) (table further : Params.TableName)
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) (r : Entry.EntryRead)
    (l0 l1 : List (List E × E))
    (hr : Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table
      F.ent = .ok r) (_ : r.further = further) :
    WalksAt G (Params.configurationDigest [F.pol, F.lay, F.KL])
      (Params.configurationDigest_size _) (hok _ (Params.configurationDigest_size _))
      ⟨table, further, l0, l1, r.chain.out⟩ := by
  obtain ⟨r', -, -, i, hr', -, -, -, -, -, e, -, hit⟩ := ground G hA h hl
  obtain rfl : r' = r := Except.ok.inj (hr'.symm.trans hr)
  have hc := Params.configurationDigest_size [F.pol, F.lay, F.KL]
  exact walks_rest G _ hc (hok _ hc) (within_of G hb _ hc)
    ⟨table, further, l0, l1, r'.chain.out⟩ _ _ _ _ e hit

/-- The five fields at every yes of the program, at the full size. -/
theorem restAll_full : RestAll recordGround record_ok :=
  restAll_of recordGround record_ok record_answers full_base_ok
    (walks_port recordGround record_ok record_answers full_base_ok) accept_port_full

/-- At the small example. -/
theorem restAll_small : RestAll smallRecordGround small_record_ok :=
  restAll_of smallRecordGround small_record_ok small_record_answers small_base_ok
    (walks_port smallRecordGround small_record_ok small_record_answers small_base_ok)
    accept_port_small

/-- The left half at the full size. -/
theorem left_full : EntryLeftAt recordGround record_ok Params.stdFull := leftAt_full restAll_full

/-- At the small example. -/
theorem left_small : EntryLeftAt smallRecordGround small_record_ok Params.stdSmall :=
  leftAt_small restAll_small

end OnBytes.K.Left
