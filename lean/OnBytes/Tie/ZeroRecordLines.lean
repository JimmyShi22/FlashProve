-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ZeroRecordLines.lean: from the entry function's exit code 0 to `RecordTiedAt`, at the
full size with a record, under one equation on the parameter file's lines.

The hypothesis on the configuration is one equation, on the parameter file's lines alone; the digest
is whatever the three files as read have. Under a record the digest enters the decision, through the
tables' names and so the seeds: so the conclusion is at `linkAtCfg recordRead c`.

Not claimed. Nothing on soundness; no probability; the Lean port; one chain of seven.

-/
import OnBytes.Tie.ZeroAt
import OnBytes.Tie.EntryClosedRec
import OnBytes.Tie.EntryRecord
import OnBytes.Tie.EntryAtCfgRecord
import OnBytes.Model.VerifyDigest

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (World)

/-- The typed digest has 32 bytes. -/
theorem recordCfg_size : Params.recordCfg.size = 32 := by decide +kernel

/-- Whether the base of the description is in order has the same value at `linkAtCfg p c` as at p:
`withinX_linkAtCfg`'s like. -/
theorem baseOk_linkAtCfg (p : Params.Link) (c : ByteArray) (rs : Params.Rounds) (st : ByteArray)
    (hc : c.size = p.given.cfg.size)
    (hp : p.given.bytes = Fmt.paramsBytes p.given.plan p.given.cfg p.given.items) :
    (Params.entrySpecOf (linkAtCfg p c) rs st).base.ok = (Params.entrySpecOf p rs st).base.ok := by
  refine specOk_reCfg (Params.entrySpecOf p rs st).base c
    (Fmt.paramsBytes p.given.plan c p.given.items) ?_ hc ?_
  · show _ = p.given.bytes.size
    rw [hp]
    exact size_paramsBytes _ _ _ _ hc
  · show ((Fmt.paramsBytes p.given.plan c p.given.items).extract 0
        (Fmt.paramsBytes p.given.plan c []).size == Fmt.paramsBytes p.given.plan c []) =
      (p.given.bytes.extract 0 (Fmt.paramsBytes p.given.plan p.given.cfg []).size ==
        Fmt.paramsBytes p.given.plan p.given.cfg [])
    rw [hp, paramsBytes_prefix, paramsBytes_prefix, Run.PQ.bytes_beq_self,
      Run.PQ.bytes_beq_self]

/-- For every c of 32 bytes the description at `linkAtCfg Params.recordRead c` and
`Params.recordRounds` is within the limits at every statement at which its base is in order. -/
theorem withinX_record_at (c : ByteArray) (hc : c.size = 32) (st : ByteArray)
    (hb : (Params.entrySpecOf (linkAtCfg Params.recordRead c) Params.recordRounds st).base.ok
      = true) :
    withinX (Params.entrySpecOf (linkAtCfg Params.recordRead c) Params.recordRounds st) = true := by
  rw [withinX_linkAtCfg Params.recordRead c Params.recordRounds st
    (hc.trans recordCfg_size.symm) rfl]
  refine withinX_record st ?_
  rw [← baseOk_linkAtCfg Params.recordRead c Params.recordRounds st
    (hc.trans recordCfg_size.symm) rfl]
  exact hb

/-- The dry run at keys of zeros does not read the digest. -/
theorem entryRoundsAny_linkAtCfg (p : Params.Link) (c : ByteArray) :
    Params.entryRoundsAny (linkAtCfg p c) = Params.entryRoundsAny p := rfl

/-- So at every digest it gives `Params.recordRounds`. -/
theorem record_rounds_at (c : ByteArray) :
    Params.entryRoundsAny (linkAtCfg Params.recordRead c) = some Params.recordRounds :=
  (entryRoundsAny_linkAtCfg Params.recordRead c).trans Params.record_rounds

/-- **AT THE BYTES SPELLED FROM THE TYPED PLAN AND ITEMS AT ANY DIGEST c OF 32 BYTES, A FIRST ROOT
OF 32 BYTES, A FILE BELOW ABOUT 2^32 BYTES: NO OTHER HYPOTHESIS:** `entry_closedR`'s three
conclusions. "Nothing assumed" means here: not the statement on codes; the hypotheses that stand in
the statement itself are assumed. -/
theorem entry_record_atCfg (c : ByteArray) (hc : c.size = 32)
    (first further : Params.TableName) (file : ByteArray)
    (h : Entry.check (recordBytesAt c) first file = .ok further) (h0 : first.root.size = 32)
    (hb : file.size + 16 ≤ 2 ^ 32 - 144) :
    further.root.size = 32 ∧ checkAtR Fmt.oracle (recordBytesAt c) first file = some further ∧
      EntryTiedR (linkAtCfg Params.recordRead c) Params.recordRounds first further file :=
  entry_closedR (recordBytesAt c) (linkAtCfg Params.recordRead c) Params.recordRounds
    (record_read_at c hc) (record_rounds_at c) (withinX_record_at c hc) hc first further file h h0 hb

/-- ONE EQUATION ON THE PARAMETER FILE: the lines that `Params.readLines` reads from it are
`Params.recordLines`, typed for the full size with a record and with work. PROVED OF NO FILE. That
this is a release's default parameter file is not stated. Of what else the parameter file holds, of
the layout file and of the scale file nothing is asked: they enter through the digest alone. -/
def SaysRecordLines (pol : ByteArray) : Prop :=
  (Params.readLines pol).toOption.map (·.1) = some Params.recordLines

/-- For such a parameter file, and any two other files, the parameter bytes of an entry's chain are
`recordBytesAt` of the three files' digest. -/
theorem saysRecordLines_bytes {pol : ByteArray} (h : SaysRecordLines pol) (lay kl : ByteArray) :
    Params.entryBytesOf pol lay kl =
      some (recordBytesAt (Params.configurationDigest [pol, lay, kl])) := by
  unfold Params.entryBytesOf
  cases hx : (Params.readLines pol).toOption with
  | none =>
    unfold SaysRecordLines at h
    rw [hx] at h
    cases h
  | some x =>
    unfold SaysRecordLines at h
    rw [hx] at h
    have e : x.1 = Params.recordLines := Option.some.inj h
    show (Params.entryParams x.1 (Params.configurationDigest [pol, lay, kl])).toOption = _
    rw [e, record_params_at]
    rfl

/-- What is concluded of values w, at c := the digest of the three configuration files as read.
Nothing on soundness; no probability. At the format's own oracle the clause on checkAtR is
equivalent to the program's yes (`entry_check_atR`). Of checkAtR at another function nothing is
proved; no bound is stated of it. The digest is BLAKE2b's, whatever function stands in the place of
the hash. -/
def RecordTiedAt (w : WholeSeen) : Prop :=
  w.p.chains.bytes .link =
      recordBytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]) ∧
    w.table.root.size = 32 ∧ w.further.root.size = 32 ∧
    checkAtR Fmt.oracle (recordBytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
      w.table w.ent = some w.further ∧
    EntryTiedR (linkAtCfg Params.recordRead (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
      Params.recordRounds w.table w.further w.ent

/-- **FROM THE ENTRY FUNCTION. If `main args` returns 0, some values w meet `ZeroFacts`; and IF THE
PARAMETER FILE AS READ MEETS `SaysRecordLines` (one equation, proved of no file), then `RecordTiedAt
w`.** The exit code 0 covers both `YES` and `WITHIN LIMITS`. The first table's answers are
`Key.check`'s word. Nothing on soundness; no probability; the Lean port, not cp_verify; the entry
file's chain alone. -/
theorem main_zero_saysRecordLines {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ w, ZeroFacts args s s' w ∧ (SaysRecordLines w.r.pol → RecordTiedAt w) := by
  obtain ⟨w, hw⟩ := main_zero_facts h
  refine ⟨w, hw, fun hs => ?_⟩
  have eb := zero_entry_bytes hw (saysRecordLines_bytes hs w.lay w.r.KL)
  have hy : Entry.check (recordBytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
      w.table w.ent = .ok w.further := by
    rw [← eb]
    exact hw.entryYes
  obtain ⟨h32, h1, h2⟩ := entry_record_atCfg _ (Params.configurationDigest_size _) w.table
    w.further w.ent hy (zero_table_root hw) (zero_entry_small hw)
  exact ⟨eb, zero_table_root hw, h32, h1, h2⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.withinX_record_at
#print axioms OnBytes.Tie.entry_record_atCfg
#print axioms OnBytes.Tie.saysRecordLines_bytes
#print axioms OnBytes.Tie.main_zero_saysRecordLines
