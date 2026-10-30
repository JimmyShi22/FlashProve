-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryGround.lean: OnBytes/Tie/ZeroRecordLines.lean said once, over one record of typed
facts (`EntryGround`).

No number of a model's size stands in this file (32, 16 and 2 ^ 32 - 144, the format's own, do). Its
instances, at the full size and at one small example, are in OnBytes/Tie/EntryGrounds.lean.

Not claimed. Nothing on soundness; no probability; the Lean port; the entry file's chain alone.

-/
import OnBytes.Tie.ZeroRecordLines

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (World)

/-- **What the entry's link asks of a setting, as one record**: the parameter file's lines; what the
entry's parameter bytes hold, at some digest; the rounds of the dry run at keys of zeros; and six
facts. -/
structure EntryGround where
  /-- the lines of the parameter file -/
  lines : Params.Lines
  /-- what the entry's parameter bytes hold as those of a link's chain, at some digest -/
  q : Params.Link
  /-- the rounds of the dry run -/
  rs : Params.Rounds
  /-- q's parameter bytes are spelled from its plan, digest and items -/
  spelled : q.given.bytes = Fmt.paramsBytes q.given.plan q.given.cfg q.given.items
  /-- q's digest has 32 bytes -/
  cfg32 : q.given.cfg.size = 32
  /-- at these lines and every digest c, the entry's parameter bytes are spelled from q's plan, c
  and q's items -/
  params_at : ∀ c, Params.entryParams lines c =
    .ok (Fmt.paramsBytes q.given.plan c q.given.items)
  /-- for c of 32 bytes these bytes are read as q at c -/
  read_at : ∀ c : ByteArray, c.size = 32 →
    Params.Link.read (Fmt.paramsBytes q.given.plan c q.given.items) = some (linkAtCfg q c)
  /-- the dry run at keys of zeros gives rs -/
  rounds : Params.entryRoundsAny q = some rs
  /-- the description is within the library's limits at every statement at which its base is in
  order -/
  within : ∀ st, (Params.entrySpecOf q rs st).base.ok = true →
    withinX (Params.entrySpecOf q rs st) = true

namespace EntryGround
variable (G : EntryGround)

/-- The entry's parameter bytes at a digest c. -/
def bytesAt (c : ByteArray) : ByteArray := Fmt.paramsBytes G.q.given.plan c G.q.given.items

/-- For every c of 32 bytes the description at c is within the limits wherever its base is in order.
-/
theorem within_at (c : ByteArray) (hc : c.size = 32) (st : ByteArray)
    (hb : (Params.entrySpecOf (linkAtCfg G.q c) G.rs st).base.ok = true) :
    withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs st) = true := by
  rw [withinX_linkAtCfg G.q c G.rs st (hc.trans G.cfg32.symm) G.spelled]
  refine G.within st ?_
  rw [← baseOk_linkAtCfg G.q c G.rs st (hc.trans G.cfg32.symm) G.spelled]
  exact hb

/-- At every digest the dry run gives rs. -/
theorem rounds_at (c : ByteArray) : Params.entryRoundsAny (linkAtCfg G.q c) = some G.rs :=
  (entryRoundsAny_linkAtCfg G.q c).trans G.rounds

/-- **At the bytes at any digest c of 32 bytes, a first root of 32 bytes, a file below about 2^32
bytes: no other hypothesis:** `entry_closedR`'s three conclusions. "Nothing assumed" means here: not
the statement on codes; the hypotheses that stand in the statement itself are assumed. -/
theorem entry_at (c : ByteArray) (hc : c.size = 32) (first further : Params.TableName)
    (file : ByteArray) (h : Entry.check (G.bytesAt c) first file = .ok further)
    (h0 : first.root.size = 32) (hb : file.size + 16 ≤ 2 ^ 32 - 144) :
    further.root.size = 32 ∧ checkAtR Fmt.oracle (G.bytesAt c) first file = some further ∧
      EntryTiedR (linkAtCfg G.q c) G.rs first further file :=
  entry_closedR (G.bytesAt c) (linkAtCfg G.q c) G.rs (G.read_at c hc) (G.rounds_at c)
    (G.within_at c hc) hc first further file h h0 hb

/-- ONE EQUATION ON THE PARAMETER FILE: the lines that `Params.readLines` reads from it are the
ground's. PROVED OF NO FILE. (OnBytes/K/Left/TestSaysLines.lean and SaysLinesPrefix.lean prove it of
every byte string that begins with copies of 32 lines, which stand there.) That these are a
release's default lines is not stated. Of what else the parameter file holds, of the layout file and
of the scale file nothing is asked: they enter through the digest alone. -/
def SaysLines (pol : ByteArray) : Prop :=
  (Params.readLines pol).toOption.map (·.1) = some G.lines

/-- For such a parameter file, and any two other files, the parameter bytes of an entry's chain are
the ground's at the three files' digest. -/
theorem saysLines_bytes {pol : ByteArray} (h : G.SaysLines pol) (lay kl : ByteArray) :
    Params.entryBytesOf pol lay kl =
      some (G.bytesAt (Params.configurationDigest [pol, lay, kl])) := by
  unfold Params.entryBytesOf
  cases hx : (Params.readLines pol).toOption with
  | none =>
    unfold SaysLines at h
    rw [hx] at h
    cases h
  | some x =>
    unfold SaysLines at h
    rw [hx] at h
    have e : x.1 = G.lines := Option.some.inj h
    show (Params.entryParams x.1 (Params.configurationDigest [pol, lay, kl])).toOption = _
    rw [e, G.params_at]
    rfl

/-- What is concluded of values w, at c := the digest of the three configuration files as read.
Nothing on soundness; no probability. At the format's own oracle the clause on checkAtR is
equivalent to the program's yes (`entry_check_atR`). Of checkAtR at another function nothing is
proved; no bound is stated of it. The digest is BLAKE2b's, whatever function stands in the place of
the hash. -/
def TiedAt (w : WholeSeen) : Prop :=
  w.p.chains.bytes .link = G.bytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]) ∧
    w.p.chains.tableShape = G.q.link.table ∧
    w.table.root.size = 32 ∧ w.further.root.size = 32 ∧
    checkAtR Fmt.oracle (G.bytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
      w.table w.ent = some w.further ∧
    EntryTiedR (linkAtCfg G.q (Params.configurationDigest [w.r.pol, w.lay, w.r.KL])) G.rs
      w.table w.further w.ent

/-- Under `ZeroFacts` and `SaysLines`: `TiedAt`. -/
theorem zero_tied {args : List String} {s s' : World} {w : WholeSeen}
    (hw : ZeroFacts args s s' w) (hs : G.SaysLines w.r.pol) : G.TiedAt w := by
  have hc32 := Params.configurationDigest_size [w.r.pol, w.lay, w.r.KL]
  have eb := zero_entry_bytes hw (G.saysLines_bytes hs w.lay w.r.KL)
  have hy : Entry.check (G.bytesAt (Params.configurationDigest [w.r.pol, w.lay, w.r.KL]))
      w.table w.ent = .ok w.further := by
    rw [← eb]
    exact hw.entryYes
  have hsh : w.p.chains.tableShape = G.q.link.table := by
    have e1 := hw.same.2.2
    rw [eb] at e1
    have e2 := (G.read_at _ hc32).symm.trans e1
    rw [tableShape_oneTime, hw.same.2.1.1, ← Option.some.inj e2]
    rfl
  obtain ⟨h32, h1, h2⟩ := G.entry_at _ hc32 w.table w.further w.ent hy (zero_table_root hw)
    (zero_entry_small hw)
  exact ⟨eb, hsh, zero_table_root hw, h32, h1, h2⟩

/-- **FROM THE ENTRY FUNCTION, AT ANY GROUND. If `main args` returns 0, some values w meet
`ZeroFacts`; and IF THE PARAMETER FILE AS READ MEETS `SaysLines` (one equation, proved of no file),
then `TiedAt w`.** The exit code 0 covers both `YES` and `WITHIN LIMITS`. The first table's answers
are `Key.check`'s word. Nothing on soundness; no probability; the Lean port, not cp_verify; the
entry file's chain alone. -/
theorem main_zero_saysLines {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ w, ZeroFacts args s s' w ∧ (G.SaysLines w.r.pol → G.TiedAt w) := by
  obtain ⟨w, hw⟩ := main_zero_facts h
  exact ⟨w, hw, G.zero_tied hw⟩

end EntryGround

end OnBytes.Tie

#print axioms OnBytes.Tie.EntryGround.entry_at
#print axioms OnBytes.Tie.EntryGround.zero_tied
#print axioms OnBytes.Tie.EntryGround.main_zero_saysLines
