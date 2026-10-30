-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Conv.lean: where the exit code 0 holds of eight files' bytes, the bytes' side of a
run on an entry file (`prepE`, OnBytes/TypedOracleCompiler/Slice/EntryRunBytes.lean) returns a value, and that value
is made of what the program itself read and drew.

`prepE` tests the three public files (`Params.stdEntry`), reads the first table off the key file's
head by a plain function (`Tie.keyAt`), and hands it with the entry file to the strict converter
`convE`: the program's own `Entry.read`, and the program's own seeds (`recordSeeds`) at both tables'
names.

Main names:
  `link_at`: under `PortYesAt` and `G.SaysLines`, the entry's chain in the planner's value is G's
    parameters with the three public files' digest in the digest's place.
  `table_at`: `Tie.keyAt` returns the table that `Key.check` returned.
  `read_at`: what `Entry.read` returned on the entry file, and the program's seeds at both tables'
    names; the program's block is `linkVerify` at keys made of the tables' answers and these seeds,
    and its decision on the view of what was read says yes.
  `conv`: `prepE` returns the digest, these parameters, the two tables that the program threads,
    these seeds, and what `Entry.read` read of the chain.

Hypotheses: `PortYesAt`; `G.SaysLines F.pol`; the ground's tables have a record (a test on G,
decided at both grounds: `record_answers`, `small_record_answers`); and that `Params.stdEntry` says
yes (OnBytes/K/Left/Std.lean shows it).

Limits: values alone. Nothing on soundness; no probability. That some files meet `PortYesAt` is not
shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Entry
import OnBytes.TypedOracleCompiler.Slice.EntryRunBytes

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie
open TypedOracleCompiler.Slice

/-- The full-size ground's tables have a record. -/
theorem record_answers : (recordGround.q.link.table.answers == 0) = false := by decide +kernel

/-- The small ground's tables have a record. -/
theorem small_record_answers : (smallRecordGround.q.link.table.answers == 0) = false := by
  decide +kernel

/-- Under `PortYesAt` and `G.SaysLines`: the parameter bytes of the entry's chain in the planner's
value are G's at the three public files' digest, and the chain as read back is G's parameters at
that digest. -/
theorem link_at (G : EntryGround) {F : Files} {p : Model.Verify.Planned}
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p)
    (hs : SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]))
    (hl : G.SaysLines F.pol) :
    p.chains.bytes .link = G.bytesAt (Params.configurationDigest [F.pol, F.lay, F.KL]) ∧
      p.chains.link = linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]) := by
  have eb : p.chains.bytes .link = G.bytesAt (Params.configurationDigest [F.pol, F.lay, F.KL]) :=
    Option.some.inj ((Model.Verify.planned_entryBytes hp).symm.trans
      (G.saysLines_bytes hl F.lay F.KL))
  have h2 := hs.2.2
  rw [eb] at h2
  exact ⟨eb, Option.some.inj (h2.symm.trans (G.read_at _ (Params.configurationDigest_size _)))⟩

/-- The plain reader of the key file's head returns the table that `Key.check` returned. -/
theorem table_at (G : EntryGround) {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) (c : ByteArray) :
    (keyAt G.q.link.table c F.key).2.2 = table := by
  obtain ⟨p, hp, hk, -, hs, -, -⟩ := entry_facts h
  have ht := keyCheck_tableAt hk
  rw [hs.2.1.1, (link_at G hp hs hl).2] at ht
  have ht' : tableAt G.q.link.table F.key = some table := ht
  unfold keyAt
  rw [ht']
  rfl

/-- What the program read of the entry file and drew for the two tables. At q := G's parameters
at the three public files' digest: `Entry.read` returned r, whose further table is `further`; the
program's seeds at both tables' names are l0 and l1; r's block is `linkVerify` at keys made of the
tables' answers and these seeds; and its decision on the view of what was read says yes. -/
theorem read_at (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E)),
      Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
        .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        further = some l1 ∧
      r.block = linkVerify G.q.link
        { item := 0, record := table.answers.toArray, seeds := l0.map fun x => ⟨x.1, x.2⟩ }
        { item := 1, record := further.answers.toArray, seeds := l1.map fun x => ⟨x.1, x.2⟩ } ∧
      r.block.decides
        (Entry.start (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])))
        r.chain.view = true := by
  obtain ⟨p, hp, -, he, hs, -, -⟩ := entry_facts h
  rw [(link_at G hp hs hl).1] at he
  obtain ⟨q', r, hq', hr, hf, hd⟩ := (entry_check_iff _ _ _ _).1 he
  obtain rfl : linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]) = q' :=
    Option.some.inj ((G.read_at _ (Params.configurationDigest_size _)).symm.trans hq')
  have hr' : readWithR readIn recordSeeds
      (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent = some r := by
    rw [readWithR_readIn, hr]
    rfl
  obtain ⟨P, hP, _, _, hPf, hPb⟩ := (readWithR_iff _ _ _ _ _ _).1 hr'
  obtain ⟨⟨k0, k1, hk0, hk1, hb⟩, _, _⟩ := entryPlaceR_spec_any hP
  obtain ⟨l0, hl0, rfl⟩ := keyWith_seeds hk0 hA
  obtain ⟨l1, hl1, rfl⟩ := keyWith_seeds hk1 hA
  rw [← hPf, hf] at hl1 hb
  -- by the named equation, not by unfolding: see `Tie.seedsUnder_eq`
  exact ⟨r, l0, l1, hr, hf, (seedsUnder_eq _ _ _).trans hl0, (seedsUnder_eq _ _ _).trans hl1,
    hPb.trans hb, hd⟩

/-- The bytes' side of a run returns what the program read and drew: `read_at`'s r, l0, l1. -/
theorem conv (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false) (z : Params.StdSize)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol)
    (hstd : Params.stdEntry z ⟨F.pol, F.lay, F.KL⟩ = true) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E)),
      Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
        .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        further = some l1 ∧
      r.block = linkVerify G.q.link
        { item := 0, record := table.answers.toArray, seeds := l0.map fun x => ⟨x.1, x.2⟩ }
        { item := 1, record := further.answers.toArray, seeds := l1.map fun x => ⟨x.1, x.2⟩ } ∧
      r.block.decides
        (Entry.start (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])))
        r.chain.view = true ∧
      prepE G z false F.pol F.lay F.KL F.key F.ent =
        .ok ⟨Params.configurationDigest [F.pol, F.lay, F.KL], Params.configurationDigest_size _,
          linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]),
          ⟨table, further, l0, l1, r.chain.out⟩⟩ := by
  have htab := table_at G h hl (Params.configurationDigest [F.pol, F.lay, F.KL])
  obtain ⟨r, l0, l1, hr, hf, a0, a1, hb, hd⟩ := read_at G hA h hl
  refine ⟨r, l0, l1, hr, hf, a0, a1, hb, hd, ?_⟩
  unfold prepE
  rw [if_pos hstd, htab]
  simp only [Bool.false_eq_true, if_false, convE, hr, hf, a0, a1, Option.bind_some, Option.map_some]

end OnBytes.K.Left
