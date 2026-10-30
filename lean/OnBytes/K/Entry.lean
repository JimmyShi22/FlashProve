-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Entry.lean: the entry file's chain: where the program's exit
code 0 holds of eight files' bytes (`PortYesAt`, OnBytes/K/Top.lean), the library's compiled
verifier of one slot says yes on the typed string that the library's typing makes of what
`Entry.read` read of the entry file. For proofs only; the program does not import this file.

The compiled verifier here is the one of the protocol that the library makes from the program's own
description of the entry's chain and from the program's own decision on it
(`CompiledAcceptsX`, OnBytes/Tie/StoredMain.lean; `EntryTiedR`, OnBytes/Tie/EntryClosedRec.lean). So
this is a tie of reading: what the program hashes, climbs and draws is what that verifier asks. The
decision rides along unopened.

Main definitions.
  EntryLimits q rs   the description of the entry's chain at q and rs is within the library's limits
                     wherever its base is in order, whatever the statement.
Main theorems.
  entry_tied         `PortYesAt` at the two tables: the planner's value p is named, and for all
                     rounds rs that the dry run at keys of zeros gives, under
                     `EntryLimits`: `EntryTiedR`. TWO NAMED HYPOTHESES: the dry run's answer, the
                     limits. No hypothesis on the tables' answers.
  entry_tied_at      the same over a record G of typed facts on a setting (`EntryGround`,
                     OnBytes/Tie/EntryGround.lean): NO HYPOTHESIS BUT ONE EQUATION ON THE PARAMETER
                     FILE: its first 32 lines as read are G's (`G.SaysLines`).
  entry_tied_full, entry_tied_small   that at the two grounds of OnBytes/Tie/EntryGrounds.lean: the
                     full size and a small example, each under the Johnson rule, with proof of work.


Not claimed. Nothing on soundness; no probability. Nothing on the key file's or the proof file's
chains. Nothing on what the decision means. That some files meet `PortYesAt` is not shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Top
import OnBytes.Tie.EntryGrounds

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Tie
open OnBytes.Shell (fileLimit)

/-- The description of the entry's chain at q and rs is within the library's limits wherever its
base is in order, whatever the statement. -/
def EntryLimits (q : Params.Link) (rs : Params.Rounds) : Prop :=
  ∀ st, (Params.entrySpecOf q rs st).base.ok = true →
    withinX (Params.entrySpecOf q rs st) = true

/-- What `PortYesAt` says of the entry file, by name: the planner's value, the two checks' yes, that
the entry's chain in p is read from the bytes that `Entry.check` is given, that it holds the digest
of the three public files, and the two bounds that the tie asks for. -/
theorem entry_facts {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) :
    ∃ p : Model.Verify.Planned,
      Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Key.check p.chains.key F.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table F.ent = .ok further ∧
      Tie.SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]) ∧
      table.root.size = 32 ∧ F.ent.size + 16 ≤ 2 ^ 32 - 144 := by
  obtain ⟨r, p, C, -, -, -, -, -, -, -, -, -, hes, hp, -, -, hk, he, -, -, hs, -⟩ := h
  obtain ⟨j, hj⟩ := Model.Verify.keyCheck_table hk
  refine ⟨p, hp, hk, he, hs, keyTable_root hj, ?_⟩
  unfold fileLimit at hes
  omega

/-- The entry's chain. Where `PortYesAt` holds: for all rounds rs that
the dry run at keys of zeros gives for the entry's chain in p, and under `EntryLimits`, the further
table's root has 32 bytes and `EntryTiedR` holds: `Entry.read` returned r on the entry file's bytes,
and the compiled verifier says yes on what the library's typing makes of r's own chain, under the
two tables' roots, at the program's own decision. -/
theorem entry_tied {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) :
    ∃ p : Model.Verify.Planned,
      Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      ∀ rs, Params.entryRoundsAny p.chains.link = some rs → EntryLimits p.chains.link rs →
        further.root.size = 32 ∧ EntryTiedR p.chains.link rs table further F.ent := by
  obtain ⟨p, hp, -, he, hs, h0, hb⟩ := entry_facts h
  refine ⟨p, hp, fun rs hrs hw => ?_⟩
  have hc32 : p.chains.link.given.cfg.size = 32 := by
    rw [hs.1.2.2.2.2.1]
    exact Params.configurationDigest_size _
  obtain ⟨a, -, c⟩ := entry_closedR (p.chains.bytes .link) p.chains.link rs hs.2.2 hrs hw hc32
    table further F.ent he h0 hb
  exact ⟨a, c⟩

/-- The entry's chain at a setting whose typed facts are G. Where `PortYesAt` holds and the
parameter file's first 32 lines as read are G's: the further table's root has 32 bytes, and
`EntryTiedR` holds at G's typed parameters, with the three public files' digest in the digest's
place, and at G's typed rounds. No other hypothesis. -/
theorem entry_tied_at (G : EntryGround) {F : Files} {id : String}
    {table further : Params.TableName} (h : PortYesAt F id table further)
    (hl : G.SaysLines F.pol) :
    further.root.size = 32 ∧
      EntryTiedR (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) G.rs table
        further F.ent := by
  obtain ⟨p, hp, -, he, -, h0, hb⟩ := entry_facts h
  have eb : p.chains.bytes .link = G.bytesAt (Params.configurationDigest [F.pol, F.lay, F.KL]) :=
    Option.some.inj ((Model.Verify.planned_entryBytes hp).symm.trans
      (G.saysLines_bytes hl F.lay F.KL))
  rw [eb] at he
  obtain ⟨a, -, c⟩ := G.entry_at _ (Params.configurationDigest_size _) table further F.ent he h0 hb
  exact ⟨a, c⟩

/-- `entry_tied_at` at the full size: the Johnson rule, proof of work, a record. -/
theorem entry_tied_full {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : recordGround.SaysLines F.pol) :
    further.root.size = 32 ∧
      EntryTiedR (linkAtCfg Params.recordRead (Params.configurationDigest [F.pol, F.lay, F.KL]))
        Params.recordRounds table further F.ent :=
  entry_tied_at recordGround h hl

/-- `entry_tied_at` at the small example: the Johnson rule, proof of work, a record. -/
theorem entry_tied_small {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : smallRecordGround.SaysLines F.pol) :
    further.root.size = 32 ∧
      EntryTiedR
        (linkAtCfg Params.smallRecordRead (Params.configurationDigest [F.pol, F.lay, F.KL]))
        Params.smallRecordRounds table further F.ent :=
  entry_tied_at smallRecordGround h hl

end OnBytes.K
