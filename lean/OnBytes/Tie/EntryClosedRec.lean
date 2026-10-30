-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryClosedRec.lean: from a yes of `Entry.check` to a yes of the compiled verifier, at
any parameter bytes (`entry_closedR`).

It holds under three facts (the bytes are read as q; the dry run at keys of zeros gives rs; the
description is within the library's limits wherever its base is in order) and a digest of 32 bytes.
`entry_record` (OnBytes/Tie/EntryRecord.lean) is its instance at the typed bytes.

-/
import OnBytes.Tie.EntryAtRec
import OnBytes.Tie.SpecXBase
import OnBytes.Params.EntryDescRecord

set_option autoImplicit false

namespace OnBytes.Tie

/-- What is concluded of parameters q, rounds rs, a first table, a further table and an entry file's
bytes. r is what `Entry.read` returned; k0, k1 are the two tables' keys as the program's `tableKey`
makes them. NOT THE DECISION ALONE HANGS ON THE TABLES: the description (its
statement) and the statement function hold both tables' answers too. ALL OF further IS READ FROM THE
ENTRY FILE: THE PROTOCOL IS PICKED AFTER THE FILE's AUTHOR HAS SPOKEN; the compiled verifier's key
is the two roots alone. An entry RECORD of the plan is no round of that protocol: what the planner
reckons for the record's sample has no place in it. `CompiledAcceptsX` follows for every decision
that is true on the view: it mirrors the hash chain and the trees, no more. In that clause the seeds
are the program's, computed outside that verifier. The reading at the format's own oracle returns
the same r: the very chain. -/
def EntryTiedR (q : Params.Link) (rs : Params.Rounds) (first further : Params.TableName)
    (file : ByteArray) : Prop :=
  ∃ (r : Entry.EntryRead) (k0 k1 : TableKey),
    Entry.read q first file = .ok r ∧ r.further = further ∧
    readWithR (readerAt Fmt.oracle) (seedsAt Fmt.oracle) q first file = some r ∧
    r.block = linkVerify q.link k0 k1 ∧
    tableKey q.given.plan.field q.given.cfg q.link.table first 0 = some k0 ∧
    tableKey q.given.plan.field q.given.cfg q.link.table further 1 = some k1 ∧
    entrySpec q first further = some (linkVerify q.link k0 k1,
      Params.entrySpecOf q rs (Params.Link.statement first further)) ∧
    (∃ j s2, readIn (Params.entrySpecOf q rs (Params.Link.statement first further)) file j
      Session.start = some (r.chain, s2)) ∧
    entryDecR q k0 k1 r.chain.view = true ∧
    CompiledAcceptsX (Params.entrySpecOf q rs (Params.Link.statement first further))
      (entryStatement first further) (entryDecR q k0 k1) first.root further.root r.chain.out

/-- **UNDER: the parameter bytes are read as q; the dry run at keys of
zeros gives rs; the description at q, rs is within the limits at every statement at which its base
is in order; q's digest and the first root have 32 bytes; the file is below about 2^32 bytes.** If
the program's check says yes and returns `further`: its root has 32 bytes; the check at a function
in the place of the hash (the reader but for one pinned string) says yes at the format's own oracle;
and `EntryTiedR`. (The clause on `checkAtR` holds both ways: `entry_check_atR`.) OF `checkAtR` AT A
FUNCTION OTHER THAN THE FORMAT's OWN ORACLE NOTHING IS PROVED; NO BOUND IS STATED OF IT. -/
theorem entry_closedR (params : ByteArray) (q : Params.Link) (rs : Params.Rounds)
    (hq : Params.Link.read params = some q) (hrs : Params.entryRoundsAny q = some rs)
    (hw : ∀ st, (Params.entrySpecOf q rs st).base.ok = true →
      withinX (Params.entrySpecOf q rs st) = true)
    (hc : q.given.cfg.size = 32)
    (first further : Params.TableName) (file : ByteArray)
    (h : Entry.check params first file = .ok further) (h0 : first.root.size = 32)
    (hb : file.size + 16 ≤ 2 ^ 32 - 144) :
    further.root.size = 32 ∧ checkAtR Fmt.oracle params first file = some further ∧
      EntryTiedR q rs first further file := by
  obtain ⟨q', r, hq', hr, e1, hd⟩ := (entry_check_iff _ first further file).1 h
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  obtain ⟨j, S, s', hS, hrd, h32⟩ := entry_read_spec _ first file r hr
  obtain ⟨S', hS', himp⟩ := entry_read_compiled _ first file r hr hd
  obtain rfl : S = S' := congrArg (·.2) (Option.some.inj (hS.symm.trans hS'))
  obtain ⟨⟨k0, k1, a0, a1, a2⟩, rs', hrs', eS⟩ := Params.entrySpec_eq_all hS
  obtain rfl : rs = rs' := Option.some.inj (hrs.symm.trans hrs')
  have hok := readX_ok Fmt.formatHash _ _ file j _ (readIn_read _ file j _ s' r.chain hrd).1
  subst e1
  rw [eS] at hok himp hS hrd
  have hwi := hw _ (specX_base _ hok)
  have hcx := himp hwi (smallFX_of_withinX _ hok hwi file hb) h0
  rw [a2] at hd hcx hS
  have hsm : ∀ P, entryPlaceR recordSeeds q first file = some P → P.spec.ok = true →
      smallFX P.spec file = true := by
    intro P hP hokP
    obtain ⟨_, ⟨rs2, h2, eP⟩, _⟩ := entryPlaceR_spec_any hP
    obtain rfl : rs = rs2 := Option.some.inj (hrs.symm.trans h2)
    rw [eP] at hokP ⊢
    exact smallFX_of_withinX _ hokP (hw _ (specX_base _ hokP)) file hb
  exact ⟨h32, (entry_check_atR params q first r.further file hq hc h0 hsm).2 h, r, k0, k1, hr, rfl,
    (readWithR_oracle hc h0 hsm r).2 hr, a2, a0, a1, hS, ⟨j, s', hrd⟩, hd, hcx⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.entry_closedR
