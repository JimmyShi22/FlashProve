-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ZeroAt.lean: from the facts on the exit code 0 of the entry function to what
`Entry.read` returned on the entry file.

OnBytes/Tie/ZeroFacts.lean gathers the clauses on the exit code 0. OnBytes/Tie/EntryWith.lean states
`Entry.check` through what `Entry.read` returns. Here the two are joined, for the entry file's chain
alone.


Main definition: `EntryReadTied`.
Main theorems. Each is for every record that meets `ZeroFacts`.
- `zero_entry_read`: `Entry.read` under the entry's chain in p returned an entry r with `further` as
  its further table, and the decision of r's block is true on the view of r's chain.
- `zero_entry_bytes`: if `Params.entryBytesOf` of the three configuration files is a string, that
  string is the parameter bytes of the entry's chain in p.




- `EntryReadTied.triple`: from `EntryReadTied` its clauses on the description, the reader and the
  compiled verifier.




What is not claimed. Nothing on soundness, and no probability: every statement is on one run of the
Lean program at the format's hash. Of a yes of the compiled verifier nothing is proved here.
`EntryReadTied` is a hypothesis of `EntryReadTied.triple`: no theorem of this file gives it.
The equation on `Params.entryBytesOf` is a hypothesis; this file proves it of no string or files.

Nothing is said of the other six chains of a whole call, of the key file or of the proof file
beyond `ZeroFacts`. All limits in the heads of the two files named above hold here too.
(`keyTable_root` is taken from OnBytes/Tie/LeafCall.lean.) The program is the Lean port built from
OnBytes/; nothing here is said of the C++ program `cp_verify` or of how its results compare. For
proofs only; the program does not import this file.

-/
import OnBytes.Tie.ZeroFacts
import OnBytes.Tie.EntryAt
import OnBytes.Tie.LeafCall

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Shell (World fileLimit)

/-- For parameters q, rounds rs, two tables and the bytes of an entry file: `Entry.read` under q,
against `table`, returned some r, with `further` as its further table and `Params.entryBlock q` as
its block; `entrySpec` gives that block and the description made of q, rs and the two tables; the
reader `readIn` reads r's chain under that description, in a session that starts empty, from some
byte offset of the file, which is not named; and the compiled verifier (a term of the library's Lean
theory, not machine code) accepts `r.chain.out` under that description and the two tables' roots. Of
the compiled verifier's yes this says nothing further. -/
def EntryReadTied (q : Params.Link) (rs : Params.Rounds) (table further : Params.TableName)
    (ent : ByteArray) : Prop :=
  ∃ r : Entry.EntryRead,
    Entry.read q table ent = .ok r ∧ r.further = further ∧ r.block = Params.entryBlock q ∧
    entrySpec q table further = some (Params.entryBlock q,
      Params.entrySpecOf q rs (Params.Link.statement table further)) ∧
    (∃ j s2, readIn (Params.entrySpecOf q rs (Params.Link.statement table further)) ent j
      Session.start = some (r.chain, s2)) ∧
    CompiledAcceptsX (Params.entrySpecOf q rs (Params.Link.statement table further))
      (entryStatement table further) ((Params.entryBlock q).decides (Entry.start q))
      table.root further.root r.chain.out

/-- From `EntryReadTied` its clauses on the description, the reader and the compiled verifier. -/
theorem EntryReadTied.triple {q : Params.Link} {rs : Params.Rounds}
    {table further : Params.TableName} {ent : ByteArray}
    (h : EntryReadTied q rs table further ent) :
    ∃ (j : ℕ) (c : ChainRead) (s2 : Session),
      entrySpec q table further = some (Params.entryBlock q,
        Params.entrySpecOf q rs (Params.Link.statement table further)) ∧
      readIn (Params.entrySpecOf q rs (Params.Link.statement table further)) ent j Session.start
        = some (c, s2) ∧
      CompiledAcceptsX (Params.entrySpecOf q rs (Params.Link.statement table further))
        (entryStatement table further) ((Params.entryBlock q).decides (Entry.start q))
        table.root further.root c.out := by
  obtain ⟨r, _, _, _, hS, ⟨j, s2, hrd⟩, hc⟩ := h
  exact ⟨j, r.chain, s2, hS, hrd, hc⟩

/-- Under `ZeroFacts`: the parameter bytes of the entry's chain in p are read as the entry's chain
in p; `Entry.read` under it, against `table`, returned some r on the entry file's bytes; r's further
table is `further`; and the decision of r's block is true on the view of r's chain. -/
theorem zero_entry_read {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) :
    ∃ r : Entry.EntryRead,
      Params.Link.read (w.p.chains.bytes .link) = some w.p.chains.link ∧
      Entry.read w.p.chains.link w.table w.ent = .ok r ∧ r.further = w.further ∧
      r.block.decides (Entry.start w.p.chains.link) r.chain.view = true := by
  obtain ⟨q, r, hq, hr, hf, hd⟩ := (entry_check_iff _ _ _ _).1 h.entryYes
  have e : q = w.p.chains.link := Option.some.inj (hq.symm.trans h.same.2.2)
  subst e
  exact ⟨r, hq, hr, hf, hd⟩

/-- Under `ZeroFacts` the root of `table` has 32 bytes. -/
theorem zero_table_root {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) : w.table.root.size = 32 := by
  obtain ⟨j, hj⟩ := Model.Verify.keyCheck_table h.keyYes
  exact keyTable_root hj

/-- Under `ZeroFacts` the entry file meets the bound on its size that `entry_closedR` asks for. -/
theorem zero_entry_small {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) : w.ent.size + 16 ≤ 2 ^ 32 - 144 := by
  have := h.entSize
  unfold fileLimit at this
  omega

/-- Under `ZeroFacts`, if `Params.entryBytesOf` of the three configuration files' bytes is `bytes`,
then `bytes` is the parameter bytes of the entry's chain in p, under which `Entry.check` ran. -/
theorem zero_entry_bytes {args : List String} {s s' : World} {w : WholeSeen}
    (h : ZeroFacts args s s' w) {bytes : ByteArray}
    (hb : Params.entryBytesOf w.r.pol w.lay w.r.KL = some bytes) :
    w.p.chains.bytes .link = bytes :=
  Option.some.inj ((Model.Verify.planned_entryBytes h.planned).symm.trans hb)

end OnBytes.Tie
