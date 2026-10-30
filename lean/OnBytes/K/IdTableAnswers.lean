-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/IdTableAnswers.lean: what the Lean program's own readers have tested of the answers
in a table that they return: their number is the shape's, and every answer's three words are below
the prime. So the list of answers comes back from the typed answers that are read off it.

Statements and proofs. The conclusions name no hash. The premises are the program's own checks,
which hash by Lean's BLAKE2b; no property of the hash is used.

"The program" is the Lean port built from OnBytes/. A key file and an entry file each hold a table:
a root and the answers of its record. Both are read by `readTable` (OnBytes/Entry/Table.lean).

Main names:
  `answers_of_readTable`: a table that `readTable f count` returns has `count` answers, each with
    its three words below the prime of f.
  `answers_of_keyCheck`: a table that `Key.check k` returns has 2 ^ v * s answers, at the numbers v
    and s of the tables' shape in the key's one-time chain, each within `okE`.
  `answers_of_entryCheck`: a table that `Entry.check params first` returns: the same at the shape in
    the link's parameters, which are read off `params`.
  `port_answers`: at a yes of the program (`PortYesAt`, OnBytes/K/Top.lean) both hold, of both
    tables at ONE shape, the planner's tables' shape: by the clause `SameChains` of `PortYesAt`
    (OnBytes/Tie/SameChains.lean).
  `port_spell_first`, `port_spell_further`: so `spellAns` (OnBytes/K/IdTableSpell.lean) of the
    answers read off the table's triples of words is the table's own list.

Limits: the two last theorems speak of the function that reads entry r * s + i of the table's
triples of words by `toE`, 0 beyond the end, at the plan's own numbers v and s. That a given
reading of tables as records has this function for its answers, and that its type of answers is
`(Fin v → Bool) × Fin s → GE` at these numbers, is not shown here. `PortYesAt` is taken apart by the
position of its clauses. That some files meet `PortYesAt` is not shown. Nothing on a root, on the
bound on a code's length, on seeds, or on soundness. For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.IdTableSpell
import OnBytes.K.Top
import OnBytes.Tie.SameChains
import Fmt.Rules1Only

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.IdTable
open OnBytes OnBytes.Slice OnBytes.Tie Cb

/-- A table that `readTable` returns: the number of its answers; their words. -/
theorem answers_of_readTable (f : Fmt.Fld) (count : ℕ) (b : ByteArray) (i : ℕ)
    (t : Params.TableName) (j : ℕ) (h : readTable f count b i = .ok (t, j)) :
    t.answers.length = count ∧ ∀ x ∈ t.answers, f.okE x.triple = true := by
  unfold readTable at h
  split at h
  · cases h
  · rename_i root k hd
    split at h
    · cases h
    · rename_i ys m hm
      injection h with h'
      have ht : t = ⟨root, ys.map E.ofTriple⟩ := (congrArg (·.1) h').symm
      rw [rdManyT_eq] at hm
      obtain ⟨_, _, hk, _⟩ := Fmt.only_digest b i root k hd
      obtain ⟨h1, h2, _⟩ := Fmt.only_many (Fmt.only_ext f) count b k ys m hk hm
      subst ht
      refine ⟨by rw [List.length_map]; exact h1, fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨a1, a2, a3⟩ := h2 y hy
      rw [E.triple_ofTriple]
      unfold Fmt.Fld.okE Fmt.Fld.ok
      rw [decide_eq_true a1, decide_eq_true a2, decide_eq_true a3]
      rfl

/-- A table that the key file's reader returns. -/
theorem answers_of_keyReadTable (s : Params.IndexShape) (cfg file : ByteArray)
    (t : Params.TableName) (j : ℕ) (h : Key.readTable s cfg file = .ok (t, j)) :
    t.answers.length = 2 ^ s.v * s.answers ∧ ∀ x ∈ t.answers, okE x = true := by
  unfold Key.readTable at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i i _
      split at h
      · cases h
      · rename_i table m hm
        split at h
        · injection h with h'
          obtain rfl : table = t := congrArg (·.1) h'
          obtain ⟨h1, h2⟩ := answers_of_readTable .two _ file i table m hm
          exact ⟨h1, fun x hx => by rw [okE_triple]; exact h2 x hx⟩
        · cases h

/-- A table that the check of a key file returns. -/
theorem answers_of_keyCheck (k : Params.KeyChains) (file : ByteArray) (t : Params.TableName)
    (h : Key.check k file = .ok t) :
    t.answers.length = 2 ^ k.oneTime.lin.fold.index.v * k.oneTime.lin.fold.index.answers ∧
      ∀ x ∈ t.answers, okE x = true := by
  unfold Key.check at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i table j hr
        split at h
        · cases h
        · split at h
          · cases h
          · injection h with h'
            subst h'
            exact answers_of_keyReadTable _ _ file table j hr

/-- The further table that the reader of an entry file returns. -/
theorem answers_of_entryRead (p : Params.Link) (first : Params.TableName) (file : ByteArray)
    (r : Entry.EntryRead) (h : Entry.read p first file = .ok r) :
    r.further.answers.length = 2 ^ p.link.table.v * p.link.table.answers ∧
      ∀ x ∈ r.further.answers, okE x = true := by
  unfold Entry.read at h
  dsimp only at h
  split at h
  · cases h
  · rename_i i _
    split at h
    · cases h
    · rename_i hf
      split at h
      · cases h
      · rename_i further j hr
        have hf2 : p.given.plan.field = .two := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hf
          exact hf.1
        obtain ⟨h1, h2⟩ := answers_of_readTable _ _ file i further j hr
        have key : further.answers.length = 2 ^ p.link.table.v * p.link.table.answers ∧
            ∀ x ∈ further.answers, okE x = true :=
          ⟨h1, fun x hx => by rw [okE_triple, ← hf2]; exact h2 x hx⟩
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · injection h with h'
                subst h'
                exact key
        · cases h

/-- A table that the check of an entry file returns. -/
theorem answers_of_entryCheck (params : ByteArray) (first : Params.TableName) (file : ByteArray)
    (t : Params.TableName) (h : Entry.check params first file = .ok t) :
    ∃ p, Params.Link.read params = some p ∧
      t.answers.length = 2 ^ p.link.table.v * p.link.table.answers ∧
      ∀ x ∈ t.answers, okE x = true := by
  unfold Entry.check at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i r hr
      split at h
      · injection h with h'
        subst h'
        exact ⟨p, hp, answers_of_entryRead p first file r hr⟩
      · cases h

/-- **At a yes of the program**: both tables have the number of answers of the planner's tables'
shape, and every answer's words are below the prime. -/
theorem port_answers {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) :
    ∃ p, Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      (table.answers.length = 2 ^ p.chains.tableShape.v * p.chains.tableShape.answers ∧
        ∀ x ∈ table.answers, okE x = true) ∧
      (further.answers.length = 2 ^ p.chains.tableShape.v * p.chains.tableShape.answers ∧
        ∀ x ∈ further.answers, okE x = true) := by
  obtain ⟨_, p, _, _, _, _, _, _, _, _, _, _, _, hpl, _, _, hk, he, _, _, hsame, _⟩ := h
  refine ⟨p, hpl, answers_of_keyCheck _ _ _ hk, ?_⟩
  obtain ⟨q, hq, h1, h2⟩ := answers_of_entryCheck _ _ _ _ he
  obtain rfl : p.chains.link = q := Option.some.inj (hsame.2.2.symm.trans hq)
  rw [tableShape_oneTime, hsame.2.1.1]
  exact ⟨h1, h2⟩

/-- So the first table's list of answers comes back from the typed answers that are read off its
triples of words, at the shape of whatever plan the planner returns on the three public files. -/
theorem port_spell_first {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) {pl : Model.Verify.Planned}
    (hpl : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl) :
    spellAns pl.chains.tableShape.v pl.chains.tableShape.answers (fun x =>
      toE ((table.answers.map E.triple).getD
        (Sz.rowNo x.1 * pl.chains.tableShape.answers + x.2.val) (0, 0, 0))) = table.answers := by
  obtain ⟨p, hp, ⟨h1, h2⟩, _⟩ := port_answers h
  obtain rfl : p = pl := Except.ok.inj (hp.symm.trans hpl)
  exact spell_triples _ _ _ h1 h2

/-- The same for the further table. -/
theorem port_spell_further {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) {pl : Model.Verify.Planned}
    (hpl : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl) :
    spellAns pl.chains.tableShape.v pl.chains.tableShape.answers (fun x =>
      toE ((further.answers.map E.triple).getD
        (Sz.rowNo x.1 * pl.chains.tableShape.answers + x.2.val) (0, 0, 0))) =
      further.answers := by
  obtain ⟨p, hp, _, h1, h2⟩ := port_answers h
  obtain rfl : p = pl := Except.ok.inj (hp.symm.trans hpl)
  exact spell_triples _ _ _ h1 h2

end OnBytes.K.IdTable
