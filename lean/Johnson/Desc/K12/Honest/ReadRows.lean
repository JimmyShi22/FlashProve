-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadRows.lean: the last step of the reading of the old rows: the found
symbols fit the layout (`Own.rowsSymbols`, Johnson/Desc/Own/Symbols.lean), at a layout of any number
of members, none of them kept, with a fresh mask table. The reading is `Tw.L9.readOld`
(Johnson/Top/H0/Tw/L9/Switch.lean), a step of the code switch as that file writes it. It ends with a
call of `Own.rowsSymbols` and refuses where that call returns nothing; `rows_there` says under which
hypotheses the call returns a value. A definition, statements and proofs, whatever the symbols are:
of the found symbols the hypotheses read only which columns are there and how many symbols each has.
The file depends on no frame for an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean): the only
file that it imports is Johnson/Desc/Own/Symbols.lean.

In the list: the old rows are s, a structure `SingleRows` (OnBytes/Iop/Fold.lean) with a number of
mask rows (`s.masks`), a number of kept rows (`s.keptRows`) and a layout L. A layout
(`GroupLayout`, OnBytes/Iop/Ground.lean) lists its members, which are numbers of oracle messages,
and for each member whether it is kept (`kept`) and the first row of its main rows and of its mask
rows (`mainFirst`, `maskFirst`). A column (`Column`, same file) has the main symbols and the mask
symbols of one oracle message at one position. The found symbols are `opened`: entry number w is the
list of columns of member number w, and the entry after the last member's is the fresh table's
(`fresh` in `Own.rowsAt`). n is the number of positions. The two tables are the fields `main` and
`mask` of `Own.Tables`; `Own.rowsAt` begins with 2 ^ L.k zeros in the first and 2 ^ L.h zeros in the
second.

  `rows_there`: the rows' own numbers pass their test · two mask rows, no kept row · `ColsFit`
    ⟹ the rows' symbols are made. That is: `Own.rowsSymbols s opened n` returns a value
  `ColsFit`: what is asked of the found symbols: one list of columns for each member and one for
    the fresh table, each with a column for every position · no member is kept · each member's main
    and mask symbols have a first row in the layout and fit the two tables, or are none · the fresh
    table's columns have as many mask symbols as the mask table has rows. A definition: a structure
    of propositions; its fields, in that order: `col`, `kept`, `main` and `mask`, `fresh`
  `rowsFrom_there`, `rowsAt_there`: under the last three hypotheses of `rows_there`:
    `Own.rowsFrom` returns a value at every list of numbers below n, and `Own.rowsAt` at every
    number below n; both at every array y, to which they append
  `layMembers_there`: under `ColsFit`, at a number i below n, at every list of members' numbers
    and at all tables with 2 ^ L.k entries in `main`, 2 ^ L.h in `mask` and none in `kept`:
    `Own.layMembers` returns tables, again with no entry in `kept`
  `layRows_there`: `Own.layRows` returns a table, of the size of the table that it is given, where
    the column has no symbol, or where a first row f is given and f plus the number of symbols is
    at most the table's size
  `size_layFrom`: `Own.layFrom` returns a table of the size of the table that it is given

By what. The proofs unfold the definitions of Johnson/Desc/Own/Symbols.lean and call no lemma of
another file of this library. `rows_there` passes the test `Own.shapeFits` by hs and calls
`rowsFrom_there` at `List.range n`. That calls `rowsAt_there` at each number of the list.
`rowsAt_there` calls `layMembers_there` at all members and at tables of zeros, then takes the fresh
table's column from `ColsFit.col` and its size from `ColsFit.fresh`. `layMembers_there` calls
`layRows_there` twice for each member, and `layRows_there` calls `size_layFrom`.

Hypotheses of `rows_there`. hs: `Own.shapeFits s` passes: s has L.k challenges, L.h ≤ L.k, and the
layout's lists `kept`, `mainFirst` and `maskFirst` are as long as `members`. h2: `s.masks` is 2.
hk: `s.keptRows` is 0. H: `ColsFit` at the layout of s, `opened` and n.

Limits. Of the reading only its last step: the look-up of the messages' places in the book, the
opening of their trees (Johnson/Desc/K12/Honest/ReadTrees.lean) and the finding of each message's
symbols (Johnson/Desc/K12/Honest/ReadSymbols.lean) are not in this file. `ColsFit` is a hypothesis:
no value that meets it is given in this file; `read_yes_trees`
(Johnson/Desc/K12/Honest/ReadWhole.lean) derives it from its own hypothesis `ReadAsks`. Nothing is
stated where a member is kept, where `s.keptRows` is not 0 or where `s.masks` is not 2. Nothing on
what the symbols are. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.Own.Symbols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc.Own (layFrom layRows layMember layMembers rowsAt rowsFrom rowsSymbols
  shapeFits Tables)

theorem size_layFrom : ∀ (l : List E) (table : Array E) (f : Nat),
    (layFrom table f l).size = table.size
  | [], _, _ => rfl
  | e :: es, table, f => by
    rw [layFrom, size_layFrom es, Array.size_setIfInBounds]

/-- `Own.layRows` returns a table of the same size where the column has no symbol, or where its
symbols have a first row and fit the table. -/
theorem layRows_there (table : Array E) (first : Option Nat) (col : Array E)
    (h : col.size = 0 ∨ ∃ f, first = some f ∧ f + col.size ≤ table.size) :
    ∃ t', layRows table first col = some t' ∧ t'.size = table.size := by
  unfold layRows
  cases hc : col.toList with
  | nil => exact ⟨table, rfl, rfl⟩
  | cons e es =>
    have hsz : col.size = (e :: es).length := by rw [← hc, Array.length_toList]
    rcases h with h | ⟨f, rfl, hf⟩
    · rw [hsz] at h
      cases h
    · dsimp only
      rw [if_pos (by rw [← hsz]; exact hf)]
      exact ⟨_, rfl, size_layFrom _ _ _⟩

/-- What is asked of the found symbols: a hypothesis of `rows_there`. n: the number of positions. -/
structure ColsFit (L : GroupLayout) (opened : Array (Array Column)) (n : Nat) : Prop where
  col : ∀ w, w ≤ L.members.size → ∀ i, i < n → ∃ c, (opened[w]?).bind (·[i]?) = some c
  kept : ∀ w, w < L.members.size → L.kept.getD w false = false
  main : ∀ w, w < L.members.size → ∀ (i : Nat) (c : Column), (opened[w]?).bind (·[i]?) = some c →
    c.main.size = 0 ∨ ∃ f, L.mainFirst.getD w none = some f ∧ f + c.main.size ≤ 2 ^ L.k
  mask : ∀ w, w < L.members.size → ∀ (i : Nat) (c : Column), (opened[w]?).bind (·[i]?) = some c →
    c.mask.size = 0 ∨ ∃ f, L.maskFirst.getD w none = some f ∧ f + c.mask.size ≤ 2 ^ L.h
  fresh : ∀ (i : Nat) (c : Column), (opened[L.members.size]?).bind (·[i]?) = some c →
    c.mask.size = 2 ^ L.h

theorem layMembers_there (L : GroupLayout) (opened : Array (Array Column)) (n i : Nat) (hi : i < n)
    (H : ColsFit L opened n) : ∀ (ws : List Nat) (t : Tables), (∀ w ∈ ws, w < L.members.size) →
    t.main.size = 2 ^ L.k → t.mask.size = 2 ^ L.h → t.kept = #[] →
    ∃ t', layMembers L opened i ws t = some t' ∧ t'.kept = #[]
  | [], t, _, _, _, hk => ⟨t, rfl, hk⟩
  | w :: ws, t, hw, hm, hz, hk => by
    have hw0 := hw w (List.mem_cons_self ..)
    obtain ⟨c, hc⟩ := H.col w (Nat.le_of_lt hw0) i hi
    obtain ⟨mask, e1, s1⟩ := layRows_there t.mask (L.maskFirst.getD w none) c.mask
      (by rw [hz]; exact H.mask w hw0 i c hc)
    obtain ⟨main, e2, s2⟩ := layRows_there t.main (L.mainFirst.getD w none) c.main
      (by rw [hm]; exact H.main w hw0 i c hc)
    have hl : layMember L w c t = some ⟨main, mask, t.kept⟩ := by
      unfold layMember
      rw [e1, Option.bind_some, H.kept w hw0, e2]
      rfl
    rw [layMembers, hc, Option.bind_some, hl, Option.bind_some]
    exact layMembers_there L opened n i hi H ws _ (fun u hu => hw u (List.mem_cons_of_mem _ hu))
      (s2.trans hm) (s1.trans hz) hk

theorem rowsAt_there (s : SingleRows) (opened : Array (Array Column)) (n i : Nat) (hi : i < n)
    (H : ColsFit s.layout opened n) (h2 : s.masks = 2) (hk : s.keptRows = 0) (y : Array E) :
    ∃ y', rowsAt s opened y i = some y' := by
  obtain ⟨t, ht, hkept⟩ := layMembers_there s.layout opened n i hi H
    (List.range s.layout.members.size)
    ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩
    (fun w hw => List.mem_range.1 hw) (by simp) (by simp) rfl
  obtain ⟨c, hc⟩ := H.col s.layout.members.size (Nat.le_refl _) i hi
  have hf := H.fresh i c hc
  unfold rowsAt
  simp only [ht, Option.bind_some, hkept, hk, h2, hc, hf]
  simp

theorem rowsFrom_there (s : SingleRows) (opened : Array (Array Column)) (n : Nat)
    (H : ColsFit s.layout opened n) (h2 : s.masks = 2) (hk : s.keptRows = 0) :
    ∀ (is : List Nat) (y : Array E), (∀ i ∈ is, i < n) → ∃ y', rowsFrom s opened is y = some y'
  | [], y, _ => ⟨y, rfl⟩
  | i :: is, y, h => by
    obtain ⟨y1, e1⟩ := rowsAt_there s opened n i (h i (List.mem_cons_self ..)) H h2 hk y
    rw [rowsFrom, e1, Option.bind_some]
    exact rowsFrom_there s opened n H h2 hk is y1 fun j hj => h j (List.mem_cons_of_mem _ hj)

/-- **The rows' symbols are made**: `Own.rowsSymbols s opened n` returns a value. -/
theorem rows_there (s : SingleRows) (opened : Array (Array Column)) (n : Nat)
    (hs : shapeFits s = true) (h2 : s.masks = 2) (hk : s.keptRows = 0)
    (H : ColsFit s.layout opened n) : ∃ y, rowsSymbols s opened n = some y := by
  unfold rowsSymbols
  rw [if_pos hs]
  exact rowsFrom_there s opened n H h2 hk (List.range n) #[] fun i hi => List.mem_range.1 hi

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.size_layFrom
#print axioms ProofFile.Honest.K12.layRows_there
#print axioms ProofFile.Honest.K12.layMembers_there
#print axioms ProofFile.Honest.K12.rowsAt_there
#print axioms ProofFile.Honest.K12.rowsFrom_there
#print axioms ProofFile.Honest.K12.rows_there
#print axioms ProofFile.Honest.K12.ColsFit
