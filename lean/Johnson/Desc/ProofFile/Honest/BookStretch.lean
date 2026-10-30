-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookStretch.lean: the maker of the book of coins (`ProverCoinCounts`,
Honest/Frame.lean), fourteenth file: A TEST WITH CODE ON THE BOOK ALONE, AND THE STATEMENT THAT IT
PAYS: WHAT THE PARTS OF A ROW SPEND IS ONE STRETCH OF ONE SENDER's COINS. The test walks the book's
spending entries that name the row's parts, part by part, and asks that all have one owner and that
each begins, among the owner's coins of the extension field, where the one in front ends. Where it
says yes, the premise's form `RowIsStretch` (Honest/Law/Rule/TiesFall.lean) holds at every run's
coins. General in the book: the maker's text is not read. Definitions with code, tests at synthetic
entries, and statements with proofs.

  `rowEntries`        the book's spending entries that name the parts number j to j + n - 1 at a
                     place
  `runOn`, `oneStretch`   THE TEST: the owner, the first coin's number and the count; `none` where
                     the list is empty, where two owners stand in it, or where a stretch does not
                     begin at the end of the one in front
  `rowSpent_entries`  what a row spends is its entries' runs, in a row
  `runOn_slices`, `oneStretch_slices`   where the test says yes, these runs are one stretch
  `rowIsStretch_of`   THE STATEMENT: `oneStretch (rowEntries Bk p n 0) = some (o, s₀, cnt)` gives
                     `RowIsStretch Bk ch p n o s₀ cnt`

Limits. Coins of the extension field alone, as `rowSpent`. A row that spends of two messages (a
merge, whose end values lie under the index-mask message) fails the test: it is not one stretch.
That the first coin's number is the one that the plan gives (`startOf`, Honest/BookStart.lean) is
not said here. That the stretch lies within the owner's count, and that chain ch is given the
owner's coins, is not asked: else both sides are shorter than cnt, without an error. Nothing on a
run or a measure. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.SpentStart
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place)

/-- **The book's spending entries that name a row's parts**, part by part: n parts from number j on.
-/
def rowEntries (Bk : ProverCoinCounts) (p : Place) : Nat → Nat → List Ahead
  | 0, _ => []
  | n + 1, j => spentE Bk ⟨p, j⟩ ++ rowEntries Bk p n (j + 1)

/-- The walk: o: the owner. s: the first coin's number. c: how many coins so far. It yields the
count. -/
def runOn (o : Addr) (s : Nat) : Nat → List Ahead → Option Nat
  | c, [] => some c
  | c, f :: fs => if f.owner = o ∧ f.start.e = s + c then runOn o s (c + f.count.e) fs else none

/-- **THE TEST**: the owner, the first coin's number, the count. -/
def oneStretch : List Ahead → Option (Addr × Nat × Nat)
  | [] => none
  | e :: es => (runOn e.owner e.start.e e.count.e es).map fun c => (e.owner, e.start.e, c)

variable (look : Addr → (d : Due) × Cs d)

/-- What a row spends is its entries' runs, in a row. -/
theorem rowSpent_entries (Bk : ProverCoinCounts) (p : Place) : ∀ n j,
    rowSpent Bk look p n j = (rowEntries Bk p n j).flatMap (sliceE look)
  | 0, _ => rfl
  | n + 1, j => by
    show spentAt Bk look ⟨p, j⟩ ++ rowSpent Bk look p n (j + 1) =
      (spentE Bk ⟨p, j⟩ ++ rowEntries Bk p n (j + 1)).flatMap (sliceE look)
    rw [List.flatMap_append, rowSpent_entries Bk p n (j + 1)]
    rfl

/-- Where the walk yields, the stretch so far with the entries' runs behind it is the whole stretch.
-/
theorem runOn_slices (o : Addr) (s : Nat) : ∀ (fs : List Ahead) (c c' : Nat),
    runOn o s c fs = some c' →
    ((coinsE (look o).2).drop s).take c ++ fs.flatMap (sliceE look) =
      ((coinsE (look o).2).drop s).take c'
  | [], c, c', h => by
    have e : c = c' := Option.some.inj h
    subst e
    exact List.append_nil _
  | f :: fs, c, c', h => by
    unfold runOn at h
    split at h
    · rename_i hc
      obtain ⟨ho, hs⟩ := hc
      have e : ((coinsE (look o).2).drop s).take c ++ sliceE look f =
          ((coinsE (look o).2).drop s).take (c + f.count.e) := by
        unfold sliceE
        rw [ho, hs]
        exact take_two _ s c f.count.e
      rw [List.flatMap_cons, ← List.append_assoc, e]
      exact runOn_slices o s fs _ _ h
    · cases h

/-- **Where the test says yes, the entries' runs are one stretch of the owner's coins.** -/
theorem oneStretch_slices {es : List Ahead} {o : Addr} {s₀ cnt : Nat}
    (h : oneStretch es = some (o, s₀, cnt)) :
    es.flatMap (sliceE look) = ((coinsE (look o).2).drop s₀).take cnt := by
  cases es with
  | nil => cases h
  | cons e es =>
    have h' : (runOn e.owner e.start.e e.count.e es).map (fun c => (e.owner, e.start.e, c)) =
        some (o, s₀, cnt) := h
    cases hr : runOn e.owner e.start.e e.count.e es with
    | none =>
      rw [hr] at h'
      cases h'
    | some c =>
      rw [hr] at h'
      have e' : (e.owner, e.start.e, c) = (o, s₀, cnt) := Option.some.inj h'
      cases e'
      rw [List.flatMap_cons]
      exact runOn_slices look e.owner e.start.e es _ _ hr

/-- **THE STATEMENT.** -/
theorem rowIsStretch_of {Bk : ProverCoinCounts} {ch : Nat} {p : Place} {n : Nat} {o : Addr} {s₀ cnt : Nat}
    (h : oneStretch (rowEntries Bk p n 0) = some (o, s₀, cnt)) :
    RowIsStretch Bk ch p n o s₀ cnt := by
  intro k
  rw [rowSpent_entries]
  exact oneStretch_slices _ h

/-! ### Tests at synthetic entries -/

namespace BookStretchToy

def o : Addr := ⟨⟨1, some 0, 1, .K1⟩, 0⟩
def q : Addr := ⟨⟨1, some 0, 3, .K3⟩, 0⟩
def en (owner : Addr) (s c : Nat) : Ahead := ⟨"x", owner, ⟨0, s⟩, ⟨0, c⟩, q, true⟩

#guard oneStretch [en o 4 2, en o 6 5, en o 11 1] == some (o, 4, 8)
-- a gap; an overlap; a second owner; no entry
#guard oneStretch [en o 4 2, en o 7 5] == none && oneStretch [en o 4 2, en o 5 5] == none &&
  oneStretch [en o 4 2, en q 6 5] == none && oneStretch [] == none

end BookStretchToy

end ProofFile.Honest

#print axioms ProofFile.Honest.rowSpent_entries
#print axioms ProofFile.Honest.runOn_slices
#print axioms ProofFile.Honest.oneStretch_slices
#print axioms ProofFile.Honest.rowIsStretch_of
