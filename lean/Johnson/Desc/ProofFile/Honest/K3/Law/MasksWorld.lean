-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/MasksWorld.lean: from "under slot j the sender's coin" to the
mask entries of the world in which the library reads a segment's forms. Conditional on a named
hypothesis, `SenderLays`. Its definition, two statements and theorems.

Terms. Honest/K3/GLOSSARY.md ("book, coins", "mask, mask row", "slot", "world, worth").

What is shown.
  `world_mask`: the world's mask entry under ledger slot j is entry j of the mask table of the
    segment's first message with mask rows (by the text of `dataOf`,
    Johnson/Desc/First/Batch/Law/AsRow.lean).
  `index_one`: at one mask row the table's index of the entry with the format's number j is j.
  `SenderLays`: the named hypothesis: the law of the part that sends the mask rows.
  `take_sum_le`: of a list of numbers: the sum of a front and the next entry are no more than the
    whole sum.
  `stage_room`: a stage's hidden values lie inside the lookup's.
  `masksAre_congr`: `MasksAre` (Honest/K3/Law/Statements.lean) reads a function of slots at the
    lookup's own slots alone.
  `MasksWorld`, `masksWorld`: the statement and its proof: if `MasksAre` holds of the course at
    "under slot j the coin number start + j", it holds at the world's own mask entries.
  `MasksWorldBook`, `masksWorldBook`: a composition of it with `masksFromBook`
    (Honest/K3/Law/MasksBook.lean): from the two tests on the book and the sender's law to
    `MasksAre` at the world's own mask entries.

Hypotheses that remain.
  `SenderLays`, at one mask row: a hypothesis on the part that sends the mask rows. It is proved of
    nothing here, nor in a file that this one imports.
  Why one mask row: the verifier's own text asks it. `K9.asRow` (Johnson/Desc/First/Batch/Text.lean)
    needs "K9.one-mask-row", takes one free mask entry for each slot off the message's own ledger,
    needs that the first taken is 0 and the last the count less one ("K9.mask-from-0"), and lays the
    equation's coefficients on the mask table from index 0 on, one by one.
  Two planes at least (`h2`); `maskOracle f` returns (`h`, in `world_mask`); the lookup's slots lie
    below n. `hs`: (in `stage_room`) the stage is one of the row's. `h`, `hm`: (in `masksAre_congr`)
    the two functions agree below the lookup's last slot; `MasksAre` holds at the first.
  In `MasksWorldBook` besides: the hypotheses of `MasksFromBook` (MasksBook.lean).
  `h`: (in `take_sum_le`) i < l.length.

Users. Honest/K3/Law/SpentFlat.lean [not in this library] imports this file.

Limits. That the table tab, of which the world is made, is what the sending part holds as sent is
not said. The numeral 1 stands in the statements: a caller must have "one mask row" at the link. The
world in front of a segment's second sending passes the data through a letter of the library's
(Stated.at1): that it changes no mask entry is not said. The theorems of this folder speak in worlds
that `Fork.worldOf` (OnBytes/Model/HideLaws.lean) makes of a function of slots and a function of
entries; the library's data are cells and mask entries: how such a world and the world in which the
library reads a segment's forms are one is for the callers of these statements to show.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MasksBook
import Johnson.Desc.First.Batch.Law.AsRow
import Johnson.Desc.K1.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.K9L (dataOf maskOracle)

/-- The world's mask entry under ledger slot j is entry j of the mask table. -/
theorem world_mask (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o : Nat) (h : maskOracle f = some o) (j : Nat) :
    (dataOf Rr f S tab).mask j = tab o .mask j := by
  simp only [dataOf, h]

/-- At one mask row the table's index of the entry with the format's number j is j. -/
theorem index_one (j : Nat) : j % 1 + j / 1 * 2 ^ VerifiableInference.Desc.K1.clog 1 = j := by
  simp [VerifiableInference.Desc.K1.clog, Nat.mod_one]

/-- **The named hypothesis: the law of the part that sends the mask rows**, in the form in which
that part's own file has it. tab o part J: entry J of a table of the oracle message number o. m: how
many mask rows the message has. The entry with the format's number j (row j % m, column j / m)
stands in the mask table at the index j % m + j / m * 2 ^ clog m, and is coin number start + j: for
the first n numbers. coin is a letter: where a statement fills it with a reading of the owner's
coins by `getD … zeroE`, the default is never taken where `bookFits` (each entry inside its owner's
coins) and `startsFit` (owner and start) hold and the face has at least two planes, up to the
lookup's last slot (`tests_fence`, `named_reads`, Honest/K3/Law/BookFence.lean): none of these is a
premise of this definition. -/
def SenderLays (tab : Nat → OnBytes.Part → Nat → GE) (o m n start : Nat) (coin : Nat → GE) : Prop :=
  ∀ j, j < n →
    tab o .mask (j % m + j / m * 2 ^ VerifiableInference.Desc.K1.clog m) = coin (start + j)

theorem take_sum_le : ∀ (l : List Nat) (i : Nat) (h : i < l.length), (l.take i).sum + l[i] ≤ l.sum
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => by simp
  | a :: l, i + 1, h => by
    have := take_sum_le l i (by simpa using h)
    simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
    omega

/-- A stage's hidden values lie inside the lookup's. -/
theorem stage_room (f : LFace) (h2 : 2 ≤ f.planes) (s : Stage) (hs : s ∈ stages f) :
    firstSlot f s + s.own f + s.tail f ≤ f.slots := by
  have hj : indexOf f s < (stages f).length := List.idxOf_lt_length_iff.2 hs
  have hj' : indexOf f s < ((stages f).map (Stage.slots f)).length := by simpa using hj
  have h := take_sum_le ((stages f).map (Stage.slots f)) (indexOf f s) hj'
  rw [slots_stages f h2, ← List.map_take, List.getElem_map] at h
  have e : (stages f)[indexOf f s]'hj = s := by simp [indexOf]
  rw [e] at h
  have h' : firstSlot f s + (s.own f + s.tail f) ≤ f.slots := h
  omega

/-- `MasksAre` reads a function of slots at the lookup's own slots alone. -/
theorem masksAre_congr {W : Type} (R : Course W) (h2 : 2 ≤ R.f.planes) (mask mask' : Nat → GE)
    (h : ∀ j, j < R.first + R.f.slots → mask' j = mask j) (hm : MasksAre R mask) :
    MasksAre R mask' := by
  intro s hs
  have hr := stage_room R.f h2 s hs
  obtain ⟨h1, h3⟩ := hm s hs
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · rw [h _ (by omega)]
    exact h1 i hi
  · rw [h _ (by
      show R.first + firstSlot R.f s + s.own R.f + j < _
      omega)]
    exact h3 j hj

/-- **Conditional on `SenderLays` at one mask row: the world's own mask entries under the lookup's
slots are the sender's coins.** The world in which the library reads a segment's forms has, as the
mask entry under ledger slot j, entry j of the mask table of the segment's first message with mask
rows (`dataOf`, Johnson/Desc/First/Batch/Law/AsRow.lean). The verifier's own text asks that this
message has one mask row and takes its entries from 0 on, one for each slot (`K9.asRow`,
Johnson/Desc/First/Batch/Text.lean: "K9.one-mask-row", "K9.mask-from-0"): so the table's index of
the entry for slot j is j, and it is the format's number j. If `MasksAre` holds of the course at
"under slot j the coin number start + j", it holds at the world's own mask entries. This is the
statement of a lemma, none of the library's goals. -/
def MasksWorld : Prop :=
  ∀ (W : Type) (R : Course W) (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n start : Nat) (coin : Nat → GE),
    2 ≤ R.f.planes → maskOracle f = some o → SenderLays tab o 1 n start coin →
    R.first + R.f.slots ≤ n → MasksAre R (fun j => coin (start + j)) →
    MasksAre R (dataOf Rr f S tab).mask

/-- **The proof of `MasksWorld`.** -/
theorem masksWorld : MasksWorld := by
  intro W R Rr f S tab o n start coin h2 ho hl hn hm
  refine masksAre_congr R h2 _ _ (fun j hj => ?_) hm
  have := hl j (by omega)
  rw [index_one] at this
  rw [world_mask Rr f S tab o ho j, this]

/-- **Conditional on `bookFits`, `startsFit` and `SenderLays` at one mask row: the world's own mask
entries under the lookup's slots are the coins that the stages spend.** ow: the owner: the part that
sends the segment's mask row. base: where, among its coins, the mask row's entries begin, in both
fields' counts: the book's entries start there (`startsFit`), and the sender lays them from its coin
number base.e of the extension field on (`SenderLays`). All three are hypotheses that are other
files' to show. The two tests on the book: no theorem of this file shows them;
Honest/K3/Law/BookAtSites.lean [not in this library] takes them at a book that a maker in other
files makes of a description, for a program to
evaluate. `SenderLays`: not shown in this file. That the book's base.e is the number at which the
sender lays the row is not shown in this file either. A coin is read by `getD … zeroE`, in the
hypothesis on the sender: up to the lookup's last slot the default is never taken where `bookFits`
(each entry inside its owner's coins) and `startsFit` (owner and start) hold: both are premises
here, and so is that the face has at least two planes (`tests_fence`, Honest/K3/Law/BookFence.lean);
n, the number of entries at which the sender's law is asked, has a lower bound alone. The end,
`MasksAre`, says the same with no default in it (`masksAre_entries`,
Honest/K3/Law/MasksAreFenced.lean [not in this library; so here read: not proved in this library]).
This is a lemma's statement, none of the library's goals. -/
def MasksWorldBook : Prop :=
  ∀ (W : Type) (R : Course W) (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (ow : Addr) (base : Due)
    (c : RowCoins (lookRow (V := Unit) ⟨ptsOf, pointsAt⟩ R.J R.a))
    (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n : Nat),
    2 ≤ R.f.planes →
    bookFits B rows (fun x => (look x).1) R.a = true → startsFit B R.a R.first ow base = true →
    rowSpent _ c = ((List.range (stages R.f).length).map fun i =>
      (entriesAt B R.a.place i).map (lentE look)) →
    CoinsAre R c → maskOracle f = some o →
    SenderLays tab o 1 n base.e (fun i => rd ((coinsE (look ow).2).getD i zeroE)) →
    R.first + R.f.slots ≤ n →
    MasksAre R (dataOf Rr f S tab).mask

/-- **The proof of `MasksWorldBook`.** -/
theorem masksWorldBook : MasksWorldBook := by
  intro W R B rows look ow base c Rr f S tab o n h2 hb hs hsp hc ho hl hn
  exact masksWorld W R Rr f S tab o n base.e _ h2 ho hl hn
    (masksFromBook W R B rows look ow base c hb hs hsp hc)

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.world_mask
#print axioms ProofFile.Honest.K3.Law.index_one
#print axioms ProofFile.Honest.K3.Law.take_sum_le
#print axioms ProofFile.Honest.K3.Law.stage_room
#print axioms ProofFile.Honest.K3.Law.masksAre_congr
#print axioms ProofFile.Honest.K3.Law.masksWorld
#print axioms ProofFile.Honest.K3.Law.masksWorldBook
