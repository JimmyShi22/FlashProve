-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/HeldShift.lean: **"THE RECORD HOLDS THE SAMPLE" (smpHeld) ON A CHAIN THAT IS NOT THE FILE's FIRST: THE BOOK COUNTS ITS TREES FROM 0, THE TABLE's SEATS FROM lo.** One definition;
statements and proofs.

smpHeld st book j t (Johnson/Desc/SmpRows.lean) looks in the book for a message whose place is (j, t). Its own head says: "a tree's number in the book is its place among the trees that the session has
sent: in the first chain that is MEANT to be its number through the file …; of the other two chains nothing is said here". The shared table's promise (promSigS, Johnson/Desc/Sound/BordersSharedFill.lean) asks
held := smpHeld (stOf s) (bookOf s) (N.tenant m).1 (N.tenant m).2, and N.tenant m is a seat THROUGH THE FILE: its tree's number is at least N.lo (SentBefore.lo). The shared chain's own book begins
empty (Desc.K14.first) and a receiving places a new message at (the book's count of trees + …): so its places run from 0.
  PlacesInBook B      every place of the book names a tree of the book.
  oracleNo_high · **smpHeld_high**   under PlacesInBook: at a tree number j from the book's count of trees on: NO message sits there: smpHeld = false. SO WITH bookOf := the chain's own book THE PROMISE
                      "held" IS FALSE AT EVERY RECORD WHOSE BOOK HAS AT MOST lo TREES: the promise is empty there.
  shiftBook lo B      the book with every place's tree number raised by lo: THE READER THAT THE TABLE's SEATS WANT.
  oracleNo_shift · smpRows_shift · **smpHeld_shift**   at the seat (lo + z, t) the shifted book says what the chain's own book says at (z, t).
  placesIn_empty · placesIn_recv   an empty book has PlacesInBook; a receiving keeps it where the planner's layout names its own trees.
Limits. Where lo is smaller than the book's count of trees the unshifted reader is not false at every seat: it then reads ANOTHER tree's tenant. Nothing on what a sample is worth. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.SmpRows
import Johnson.Desc.Sound.BookInOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes

/-- Every place of the book names a tree of the book. -/
def PlacesInBook (B : TreeBook) : Prop :=
  ∀ (o : ℕ) (q : ℕ × ℕ), B.place[o]? = some q → q.1 < B.trees.size

/-- No message sits in a tree that the book has not. -/
theorem oracleNo_high (B : TreeBook) (h : PlacesInBook B) (j t : ℕ) (hj : B.trees.size ≤ j) :
    oracleNo B j t = none := by
  unfold oracleNo
  rw [List.find?_eq_none]
  intro o _ ho
  have e : B.place[o]? = some (j, t) := beq_iff_eq.1 ho
  have := h o _ e
  omega

/-- **So the record "holds" no sample there.** -/
theorem smpHeld_high (st : Statement) (B : TreeBook) (h : PlacesInBook B) (j t : ℕ)
    (hj : B.trees.size ≤ j) : smpHeld st B j t = false := by
  unfold smpHeld smpSeed
  rw [oracleNo_high B h j t hj]
  rfl

/-- **The book as the table's seats read it**: every place's tree number raised by lo. -/
def shiftBook (lo : ℕ) (B : TreeBook) : TreeBook :=
  { B with place := B.place.map fun q => (lo + q.1, q.2) }

theorem oracleNo_shift (lo : ℕ) (B : TreeBook) (z t : ℕ) :
    oracleNo (shiftBook lo B) (lo + z) t = oracleNo B z t := by
  unfold oracleNo shiftBook
  simp only [Array.size_map]
  congr 1
  funext o
  rw [Array.getElem?_map]
  cases hq : B.place[o]? with
  | none => rfl
  | some q =>
    obtain ⟨a, b⟩ := q
    show (some (lo + a, b) == some (lo + z, t)) = (some (a, b) == some (z, t))
    by_cases e : a = z ∧ b = t
    · obtain ⟨rfl, rfl⟩ := e
      simp
    · have h1 : ¬ ((lo + a, b) = (lo + z, t)) := by
        intro h
        have h2 := Prod.mk.inj h
        exact e ⟨by omega, h2.2⟩
      have h2 : ¬ ((a, b) = (z, t)) := by
        intro h
        have h3 := Prod.mk.inj h
        exact e ⟨h3.1, h3.2⟩
      simp [h1, h2]

theorem smpRows_shift (st : Statement) (lo : ℕ) (B : TreeBook) (z t : ℕ) :
    smpRows st (shiftBook lo B) (lo + z) t = smpRows st B z t := by
  unfold smpRows
  rw [oracleNo_shift]

/-- **At the seat (lo + z, t) the shifted book says what the chain's own book says at (z, t).** -/
theorem smpHeld_shift (st : Statement) (lo : ℕ) (B : TreeBook) (z t : ℕ) :
    smpHeld st (shiftBook lo B) (lo + z) t = smpHeld st B z t := by
  unfold smpHeld smpSeed
  rw [oracleNo_shift, smpRows_shift]

theorem placesIn_empty : PlacesInBook { trees := #[], place := #[] } := fun o q h => by simp at h

/-- A receiving keeps it, where the planner's layout names its own trees. -/
theorem placesIn_recv (ft : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay)
    (n0 roots : ℕ) (h : PlacesInBook bk) (hl : ∀ i, i < sent.size → lay.tree.getD i 0 < lay.shapes.size) :
    PlacesInBook (recvBook ft bk sent lay n0 roots) := by
  have hsz : (recvBook ft bk sent lay n0 roots).trees.size = bk.trees.size + lay.shapes.size := by
    show (OnBytes.Slice.partsLaid sent lay n0 bk.trees.size
      (OnBytes.Slice.treesSent ft lay.shapes.toList roots bk.trees)).size = _
    rw [partsLaid_count, treesSent_count, Array.length_toList]
  intro o q hq
  rw [hsz]
  by_cases ho : o < bk.place.size
  · rw [recvBook_place_old ft bk sent lay n0 roots o ho] at hq
    have := h o q hq
    omega
  · obtain ⟨i, rfl⟩ : ∃ i, o = bk.place.size + i := ⟨o - bk.place.size, by omega⟩
    have hi : i < sent.size := by
      have h1 := (Array.getElem?_eq_some_iff.1 hq).1
      have h2 : (recvBook ft bk sent lay n0 roots).place.size = bk.place.size + sent.size := by
        show (bk.place ++ _).size = _
        simp
      omega
    rw [recvBook_place_new ft bk sent lay n0 roots i hi] at hq
    have e := Option.some.inj hq
    rw [← e]
    have := hl i hi
    show bk.trees.size + lay.tree.getD i 0 < _
    omega

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.smpHeld_high
#print axioms VerifiableInference.Desc.Sound.smpHeld_shift
#print axioms VerifiableInference.Desc.Sound.placesIn_recv
