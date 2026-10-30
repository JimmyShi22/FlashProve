-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/WordsMore.lean: THREE LEMMAS
AROUND THE
TERM "words" (Johnson/Desc/Sound/WordsAt.lean). Theorems with their proofs.
The five points are B1 to B5.

  (B5 i) **`wordsBy_reads`**: what a text of this project said and no lemma did: AT THE NUMBER o THE
  TERM READS OF A
    WITNESS ITS MESSAGE OF THE SEAT's NUMBER AND ITS PAD AT THE SEAT, ALONE: two witnesses that
    agree in
    these two give the same words at o. `tabAt_reads`: the like of the tables.
  (B1) `lengthsOk_of_start`: `wordsOn` cuts the rows at the real rows and does not cut the PLACES at
  the code's length: where a message length is no power of two the term reads places that no pin
    fixes. `Codes.lengthsOk` shuts that. It stood in no fence of these files (`BookedLast`,
    WordsAt.lean; `AtStart`, ReadsAt.lean). THE START's YES GIVES IT: the
    last chain's `start₃E` tests it first of all: so at the start's record the codes have it.
  (B2) `seat_there`: where the book has no place for o, or no tree there, the table is 0, and every
    row on o with the target 0 holds of every witness. Inside the fence that does not happen at a
    message of the statement in front: under `BookedLast o s s'` every n < s.st.oracles.size HAS a
    seat through the record in front.

NOT MET HERE: (B3) that `seatBy` is one-to-one on a statement's messages (`noLast`'s third arm is a
natural subtraction; t₁, t₂ are letters): said nowhere · (B4) the seam "number = place" · (B5 ii)
the
ride of an item along the first chain's borders: `words_older` is typed for ONE block alone.
Limits. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BookedOfFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.Third (S₃ SharedOut start₃E start₃ firstOutFrom)

section
variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- The table of the message number o reads of a witness its message of the seat's number and its
pad
at the seat, alone. -/
theorem tabAt_reads (cs : Codes) (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement)
    (w w' : Wit Cells Tok MsgT) (o : ℕ)
    (h : ∀ q, seatAt o = some q → w'.msg (arr q.1 q.2) = w.msg (arr q.1 q.2) ∧
      w'.pad q.1 q.2 = w.pad q.1 q.2) :
    tabAt cs arr seatAt S w' o = tabAt cs arr seatAt S w o := by
  unfold tabAt
  cases hq : seatAt o with
  | none => rfl
  | some q =>
    cases S.oracles[o]? with
    | none => rfl
    | some y =>
      funext mask row place
      show (if padB cs y.shape mask row place = true then w'.pad q.1 q.2 mask row place
        else w'.msg (arr q.1 q.2) mask row place) =
        (if padB cs y.shape mask row place = true then w.pad q.1 q.2 mask row place
        else w.msg (arr q.1 q.2) mask row place)
      rw [(h q hq).1, (h q hq).2]

/-- **So do the words.** -/
theorem wordsBy_reads (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement) (w w' : Wit Cells Tok MsgT)
    (o : ℕ)
    (h : ∀ q, seatAt o = some q → w'.msg (arr q.1 q.2) = w.msg (arr q.1 q.2) ∧
      w'.pad q.1 q.2 = w.pad q.1 q.2) (part : Part) (i : ℕ) :
    wordsBy arr seatAt S w' o part i = wordsBy arr seatAt S w o part i := by
  unfold wordsBy
  exact wordsOn_congr S S _ _ o o rfl (tabAt_reads arr S.codes seatAt S w w' o h) part i

end

/-- **The start's yes: every code's message length is a power of two**, at the start's record. -/
theorem lengthsOk_of_start (codes : Codes) (S : Params.LinShape) (st₁ : Statement)
    (book₁ : TreeBook) (roots₁ w₁ own₁ : ℕ) (mask₁ : Option ℕ) (pile₁ : List TensorRow)
    (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.st.codes.lengthsOk = true := by
  unfold start₃E at h
  split at h
  · cases h
  · rename_i hl
    split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i s hs
        obtain rfl := Except.ok.inj h
        unfold start₃ at hs
        split at hs
        · rename_i hc
          obtain rfl := Option.some.inj hs
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true] at hl
          show f.st.codes.lengthsOk = true
          rw [hc.1.1]
          exact hl.1
        · cases hs

/-- **Inside the fence every message of the statement in front has a seat.** -/
theorem seat_there (no : ℕ → Tree → ℕ) (o : SharedOut) (s s' : S₃) (hB : BookedLast o s s') (n : ℕ)
    (hn : n < s.st.oracles.size) : ∃ q, seatBy no s.book n = some q := by
  obtain ⟨_, _, _, _, _, _, _, hsz, _⟩ := hB.bookSays
  have hp : n < s.book.place.size := hsz ▸ hn
  have hq := Array.getElem?_eq_getElem hp
  have ht := Array.getElem?_eq_getElem (hB.placed n _ hq)
  exact ⟨_, seatBy_some no s.book n _ _ hq ht⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tabAt_reads
#print axioms VerifiableInference.Desc.Sound.wordsBy_reads
#print axioms VerifiableInference.Desc.Sound.lengthsOk_of_start
#print axioms VerifiableInference.Desc.Sound.seat_there
