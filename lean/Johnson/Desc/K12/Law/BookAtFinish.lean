-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.BookThrough
import Johnson.Desc.K12.AtFinish
/-
Johnson/Desc/K12/Law/BookAtFinish.lean: THE PROXIMITY TEST AT THE FIRST CHAIN's FINISH (atFinish, Johnson/Desc/K12/AtFinish.lean) HANDS ON «THE BOOK's NUMBERS»: the record counts as many roots as its book has trees, and every tree bears its place's number. For the row book_numbers_first_chain. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
«NO TREE COMES OR GOES, THE ROOTS STAY» IS FALSE OF THIS BLOCK: each code switch inside the test receives a tree, and the reading of the old rows counts at how many lists a tree has been opened. What holds is: THE INVARIANT IN FRONT GIVES THE INVARIANT BEHIND.
  BookInv s            s.roots = s.book.trees.size ∧ ∀ z T, s.book.trees[z]? = some T → T.number = z: the row's carrier's form, at the first chain's record
  bookInv_iff          BookInv s ↔ BookStep 0 s.book s.roots (the form of Johnson/Desc/Sound/BookOrder.lean)
  atFinish_bookStep    a yes of atFinish p from s to s' · p.early = true · p.answers = 1 · BookStep p.nums.firstTree in front ⇒ behind
  atFinish_bookInv     … · p.nums.firstTree = 0 · BookInv s ⇒ BookInv s'
ALL THE WEIGHT IS k12_bookStep (Johnson/Desc/K12/Coin/BookThrough.lean): called. What is added: the two doors: enterFinish lays the chain's record's book and roots into the test's; leaveFinish writes the test's back: in the manner of that file's seat_bookStep.
THE THREE PREMISES ON THE PLACE: firstTree = 0: at every place that the maker lays for this test (places_firstTree, Johnson/Desc/K12/Law/FirstTreeOfMade.lean) · early | answers: two numbers of the plan (the masks ride; the setting's samples): true | 1 at the two closed places; in general premises.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace VerifiableInference.Desc.K12.Coin
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open VerifiableInference.Desc.Sound (BookOrd BookStep)

/-- The row's carrier's form. -/
def BookInv (s : First.S) : Prop :=
  s.roots = s.book.trees.size ∧ ∀ (z : ℕ) (T : Tree), s.book.trees[z]? = some T → T.number = z

theorem bookInv_iff (s : First.S) : BookInv s ↔ BookStep 0 s.book s.roots := by
  unfold BookInv BookStep BookOrd
  simp only [Nat.zero_add]

theorem atFinish_bookStep (p : P12) (he : p.early = true) (ha : p.answers = 1) (s s' : First.S)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (atFinish p).decide s rs gs = .ok s')
    (hB : BookStep p.nums.firstTree s.book s.roots) :
    BookStep p.nums.firstTree s'.book s'.roots := by
  have h' : ((enterFinish s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (leaveFinish s)) = .ok s' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  have e : t.book = s.book ∧ t.roots = s.roots := by
    unfold enterFinish at ht
    split at ht
    · obtain ⟨_, _, ht⟩ := (Seat.ebind_ok _ _ _).1 ht
      obtain ⟨_, _, ht⟩ := (Seat.ebind_ok _ _ _).1 ht
      cases ht
      exact ⟨rfl, rfl⟩
    · cases ht
  cases hl
  exact k12_bookStep p he ha t t' rs gs ht' (by rw [e.1, e.2]; exact hB)


theorem atFinish_bookInv (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hf : p.nums.firstTree = 0) (s s' : First.S) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (atFinish p).decide s rs gs = .ok s') (hB : BookInv s) : BookInv s' := by
  rw [bookInv_iff] at hB ⊢
  have := atFinish_bookStep p he ha s s' rs gs h (by rw [hf]; exact hB)
  rw [hf] at this
  exact this

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atFinish_bookStep
#print axioms VerifiableInference.Desc.K12.Coin.atFinish_bookInv
