-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookWholeAlike.lean: WHERE TWO DESCRIPTIONS' THREE CHAINS ARE ALIKE
BLOCK BY BLOCK, IN ORDER, THE BOOK's OWN ELEVEN TESTS (ProverCoinCounts.clauses, Honest/Frame.lean) GIVE THE
SAME VERDICTS ON EVERY BOOK AT BOTH, AND THE MAKER OF THE WHOLE BOOK (bookWhole,
Honest/BookWhole.lean) GIVES ONE ANSWER AT BOTH: the same book, or the same refusal. Written by the
authors of the honest side of the linear claim's shared rounds (K14), in the frame's folder, not by
the frame's authors; the tests and the makers are theirs. Eleven statements with their proofs; no
definition. CONDITIONAL: the first eight on alike blocks or lists alone; the three at PlanAlike on
that relation, whole; the two "carried" also on hW: it returns at W. Of the library's relations
(Alike₂, PlanAlike: Johnson/AtFull/ProofPlan/PlanAlike.lean) place, rounds and oracles are spent;
"before", the arrow on the blocks' own tests and PlanAlike's fields fileOk, plans and depth are idle
here.

  maskWords_alike, masksOk_alike   the mask words that a sub-protocol states; the third test's part
                  at one chain. They spend oracles and place
  sizesIn_alike   each sub-protocol's place and number of rounds: what the tenth test looks up
  orderOf_alike   the order of places
  clauses_alike, word_alike, checked_alike   **the eleven tests, each under its name; the first that
                  fails; the book behind them, or the refusal**
  bookWhole_alike, bookWhole_planAlike   **the top**, at three lists and at the library's relation
                  PlanAlike (Johnson/AtFull/ProofPlan/PlanAlike.lean)
  bookWhole_carried, bookWhole_carried_guess   **a return is carried** from W to F; the same where
                  the merges are the guess mergesByName at each description's own first chain: the
                  very call that the frame's maker onlineProverFromPublicFiles makes (Honest/AtPure.lean)

How. ProverCoinCounts.clauses reads of a description the three lists' places (the library's alike₂_place),
orderOf, the sizes and masksOk: each has its congruence here; all else in it reads the book alone.
bookWhole is bookRaw, then ProverCoinCounts.checked: bookRaw_alike (Honest/BookRawAlike.lean).
Limits. NO TEST's VERDICT AND NO RETURN IS SHOWN BY IT, AT ANY DESCRIPTION: IT CARRIES ONE. That two
descriptions are alike is not had here. Bookkeeping: no new mathematics. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookRawAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Alike₂ PlanAlike alike₂_place)

variable {S Cl S' Cl' : Type}

/-- The mask words that a sub-protocol states. CONDITIONAL: h: the two blocks are alike. -/
theorem maskWords_alike {b : Block S Cl} {b' : Block S' Cl'} (h : Alike₂ b b') :
    maskWords b = maskWords b' := by
  unfold maskWords
  rw [h.2.2.1]

variable {l : List (Block S Cl)} {l' : List (Block S' Cl')}

/-- The third test's part at one chain. CONDITIONAL: h: the lists are alike. -/
theorem masksOk_alike (h : List.Forall₂ Alike₂ l l') (rows : List (Addr × Due)) :
    masksOk l rows = masksOk l' rows := by
  unfold masksOk
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.all_cons, maskWords_alike hb, hb.1, ih]

/-- Each sub-protocol's place and number of rounds. CONDITIONAL: h. -/
theorem sizesIn_alike (h : List.Forall₂ Alike₂ l l') :
    (l.map fun b => (b.place, b.rounds.length)) = l'.map fun b => (b.place, b.rounds.length) := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih => simp only [List.map_cons, hb.1, hb.2.1, ih]

variable {Xi Xi' : Type} {W : FileDescription Xi} {F : FileDescription Xi'}

/-- The order of places. CONDITIONAL: h₁ h₂ h₃: the three chains' flat lists are alike. -/
theorem orderOf_alike (h₁ : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder)
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder) : orderOf W = orderOf F := by
  unfold orderOf
  rw [alike₂_place _ _ h₁, alike₂_place _ _ h₂, alike₂_place _ _ h₃]

/-- **The eleven tests give the same verdicts.** CONDITIONAL: h₁ h₂ h₃. -/
theorem clauses_alike (h₁ : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder)
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder) (B : ProverCoinCounts) :
    B.clauses W = B.clauses F := by
  unfold ProverCoinCounts.clauses
  simp only [alike₂_place _ _ h₁, alike₂_place _ _ h₂, alike₂_place _ _ h₃,
    orderOf_alike h₁ h₂ h₃, sizesIn_alike h₁, sizesIn_alike h₂, sizesIn_alike h₃,
    masksOk_alike h₁, masksOk_alike h₂, masksOk_alike h₃]

/-- The name of the first test that fails, or that none does. CONDITIONAL: h₁ h₂ h₃. -/
theorem word_alike (h₁ : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder)
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder) (B : ProverCoinCounts) : B.word W = B.word F := by
  unfold ProverCoinCounts.word
  rw [clauses_alike h₁ h₂ h₃]

/-- CONDITIONAL: h₁ h₂ h₃. The same book, or the same refusal. -/
theorem checked_alike (h₁ : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder)
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder) (B : ProverCoinCounts) :
    ProverCoinCounts.checked W B = ProverCoinCounts.checked F B := by
  unfold ProverCoinCounts.checked
  rw [word_alike h₁ h₂ h₃]

/-- **THE TOP.** CONDITIONAL: h₁ h₂ h₃. The same book, or the same refusal. -/
theorem bookWhole_alike (h₁ : List.Forall₂ Alike₂ W.first.blocksInOrder F.first.blocksInOrder)
    (h₂ : List.Forall₂ Alike₂ W.shared.blocksInOrder F.shared.blocksInOrder)
    (h₃ : List.Forall₂ Alike₂ W.second.blocksInOrder F.second.blocksInOrder)
    (p0 p1 p2 : Johnson.G.ChainSends) (M : Merges) :
    bookWhole W p0 p1 p2 M = bookWhole F p0 p1 p2 M := by
  unfold bookWhole
  rw [bookRaw_alike h₁ h₂ h₃]
  congr 1
  funext B
  exact checked_alike h₁ h₂ h₃ B

/-- At the library's relation. CONDITIONAL: h. -/
theorem bookWhole_planAlike (h : PlanAlike W F) (p0 p1 p2 : Johnson.G.ChainSends) (M : Merges) :
    bookWhole W p0 p1 p2 M = bookWhole F p0 p1 p2 M :=
  bookWhole_alike h.first h.shared h.second p0 p1 p2 M

/-- **A RETURN IS CARRIED.** CONDITIONAL: h; hW: it returns at W. -/
theorem bookWhole_carried (h : PlanAlike W F) {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (hW : bookWhole W p0 p1 p2 M = .ok B) : bookWhole F p0 p1 p2 M = .ok B :=
  (bookWhole_planAlike h p0 p1 p2 M).symm.trans hW

/-- **A return is carried where the merges are the guess at each description's own first chain.**
CONDITIONAL: h; hW. -/
theorem bookWhole_carried_guess (h : PlanAlike W F) {p0 p1 p2 : Johnson.G.ChainSends} {B : ProverCoinCounts}
    (hW : bookWhole W p0 p1 p2 (mergesByName W.first.blocksInOrder) = .ok B) :
    bookWhole F p0 p1 p2 (mergesByName F.first.blocksInOrder) = .ok B := by
  rw [← mergesByName_alike h.first]
  exact bookWhole_carried h hW

end ProofFile.Honest

#print axioms ProofFile.Honest.maskWords_alike
#print axioms ProofFile.Honest.masksOk_alike
#print axioms ProofFile.Honest.sizesIn_alike
#print axioms ProofFile.Honest.orderOf_alike
#print axioms ProofFile.Honest.clauses_alike
#print axioms ProofFile.Honest.word_alike
#print axioms ProofFile.Honest.checked_alike
#print axioms ProofFile.Honest.bookWhole_alike
#print axioms ProofFile.Honest.bookWhole_planAlike
#print axioms ProofFile.Honest.bookWhole_carried
#print axioms ProofFile.Honest.bookWhole_carried_guess
