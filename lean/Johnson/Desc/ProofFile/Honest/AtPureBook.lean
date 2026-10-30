-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureBook.lean: WHAT THE BOOK OF `onlineProverFromPublicFiles` (Honest/AtPure.lean) IS
MADE OF: of the description and the library's list of sendings at the three public files: THE
FILLING IS NOT READ. Statements with their proofs, by unfolding the maker.

  `atPure_book`       where the maker yields: the library's list of sendings has seven chains, and
                     the book is what `bookWhole` (Honest/BookWhole.lean) yields at the
                     description, the last three chains' sendings and the merges by name of the
                     description's first chain
  `atPure_book_same`  so at two fillings, of whichever types, at the same three files and the same
                     hash: the same public part, ground, description and BOOK

Limits. It says of what the book is made, not that the book is right. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ Rc Tr X₀ X : Type}

theorem atPure_book {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ a b c d p0 p1 p2, Johnson.G.sendsOf pol lay KL = .ok [a, b, c, d, p0, p1, p2] ∧
      bookWhole A.F p0 p1 p2 (mergesByName A.F.first.blocksInOrder) = .ok A.B := by
  unfold onlineProverFromPublicFiles at h
  obtain ⟨Z, _, h⟩ := bind_ok h
  obtain ⟨G, _, h⟩ := bind_ok h
  obtain ⟨F, _, h⟩ := bind_ok h
  obtain ⟨cs, hcs, h⟩ := bind_ok h
  split at h
  · obtain ⟨B, hB, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨_, _, _, _, _, _, _, hcs, hB⟩
  · cases h

theorem atPure_book_same {W₀' Rc' Tr' X₀' X' : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {P' : OnlineProverParts W₀' Rc' Tr' X₀' X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    {A' : OnlineProverWithDescription W₀' Rc' Tr' X₀' X'} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (h' : onlineProverFromPublicFiles o pol lay KL P' = .ok A') :
    A.Z = A'.Z ∧ A.G = A'.G ∧ A.F = A'.F ∧ A.B = A'.B := by
  have k := atPure_ok h
  have k' := atPure_ok h'
  have eZ : A.Z = A'.Z := Except.ok.inj (k.1.symm.trans k'.1)
  have eG : A.G = A'.G := Option.some.inj ((k.2.1.symm.trans (by rw [eZ])).trans k'.2.1)
  have eF : A.F = A'.F := Except.ok.inj (k.2.2.1.symm.trans k'.2.2.1)
  obtain ⟨a, b, c, d, p0, p1, p2, hs, hB⟩ := atPure_book h
  obtain ⟨a', b', c', d', q0, q1, q2, hs', hB'⟩ := atPure_book h'
  have el := Except.ok.inj (hs.symm.trans hs')
  simp only [List.cons.injEq, and_true] at el
  obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := el
  rw [eF] at hB
  exact ⟨eZ, eG, eF, Except.ok.inj (hB.symm.trans hB')⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.atPure_book
#print axioms ProofFile.Honest.atPure_book_same
