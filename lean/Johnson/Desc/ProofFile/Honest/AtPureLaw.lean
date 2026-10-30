-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureLaw.lean: what `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns, where it
returns: statements that hold by unfolding its definition. Statements and proofs.

  `atPure_ok`   where `onlineProverFromPublicFiles` returns A: A's public part, blank ground and description are what
     `pubPlain`, `blankBy` and `onlineDescription` return at the same files; A's prover has the filling's
     trace, columns and range at A's own public part, the key `pureKey`, and the filling's prover's
     sides at A's public part and ground; the readers and the messages' data are the filling's there
  `atPure_trace`   the clause on the trace alone
  `bookWhole_word`, `atPure_tests`   the tests that `onlineProverFromPublicFiles` has asked, where it returns: the book
     fails none of its own tests at the description; every prover's side is at a place of its chain;
     the named element of the range is in range
  `bind_ok`, `due?_ok`   two small tools

What they are for. A lemma on a filling's trace speaks of `P.trace Z`; a lemma on the honest side
speaks of `H.trace`. These carry the one to the other at the prover that `onlineProverFromPublicFiles` returns.

Limits.
  * They say nothing where `onlineProverFromPublicFiles` returns an error, and not that it returns at any files.
  * Nothing on a run, a coin or a measure.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ Rc Tr X₀ X : Type}

universe u v w in
/-- Where a bind returns, its first part has returned. -/
theorem bind_ok {ε : Type u} {α : Type v} {β : Type w} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e =>
    have h' : (Except.error e : Except ε β) = .ok b := h
    cases h'
  | ok a => exact ⟨a, rfl, h⟩

universe u in
/-- Where `due?` returns, the value was there. -/
theorem due?_ok {α : Type u} {what : String} {x : Option α} {a : α} (h : due? what x = .ok a) :
    x = some a := by
  cases x with
  | none =>
    have h' : (Except.error (what ++ " is not found") : Except String α) = .ok a := h
    cases h'
  | some y =>
    have h' : (Except.ok y : Except String α) = .ok a := h
    cases h'
    rfl

/-- **Where `onlineProverFromPublicFiles` returns.** -/
theorem atPure_ok {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    pubPlain o pol lay KL = .ok A.Z ∧ blankBy pureRoad.links A.Z = some A.G ∧
      onlineDescription o pol lay KL = .ok A.F ∧ A.H.trace = P.trace A.Z ∧ A.H.stored = P.enc A.Z ∧
      A.H.inRange = P.inRange ∧ A.H.key = pureKey ∧ A.H.first = firstOf A.Z A.G P.lots ∧
      A.H.shared = P.shared A.Z A.G ∧ A.H.second = P.second A.Z A.G ∧
      A.readers = P.readers A.Z ∧ A.rows = P.rows A.Z A.G := by
  unfold onlineProverFromPublicFiles at h
  obtain ⟨Z, hZ, h⟩ := bind_ok h
  obtain ⟨G, hG, h⟩ := bind_ok h
  obtain ⟨F, hF, h⟩ := bind_ok h
  obtain ⟨cs, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨B, _, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨hZ, due?_ok hG, hF, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases h

/-- `bookWhole` returns only a book that fails none of its own tests. -/
theorem bookWhole_word {Xi : Type} {F : VerifiableInference.Desc.FileDescription Xi}
    {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (h : bookWhole F p0 p1 p2 M = .ok B) : B.word F = none := by
  unfold bookWhole at h
  obtain ⟨W, _, h⟩ := bind_ok h
  unfold ProverCoinCounts.checked at h
  split at h
  · cases h
    assumption
  · cases h

/-- **The tests that `onlineProverFromPublicFiles` has asked, where it returns**: the book fails none of its own tests at
the description; every prover's side is at a place of its chain; the named element of the range is
in range. -/
theorem atPure_tests {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    A.B.word A.F = none ∧ (strays A.F.first.blocksInOrder A.H.first).isEmpty = true ∧
      (strays A.F.shared.blocksInOrder A.H.shared).isEmpty = true ∧
      (strays A.F.second.blocksInOrder A.H.second).isEmpty = true ∧ A.H.inRange A.H.dummy = true := by
  unfold onlineProverFromPublicFiles at h
  obtain ⟨Z, _, h⟩ := bind_ok h
  obtain ⟨G, _, h⟩ := bind_ok h
  obtain ⟨F, _, h⟩ := bind_ok h
  obtain ⟨cs, _, h⟩ := bind_ok h
  split at h
  · obtain ⟨B, hB, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · rename_i hs
      split at h
      · cases h
      · rename_i hd
        cases h
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hs hd
        exact ⟨bookWhole_word hB, hs.1.1, hs.1.2, hs.2, hd⟩
  · cases h

/-- The clause on the trace alone. -/
theorem atPure_trace {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) : A.H.trace = P.trace A.Z :=
  (atPure_ok h).2.2.2.1

end ProofFile.Honest

#print axioms ProofFile.Honest.bind_ok
#print axioms ProofFile.Honest.due?_ok
#print axioms ProofFile.Honest.atPure_ok
#print axioms ProofFile.Honest.bookWhole_word
#print axioms ProofFile.Honest.atPure_tests
#print axioms ProofFile.Honest.atPure_trace
