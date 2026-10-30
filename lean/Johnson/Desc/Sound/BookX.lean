-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BookX.lean: **THE SECOND BOOL BESIDE "shape k" ON THE SHARED CHAIN: WHAT THE TWO PROXIMITY TESTS WANT OF THE RECORD, BORDER BY BORDER, AND THAT EVERY BLOCK HANDS IT ON.**
One definition with code; statements and proofs, in the blocks' own decide-form.

The rule (Johnson/Desc/Sound/LedgerBeside.lean: besideP Pm X · clause_beside) lays a Bool X k beside Pm.shape k and asks of each clause one line: X is handed on at a yes.
  bookX ft k d   at the borders 0 … 12: the book is in order and the record counts as many roots as the book has trees (bookStepB, Johnson/Desc/Sound/BookInOrder.lean), and, from the border 3
                 on, the first fold's mask is noted. IT STANDS AT THE CHAIN's LAST BORDER 12 TOO (what is handed to the last chain is the promise at 12).
  bookX_iff      what it says.
  bookX_first    the chain's first record has it at the border 0.   bookX_front   the front block: 0 → 1.
  bookX_k14      K14's eight blocks: the i-th of blocks P: i + 1 → i + 2 (the chain's blocks 1 … 8), UNDER P.par.S.masksAhead = true.
  bookX_onGu     the test on G_u: 9 → 10.   bookX_onGomega   the test on G_omega: 10 → 11.   bookX_end   11 → 12, at one record.   bookX_twelve   what can be spent at 12.
  bookX_nine · bookX_ten   what the laws at the two seats spend of it (Johnson/Desc/K12/Coin/GameBook.lean's two promises).
Limits. ft IS ONE LETTER for K14's firstTree and the two places': premises where they meet. At the chain's own record St. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BookAtK14
import Johnson.Desc.K12.Coin.BookThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Sound (BookOrd BookStep bookStepB bookStep_iff)

/-- **The second Bool beside "shape k".** -/
def bookX (ft k : ℕ) (d : St) : Bool :=
  decide (12 < k) || (bookStepB ft d.book d.roots && (decide (k < 3) || d.loc.firstMask.isSome))

theorem bookX_iff (ft k : ℕ) (d : St) : bookX ft k d = true ↔
    (12 < k ∨ (BookStep ft d.book d.roots ∧ (k < 3 ∨ d.loc.firstMask.isSome = true))) := by
  unfold bookX
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bookStep_iff]

theorem bookX_first (ft : ℕ) (codes : Codes) (key : TableKey) : bookX ft 0 (first codes key) = true :=
  (bookX_iff ft 0 _).2 (.inr ⟨bookStep_first ft codes key, .inl (by omega)⟩)

theorem bookX_front (ft : ℕ) (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontBlock c).decide d rs gs = .ok d')
    (hX : bookX ft 0 d = true) : bookX ft 1 d' = true := by
  rw [bookStep_front c d d' rs gs h]
  rcases (bookX_iff ft 0 d).1 hX with h0 | ⟨h1, _⟩
  · omega
  · exact (bookX_iff ft 1 d).2 (.inr ⟨h1, .inl (by omega)⟩)

/-- **K14's eight blocks hand it on.** i: the block's place in blocks P, from 0. -/
theorem bookX_k14 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hm : P.par.S.masksAhead = true)
    (i : ℕ) (b : Block St Unit) (hb : [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d')
    (hX : bookX P.par.toGPar.firstTree (i + 1) d = true) :
    bookX P.par.toGPar.firstTree (i + 2) d' = true := by
  have hi : i < 8 := by
    have := (List.getElem?_eq_some_iff.1 hb).1
    simpa using this
  have hmem : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8] := List.mem_of_getElem? hb
  rcases (bookX_iff _ (i + 1) d).1 hX with h0 | ⟨h1, h2⟩
  · omega
  have k1 := bookStep_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hmem d d' rs gs h h1
  refine (bookX_iff _ (i + 2) d').2 (.inr ⟨k1, ?_⟩)
  rcases i with _ | _ | i
  · exact .inl (by omega)
  · obtain rfl : b2 = b := by simpa using hb
    exact .inr (mask_at_two P b1 b2 b3 b4 b5 b6 b7 b8 hbl hm d d' rs gs h)
  · have hb' : b ∈ [b3, b4, b5, b6, b7, b8] := by
      have : [b3, b4, b5, b6, b7, b8][i]? = some b := by simpa using hb
      exact List.mem_of_getElem? this
    rw [mask_kept P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb' d d' rs gs h]
    exact .inr (h2.resolve_left (by omega))

/-- **The test on G_u.** -/
theorem bookX_onGu (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs =
      .ok d') (hX : bookX p.nums.firstTree 9 d = true) : bookX p.nums.firstTree 10 d' = true := by
  rcases (bookX_iff _ 9 d).1 hX with h0 | ⟨h1, h2⟩
  · omega
  obtain ⟨k1, k2⟩ := VerifiableInference.Desc.K12.Coin.onGu_bookStep p he ha d d' rs gs h h1
  refine (bookX_iff _ 10 d').2 (.inr ⟨k1, .inr ?_⟩)
  rw [k2]
  exact h2.resolve_left (by omega)

/-- **The test on G_omega.** -/
theorem bookX_onGomega (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs
      gs = .ok d') (hX : bookX p.nums.firstTree 10 d = true) :
    bookX p.nums.firstTree 11 d' = true := by
  rcases (bookX_iff _ 10 d).1 hX with h0 | ⟨h1, h2⟩
  · omega
  obtain ⟨k1, k2⟩ := VerifiableInference.Desc.K12.Coin.onGomega_bookStep p he ha d d' rs gs h h1
  refine (bookX_iff _ 11 d').2 (.inr ⟨k1, .inr ?_⟩)
  rw [k2]
  exact h2.resolve_left (by omega)

/-- Past the chain's end, at one record: it stands at the chain's last border too (what is handed to the last chain). -/
theorem bookX_end (ft : ℕ) (d : St) (h : bookX ft 11 d = true) : bookX ft 12 d = true := by
  rcases (bookX_iff ft 11 d).1 h with h0 | ⟨h1, h2⟩
  · omega
  · exact (bookX_iff ft 12 d).2 (.inr ⟨h1, .inr (h2.resolve_left (by omega))⟩)

/-- What can be spent of it at the chain's last border. -/
theorem bookX_twelve (ft : ℕ) (d : St) (h : bookX ft 12 d = true) :
    BookStep ft d.book d.roots ∧ d.loc.firstMask.isSome = true := by
  rcases (bookX_iff ft 12 d).1 h with h0 | ⟨h1, h2⟩
  · omega
  · exact ⟨h1, h2.resolve_left (by omega)⟩

/-- What the law at Seat.onGu spends of it. -/
theorem bookX_nine (ft : ℕ) (d : St) (h : bookX ft 9 d = true) :
    d.loc.firstMask.isSome = true ∧ BookOrd ft d.book := by
  rcases (bookX_iff ft 9 d).1 h with h0 | ⟨h1, h2⟩
  · omega
  · exact ⟨h2.resolve_left (by omega), h1.2⟩

/-- What the law at Seat.onGomega spends of it. -/
theorem bookX_ten (ft : ℕ) (d : St) (h : bookX ft 10 d = true) : BookStep ft d.book d.roots := by
  rcases (bookX_iff ft 10 d).1 h with h0 | ⟨h1, _⟩
  · omega
  · exact h1

/-- A control: a record with a root that its book lacks has it at no border up to 12. -/
theorem bookX_fails (ft k : ℕ) (hk : k ≤ 12) (codes : Codes) (key : TableKey) :
    bookX ft k { first codes key with roots := 1 } = false := by
  cases hX : bookX ft k { first codes key with roots := 1 } with
  | false => rfl
  | true =>
    rcases (bookX_iff ft k _).1 hX with h0 | ⟨h1, _⟩
    · omega
    · exact absurd h1 (VerifiableInference.Desc.Sound.not_step_roots ft)

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.bookX_k14
#print axioms Desc.K14.Law.Fence.bookX_onGu
#print axioms Desc.K14.Law.Fence.bookX_onGomega
#print axioms Desc.K14.Law.Fence.bookX_nine
#print axioms Desc.K14.Law.Fence.bookX_twelve
#print axioms Desc.K14.Law.Fence.bookX_fails
