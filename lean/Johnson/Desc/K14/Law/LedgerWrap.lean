-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerWrap.lean: THE WRAP IN WHICH A DESCRIPTION's PIECES HOLD THE SHARED
CHAIN's BLOCKS (the test "every word shown is below the prime" in front; the lift to the pair of
what was handed and the chain's own record), OPENED AT A YES, ON THE SAME ROUNDS AND COLUMNS: it
    pays the
first premise (hz, hb) of the clauses of "LIN zeta" and "SPLIT" at the ledger
(Johnson/Desc/K14/Law/LedgerZeta.lean, LedgerSplit.lean).

  wrap_decide     a yes of the wrapped block at x, to x': a yes of the block itself at x.2, to x'.2,
                  on the same rounds and columns; and x'.1 = x.1.
  zeta_wrapped, split_wrapped   so hz and hb, for a block b₀ at any type of claims that decides as
                  the kind's own seventh | eighth block does.
What is not claimed. That a description seats the kind's blocks so (b₀ decides as b7 | b8) is a
premise: a fact on the description's text. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.GoodFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block viewWordsBelowPrime)
open VerifiableInference.Desc.Sound (below)

/-- **The wrap, opened at a yes.** -/
theorem wrap_decide {U σ Cl : Type} (b : Block σ Cl) (x x' : U × σ) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.lift Prod.snd (fun x s => (x.1, s)) (below b)).decide x rs gs = .ok x') :
    b.decide x.2 rs gs = .ok x'.2 ∧ x'.1 = x.1 := by
  have hd : ((below b).decide x.2 rs gs).map (fun s => (x.1, s)) = .ok x' := h
  cases hB : (below b).decide x.2 rs gs with
  | error e => rw [hB] at hd; cases hd
  | ok s =>
    rw [hB] at hd
    cases hd
    have hB' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then
        b.decide x.2 rs gs else .error "a word is not below the prime") = .ok s := hB
    split at hB'
    · exact ⟨hB', rfl⟩
    · cases hB'

/-- hz of "LIN zeta"'s clause. -/
theorem zeta_wrapped {U Cl : Type} (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b₀ : Block St Cl)
    (hs : ∀ d rs gs, b₀.decide d rs gs = b7.decide d rs gs) :
    ∀ (t : U × St) rs gs t',
      (Block.lift Prod.snd (fun x s => (x.1, s)) (below b₀)).decide t rs gs = .ok t' →
      linZeta t.2 rs = some t'.2 := fun t rs gs t' h =>
  zeta_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _
    ((hs _ _ _).symm.trans (wrap_decide b₀ t t' rs gs h).1)

/-- hb of "SPLIT"'s clause. -/
theorem split_wrapped {U Cl : Type} (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b₀ : Block St Cl)
    (hs : ∀ d rs gs, b₀.decide d rs gs = b8.decide d rs gs) :
    ∀ (t : U × St) rs gs t',
      (Block.lift Prod.snd (fun x s => (x.1, s)) (below b₀)).decide t rs gs = .ok t' →
      split P.par t.2 rs = some t'.2 := fun t rs gs t' h =>
  decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _
    ((hs _ _ _).symm.trans (wrap_decide b₀ t t' rs gs h).1)

end Desc.K14.Law
