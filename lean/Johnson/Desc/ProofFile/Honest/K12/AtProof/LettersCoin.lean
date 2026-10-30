-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/LettersCoin.lean: what two lendings of the frame hand,
where two entries of a book have one owner and one start: one coin at each number below both
counts. General in the book, the parts and the reader of coins.

  cut_same          two cuts of one purse at one start agree below both counts
  carried_one_coin  two carried entries of one owner and start hand one coin
  spent_one_coin    a spent entry and a carried entry of one owner and start hand one coin

By what. carried_is_cut, spent_is_cut (HandedW.lean); cut_at (K12/CutOfBook.lean).

Limits.
- That the two parts are lent at one reader of coins is in the statement: look is one letter.
- That the frame lends is a premise, twice.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HandedW
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light (cut_at)

/-- **Two cuts of one purse at one start agree below both counts.** -/
theorem cut_same {d : Due} (c : Cs d) (a n n' : Due) {x : Cs n} {x' : Cs n'}
    (h : c.cut a n = some x) (h' : c.cut a n' = some x') (i : Nat) (hi : i < n.e)
    (hi' : i < n'.e) : (stretchOf x).e i = (stretchOf x').e i := by
  rw [cut_at c a n x h i hi, cut_at c a n' x' h' i hi']

variable {V W X V' W' X' : Type} {B : ProverCoinCounts} {rows rows' : List (Addr × Due)}
  {look : Addr → (d : Due) × Cs d} {a a' : Addr} {p : Part V W X} {p' : Part V' W' X'}
  {y : p.Coins} {y' : p'.Coins} {n n' : Nat} {e e' : Ahead}

/-- **Two carried entries of one owner and one start hand one coin.** -/
theorem carried_one_coin (hl : lendPart B rows look a p = .ok y)
    (hl' : lendPart B rows' look a' p' = .ok y') (he : (carryE B a)[n]? = some e)
    (he' : (carryE B a')[n']? = some e') (ho : e.owner = e'.owner) (hs : e.start = e'.start)
    (i : Nat) (hi : i < e.count.e) (hi' : i < e'.count.e) :
    (stretches p.carries y.2.2 n).e i = (stretches p'.carries y'.2.2 n').e i := by
  obtain ⟨x, hx, hst⟩ := carried_is_cut hl he
  obtain ⟨x', hx', hst'⟩ := carried_is_cut hl' he'
  rw [hst, hst']
  rw [ho, hs] at hx
  exact cut_same _ _ _ _ hx hx' i hi hi'

/-- **A spent entry and a carried entry of one owner and one start hand one coin.** -/
theorem spent_one_coin (hl : lendPart B rows look a p = .ok y)
    (hl' : lendPart B rows' look a' p' = .ok y') (he : (spentE B a)[n]? = some e)
    (he' : (carryE B a')[n']? = some e') (ho : e.owner = e'.owner) (hs : e.start = e'.start)
    (i : Nat) (hi : i < e.count.e) (hi' : i < e'.count.e) :
    (stretches p.spends y.2.1 n).e i = (stretches p'.carries y'.2.2 n').e i := by
  obtain ⟨x, hx, hst⟩ := spent_is_cut hl he
  obtain ⟨x', hx', hst'⟩ := carried_is_cut hl' he'
  rw [hst, hst']
  rw [ho, hs] at hx
  exact cut_same _ _ _ _ hx hx' i hi hi'

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.cut_same
#print axioms ProofFile.Honest.K12.AtProof.carried_one_coin
#print axioms ProofFile.Honest.K12.AtProof.spent_one_coin
