-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/BookFitTold.lean: THE TABLE's TEST bookFit SAYS YES AT THE NUMBERS THAT ARE
FILLED OFF WHAT THE BLOCKS TELL, BY THAT FILLING's OWN MAKE: for every table of numbers N and
every telling: `bookFit (N.withTold ps told) ps told = true`, WHERE EACH PLACE STANDS ONCE IN THE
LIST. Three theorems. A file beside the table: it turns nothing of it.
Why. Several kinds' laws at the first chain's table take `bookFit N ps told = true` as a premise
(so does the tie of a piece's base to the table's number: Johnson/Road/K4/PieceBase.lean). At the
meant N, `(…).withTold ps told` (Johnson/Desc/First/BookNumbers.lean), that file calls it shown BY
EVALUATION ALONE, at one honest proof a size (that file's Limit (3)). It needs no run: `withTold`
lays at a place the very sum that the test compares with, looked up by the place's number in the
list (`borderOf`): the two agree as soon as the look-up finds the right number: that is: each
place stands once.
  `idxOf_getElem_nodup`: in a list without a repeat the first standing of the k-th member is k.
  `borderOf_getElem`: so `borderOf ps ps[k]? = k` at every border k, the last among them.
  `bookFit_withTold`: **the test's yes**, for all N and all told.
Silly members. At the empty list the one border is the last: both sides are the empty sum.
Limits. (1) `ps.Nodup` IS ASKED, AND THE THEOREM IS FALSE WITHOUT IT (ps := [p, p], told := [[o],
[]]: at border 1 the look-up finds 0). It is BookNumbers.lean's own Limit (2). At the table's own
list it is a theorem, general in the segments' sorts: `ProofFile.Law.flatPlaces_nodup`
(Johnson/Desc/ProofFile/Law/KindPlaces.lean). (2) AT THIS
N THE TEST COMPARES A THING WITH ITSELF: ITS YES IS BY MAKE AND CARRIES NO CONTENT: the test bites
where N comes from elsewhere (a plan's numbers). So a law that takes `bookFit` as a premise loses
that premise at this N, and no debt hides in it. WHERE THE CONTENT LIES: in `blocksOk` (the roots
that a block declares are the oracles that it tells: there the data's trees meet the telling); in
the promise's clause `bookAt`, which must ride past every block (at a block that sends, its kind's
law owes it); in `fenceFit`. (3) Nothing on `fenceFit`. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- In a list without a repeat the first standing of the k-th member is k. -/
theorem idxOf_getElem_nodup : ∀ (l : List Place), l.Nodup → ∀ (k : Nat) (h : k < l.length),
    l.idxOf l[k] = k
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => by simp
  | a :: l, hn, k + 1, h => by
    have hn' := List.nodup_cons.1 hn
    have hk : k < l.length := Nat.lt_of_succ_lt_succ h
    have hne : a ≠ l[k] := fun e => hn'.1 (e ▸ List.getElem_mem hk)
    have hb : (a == l[k]) = false := beq_eq_false_iff_ne.2 hne
    rw [List.getElem_cons_succ, List.idxOf_cons, hb, idxOf_getElem_nodup l hn'.2 k hk]
    rfl

/-- The look-up by place finds the border's own number, at every border, the last among them. -/
theorem borderOf_getElem (ps : List Place) (hn : ps.Nodup) (k : Nat) (hk : k ≤ ps.length) :
    borderOf ps ps[k]? = k := by
  rcases Nat.lt_or_eq_of_le hk with h | h
  · rw [List.getElem?_eq_getElem h]
    exact idxOf_getElem_nodup ps hn k h
  · subst h
    rw [List.getElem?_eq_none (Nat.le_refl _)]
    rfl

/-- **The test's yes at the numbers that are filled off the telling.** -/
theorem bookFit_withTold (N : Numbers) (ps : List Place) (told : List (List Oracle))
    (hn : ps.Nodup) : bookFit (N.withTold ps told) ps told = true := by
  unfold bookFit
  refine List.all_eq_true.2 fun k hk => ?_
  have e := borderOf_getElem ps hn k (Nat.le_of_lt_succ (List.mem_range.1 hk))
  show (treesTold told (borderOf ps ps[k]?) == treesTold told k &&
    msgsTold told (borderOf ps ps[k]?) == msgsTold told k) = true
  rw [e]
  simp

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.idxOf_getElem_nodup
#print axioms VerifiableInference.Desc.First.borderOf_getElem
#print axioms VerifiableInference.Desc.First.bookFit_withTold
