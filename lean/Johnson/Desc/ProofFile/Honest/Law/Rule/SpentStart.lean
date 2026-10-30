-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/SpentStart.lean: THE PLAN's SIDE JOINED TO THE BOOK's: a
segment's spending entry, as the book's maker lays it (Honest/BookEntries.lean: `segmentWants`,
`Want.entry`; Honest/BookStart.lean: `startOf`, `segment_start`), hands its spender the stretch of
the mask row's sender's coins that begins at `startOf` and has at most as many coins as the stretch
counts (fewer where the sender's coins end first). With `sliceE`, `spentAt`, `rowSpent`
(Law/Rule/Spent.lean).

`slice_at_start` an entry's run, in the plan's terms `rowSpent_one` a row of one part with one
spending entry spends that entry's run `take_two`, `rowSpent_two` two runs that follow one another
in one owner's coins are one stretch

Limits. THAT THE BOOK's SPENDING ENTRIES WHICH NAME AN ADDRESS ARE THE PLAN's IS A PREMISE HERE (in
the form: the list `spentE Bk a` is given). The end values' stretches are left out, as in
Honest/BookStart.lean. Rows of one part and of two. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookStart
import Johnson.Desc.ProofFile.Honest.Law.Rule.Spent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type} (look : Addr → (d : Due) × Cs d)

theorem slice_at_start {bs : List (Block S Cl)} {l : Nat} {row idx : MsgAt} {merges : List Addr}
    {t : Nat} {w : Want} (hn : ((segmentParts bs l).map (·.addr)).Nodup)
    (h : w ∈ (segmentWants bs l row idx merges t).1) (hu : w.use ≠ "ends") :
    ∃ s, startOf bs l row w.spender = some s ∧
      sliceE look w.entry = ((coinsE (look row.owner).2).drop s).take w.count := by
  obtain ⟨ho, hs, hc⟩ := segment_start hn h hu
  refine ⟨_, hs, ?_⟩
  unfold sliceE
  rw [ho, hc]

theorem rowSpent_one {Bk : ProverCoinCounts} {p : Place} {e : Ahead} (h : spentE Bk ⟨p, 0⟩ = [e]) :
    rowSpent Bk look p 1 0 = sliceE look e := by
  show spentAt Bk look ⟨p, 0⟩ ++ [] = _
  unfold spentAt
  rw [h, List.append_nil]
  exact List.append_nil _

/-- Two stretches in a row are one. -/
theorem take_two {α : Type} (l : List α) (s a b : Nat) :
    (l.drop s).take a ++ (l.drop (s + a)).take b = (l.drop s).take (a + b) := by
  rw [List.take_add, List.drop_drop]

theorem rowSpent_two {Bk : ProverCoinCounts} {p : Place} {e f : Ahead} (h0 : spentE Bk ⟨p, 0⟩ = [e])
    (h1 : spentE Bk ⟨p, 1⟩ = [f]) (ho : f.owner = e.owner)
    (hs : f.start.e = e.start.e + e.count.e) :
    rowSpent Bk look p 2 0 =
      ((coinsE (look e.owner).2).drop e.start.e).take (e.count.e + f.count.e) := by
  show spentAt Bk look ⟨p, 0⟩ ++ (spentAt Bk look ⟨p, 1⟩ ++ []) = _
  unfold spentAt
  rw [h0, h1, List.append_nil]
  show (sliceE look e ++ []) ++ (sliceE look f ++ []) = _
  rw [List.append_nil, List.append_nil]
  unfold sliceE
  rw [ho, hs]
  exact take_two _ _ _ _

end ProofFile.Honest

#print axioms ProofFile.Honest.slice_at_start
#print axioms ProofFile.Honest.rowSpent_one
#print axioms ProofFile.Honest.take_two
#print axioms ProofFile.Honest.rowSpent_two
