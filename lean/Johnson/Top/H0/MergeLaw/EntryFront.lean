-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/EntryFront.lean: what the merge's ties ask of the verifier's state IN FRONT
of the merge, beside the table's condition, gathered in one structure; and what follows behind its
accepting step. A structure, and theorems with their proofs.

Why. The third tie (`merge_t3`, TieThreeFour.lean) takes two facts on the state behind the merge,
and the second tie owes the public item `hasRow` there. The merge's step leaves what these facts
read. So all three follow from facts on the state in front: the place at which a fact on the states
that the verifier reaches can be spent.

Main names:
  `entry_within`: the index masks' ledger has an entry to give, inside its message's mask table:
    where it is not closed and has n entries left, n not 0 (`leftIsB`,
    Johnson/Top/H0/Walk/FrameEntriesDefs.lean), and is the ledger of k takes since it was made
    (`LedgerAt`, with `takeEntry_within`:
    Johnson/Desc/K13/Law/LedgerWithin.lean).
  `MergeFront own xM R ni s`: FOUR FACTS on the state s: `MaskAt` (MaskRow.lean); the ledger is not
    closed and has an entry left; it is the ledger of some number of takes; ni is the size of that
    message's mask table.
  `MergeFront.he`, `MergeFront.maskBehind`: the premises he and hMb of `merge_t3`.
  `MergeFront.hasRow`: the public item `hasRow` behind, at one claim: with a closed test on the
    planner's numbers beside the accepting step: `pendAllB` (PendOfAll.lean):
    `pendB` (RowReturns.lean) accepts at every unit of the layout. (That the state's claim names a
    unit follows from the accepting step alone: so it is no fact on the state in front.)

Limits. `MergeFront` is shown at no state. Tests with code: `maskAtB` for the first field, `leftIsB`
for the second; the third and the fourth are stated without one here. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.OffRecord
import Johnson.Top.H0.Walk.FrameEntriesDefs
import Johnson.Desc.K13.Law.LedgerWithin
import Johnson.Top.H0.MergeLaw.MaskRow
import Johnson.Top.H0.MergeLaw.PendOfAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open VerifiableInference.Desc.K13.Law (LedgerAt takeEntry_within)
open Johnson.Desc.First.Walk.Tied (leftIsB)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **The index masks' ledger has an entry to give, inside its message's mask table**: where it is
not closed and has n entries left, n not 0, and is the ledger of k takes since it was made. -/
theorem entry_within {s : S} {n k : ℕ} (hl : leftIsB n s = true) (hn : 0 < n)
    (hk : LedgerAt s.st s.out.indexMasks k) :
    ∃ c, c < OnBytes.Means.tableSize s.st s.out.indexMasks .mask ∧ EntryAt s c := by
  unfold leftIsB at hl
  cases e : Johnson.Desc.First.Walk.Law.ledgerAt s with
  | none => simp [e] at hl
  | some l =>
    rw [e] at hl
    simp only [Option.any_some, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hl
    have ht : (VerifiableInference.Desc.First.Pend.takeEntry l).isSome = true := by
      unfold VerifiableInference.Desc.First.Pend.takeEntry
      have h0 : 0 < l.left := by rw [hl.2]; exact hn
      simp [hl.1, h0]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ht
    exact ⟨x.1, (takeEntry_within hk e hx).1, l, x.2, e, hx⟩

/-- **WHAT THE MERGE's TIES ASK OF THE VERIFIER's STATE IN FRONT, beside the table's condition**:
four facts. n: how many entries the index masks' ledger has left; k: how many were taken since it
was made; ni: the size of that message's mask table. -/
structure MergeFront (own : List (ℕ × ℕ)) (xM : VerifiableInference.Desc.Sound.Mem) (R ni : ℕ)
    (s : S) : Prop where
  /-- the two readings of the segment's mask row meet -/
  mask : MaskAt own xM R s
  /-- the index masks' ledger is not closed and has an entry left -/
  left : ∃ n, 0 < n ∧ leftIsB n s = true
  /-- it is the ledger of some number of takes since it was made -/
  made : ∃ k, LedgerAt s.st s.out.indexMasks k
  /-- the size of that message's mask table -/
  size : OnBytes.Means.tableSize s.st s.out.indexMasks .mask = ni

variable {P : HeadMergeP} {lin : Params.LinShape} {own : List (ℕ × ℕ)}
  {xM : VerifiableInference.Desc.Sound.Mem} {R ni : ℕ} {s s' : S} {rs : List Fmt.RoundView}

/-- **Behind the merge's accepting step**: the premise he of `merge_t3`. -/
theorem MergeFront.he (F : MergeFront own xM R ni s) (h : headMergeDecide P s rs = .ok s') :
    ∃ c, c < ni ∧ EntryAt s' c := by
  obtain ⟨n, hn, hl⟩ := F.left
  obtain ⟨k, hk⟩ := F.made
  obtain ⟨c, hc, he⟩ := entry_within hl hn hk
  exact ⟨c, by rw [← F.size]; exact hc, ((reads_stay P h).2 c).1 he⟩

/-- The premise hMb of `merge_t3`. -/
theorem MergeFront.maskBehind (F : MergeFront own xM R ni s)
    (h : headMergeDecide P s rs = .ok s') : MaskAt own xM R s' :=
  maskAt_behind P h F.mask

/-- **The public item `hasRow` behind**, at one claim: with the closed test on the planner's
numbers: the pending row's text returns at claims of zeros on every unit of the layout. -/
theorem MergeFront.hasRow (F : MergeFront own xM R ni s)
    (h : headMergeDecide P s rs = .ok s') (hB : pendAllB P.lay lin = true) :
    Johnson.Desc.First.Walk.Law.hasRow P.lay 1 lin s' = true := by
  obtain ⟨c, _, he⟩ := F.he h
  exact merge_makes_row_of_all P h lin hB ⟨c, he⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.MergeFront.he
#print axioms VerifiableInference.Desc.First.MergeLaw.MergeFront.maskBehind
#print axioms VerifiableInference.Desc.First.MergeLaw.MergeFront.hasRow
#print axioms VerifiableInference.Desc.First.MergeLaw.entry_within
