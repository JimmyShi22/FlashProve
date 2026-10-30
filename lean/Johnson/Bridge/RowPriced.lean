-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/RowPriced.lean: ONE COMPARISON FOR EVERY ROUND OF A PLAN: at an entry of a plan and a
count: a yes gives that the count is at most 2^-128 of the written verifier messages of EVERY
written round that has that entry and a kind that fits (seeds where the caller says so, else any but
seeds and sealed), whatever its bytes, roots, rows and items.

This file rests on Cb/Bridge/CodeListRSProved.lean through its imports, and so on the files under
ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15). Its own proofs unfold definitions and call
`below_of_num` (Johnson/Bridge/BasePriced.lean).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Why. The places of this folder say their clauses on counts of a written round that IS one of the
format's own rounds (`IsRd d (Fmt.M1.rTwo nb)` and the like): the whole entry is asked, its bytes,
roots and rows too. A plan's own entry may differ there. `RoundBelow` reads of an entry only what is
drawn, and the work. So here the comparison is made at the plan's own entry.

Main names:
  `rowVals e seed`: the number of typed values of a round with the entry e. `KindFits seed k`: the
    kind seeds where the round draws a seed; else any kind but seeds and sealed.
  `rowB e seed c`: the comparison of `below_of_num`, with its side conditions.
  `rowB_below`: a yes gives `RoundBelow c d` at 2^-128 in every written round d with d.entry = e
    whose kind fits. `rowOkB`, `rowOkB_below`: the same, with the count 0 let through in a round of
    any kind (`roundBelow_zero`).

Limits: no place and no plan is written here. THE COMPARISON TAKES ANY COUNT: that a count is a
round's own, at what that round's block draws, is asked by whoever calls it
(Johnson/Bridge/Slots.lean [not in this library] holds an entry's draws against a slot). Of the 128
bits the entry's bits
of work are proof of work, and where no element is drawn the comparison sets no cap on them. One
round's share; no sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.TestsAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb _root_.Run
open scoped ENNReal

/-! ## One comparison for every round -/

/-- The number of typed values of a round with the entry e: of the kind seeds, or of any kind but
seeds and sealed. -/
def rowVals (e : Fmt.Entry) : Bool → ℕ
  | true => nVals (Fmt.dsOf e .seeds)
  | false => nVals (Fmt.dsOf e .elems)

/-- The kind of a written round fits. -/
def KindFits : Bool → Fmt.Kind → Prop
  | true, k => k = .seeds
  | false, k => k ≠ .seeds ∧ k ≠ .sealed

theorem rowVals_eq (e : Fmt.Entry) :
    ∀ {seed : Bool} {k : Fmt.Kind}, KindFits seed k → nVals (Fmt.dsOf e k) = rowVals e seed
  | true, _, h => by
    have h' : _ = Fmt.Kind.seeds := h
    subst h'
    rfl
  | false, k, h => by
    show _ = nVals (Fmt.dsOf e .elems)
    rw [nVals_dsOf e k h.1 h.2, nVals_dsOf e .elems (by decide) (by decide)]

/-- The comparison of `below_of_num`, with its side conditions, at an entry and a count. -/
def rowB (e : Fmt.Entry) (seed : Bool) (c : ℕ) : Bool :=
  decide (e.logN ≤ 64) && decide (e.drawNZ ≤ e.drawE) &&
    (Nat.beq e.drawE 0 || decide (e.work + 66 ≤ 128)) && decide (0 < rowVals e seed) &&
    decide (c * 2 ^ 193 + 3 * (e.drawE + e.drawNZ) * rowVals e seed ≤
      rowVals e seed * 2 ^ (e.work + 65))

/-- **A yes: the count is at most 2^-128 of the round's written verifier messages.** -/
theorem rowB_below {e : Fmt.Entry} {seed : Bool} {c : ℕ} (h : rowB e seed c = true) (d : PQ.RD)
    (hd : d.entry = e) (hk : KindFits seed d.kind) : RoundBelow c d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  subst hd
  simp only [rowB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hlog, hnz⟩, hw⟩, h0⟩, hc⟩ := h
  refine below_of_num d hlog hnz (fun hE => ?_) c _ (rowVals_eq d.entry hk) h0 hc
  rcases hw with hw | hw
  · exact absurd (Nat.eq_of_beq_eq_true hw) hE
  · exact hw

/-- The count 0 meets the clause in every round. -/
theorem roundBelow_zero (d : PQ.RD) (εs : ℝ≥0∞) : RoundBelow 0 d εs := by
  unfold RoundBelow
  simp

/-- The count is 0, or the comparison says yes. -/
def rowOkB (e : Fmt.Entry) (seed : Bool) (c : ℕ) : Bool := Nat.beq c 0 || rowB e seed c

/-- **A yes**: in every written round with that entry: of any kind where the count is 0, else of a
kind that fits. -/
theorem rowOkB_below {e : Fmt.Entry} {seed : Bool} {c : ℕ} (h : rowOkB e seed c = true) (d : PQ.RD)
    (hd : d.entry = e) (hk : c = 0 ∨ KindFits seed d.kind) :
    RoundBelow c d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rcases hk with hc | hk
  · subst hc
    exact roundBelow_zero d _
  · rcases Bool.or_eq_true_iff.1 h with h0 | h1
    · rw [Nat.eq_of_beq_eq_true h0]
      exact roundBelow_zero d _
    · exact rowB_below h1 d hd hk

end Johnson.Bridge

#print axioms Johnson.Bridge.rowB_below
#print axioms Johnson.Bridge.rowOkB_below
