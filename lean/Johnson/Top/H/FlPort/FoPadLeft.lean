-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPadLeft.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPadLeft.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  pad_left, pad_left_chain
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Filled, Later, PadLeft, Same, Sized, Stretch, leaves, owed3, same_fields, stretch_skip, took
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadLeft
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoPadCut
import Johnson.Top.H.FlPort.PscRounds

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open OnBytes OnBytes.Model OnBytes.PscRun

/-- What a run of lkPad leaves in the state. -/
theorem pad_left {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (nA nB : ℕ)
    (sA : Stretch (owed3 F) M.F7 nA)
    (sB : Stretch (took M.F7 (1 + 2 * (M.h pub).d + 5)) M.G8 nB)
    (hL : Later (owed3 F) M.G8) (hZ : Sized M.G8) (hlv : M.lv.first = M.F7.next) :
    PadLeft (M.h pub) F F' g := by
  obtain ⟨nL, hnL⟩ : ∃ nL, nL = 1 + 2 * (M.h pub).d + 5 := ⟨_, rfl⟩
  rw [← hnL] at sB
  have h7 : M.F7.next = F.next + nA := sA.next
  have h8 : M.G8.next = F.next + nA + nL + nB := by
    rw [sB.next]
    show M.F7.next + nL + nB = _
    rw [h7]
  have hel : Forest.elems (M.h pub) = nA + nL + nB := by
    have := P.slots
    omega
  have hfirst : g.leaves.first = F.next + nA := by
    rw [P.heard]
    show M.lv.first = _
    rw [hlv, h7]
  have fA : ∀ j, Filled M.F7 j ↔ Filled F j ∨ (F.next ≤ j ∧ j < F.next + nA) := sA.filled
  have fB : ∀ j, Filled M.G8 j ↔
      Filled M.F7 j ∨ (F.next + nA + nL ≤ j ∧ j < F.next + nA + nL + nB) := by
    intro j
    have := sB.filled j
    rw [show (took M.F7 nL).next = F.next + nA + nL by show M.F7.next + nL = _; rw [h7]] at this
    exact this
  have oA : ∀ j, (j < F.next ∨ F.next + nA ≤ j) → M.F7.vp.getD j zeroE = F.vp.getD j zeroE ∧
      M.F7.mf.getD j zeroE = F.mf.getD j zeroE := sA.out
  have oB : ∀ j, (j < F.next + nA + nL ∨ F.next + nA + nL + nB ≤ j) →
      M.G8.vp.getD j zeroE = M.F7.vp.getD j zeroE ∧
        M.G8.mf.getD j zeroE = M.F7.mf.getD j zeroE := by
    intro j hj
    refine sB.out j ?_
    rw [show (took M.F7 nL).next = F.next + nA + nL by show M.F7.next + nL = _; rw [h7]]
    exact hj
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := same_fields sA.same
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := same_fields sB.same
  rw [P.fork]
  refine
    { next := P.slots
      fit := hZ
      keep := fun j hj => hL.keep j hj
      filled := ?_
      leaves := ?_
      beyond := ?_
      owed := b0.trans a0
      owedAt := ?_
      rest := ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
        b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10⟩ }
  · intro j h1 h2 h3
    rw [hfirst, ← hnL] at h3
    rw [hel] at h2
    by_cases hA : j < F.next + nA
    · exact (fB j).2 (Or.inl ((fA j).2 (Or.inr ⟨h1, hA⟩)))
    · exact (fB j).2 (Or.inr ⟨by omega, by omega⟩)
  · intro j h1 h2
    rw [hfirst] at h1 h2
    rw [← hnL] at h2
    refine ⟨?_, ((oB j (Or.inl (by omega))).1).trans (oA j (Or.inr h1)).1,
      ((oB j (Or.inl (by omega))).2).trans (oA j (Or.inr h1)).2⟩
    rw [fB, fA]
    constructor
    · rintro ((hj | hj) | hj)
      · exact hj
      · omega
      · omega
    · exact fun hj => Or.inl (Or.inl hj)
  · intro j h1
    rw [hel] at h1
    rw [fB, fA]
    constructor
    · rintro ((hj | hj) | hj)
      · exact hj
      · omega
      · omega
    · exact fun hj => Or.inl (Or.inl hj)
  · rw [P.heard]
    refine ⟨rfl, ?_, ?_⟩
    · show (F.owed.push _).size = _
      rw [Array.size_push]
    · show ((F.owed.push _).push _).size = _
      rw [Array.size_push, Array.size_push]

/-- The same, from what the five stretches hand on one by one: the draws turn nothing; the tie and
the two walks are stretches; the lines on the leaves and the bits leave the leaves' slots free. -/
theorem pad_left_chain {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (n5 n6 n7 a b : ℕ)
    (h4 : M.F4 = owed3 F) (s5 : Stretch M.F4 M.F5 n5) (s6 : Stretch M.F5 M.F6 n6)
    (s7 : Stretch M.F6 M.F7 n7) (l5 : Later M.F4 M.F5) (l6 : Later M.F5 M.F6)
    (l7 : Later M.F6 M.F7) (l8 : Later M.F7 M.G8) (ha : a = 1 + 2 * (M.h pub).d + 5)
    (same : Same (took M.F7 (a + b)) M.G8)
    (filled : ∀ j, Filled M.G8 j ↔ Filled M.F7 j ∨ (M.F7.next + a ≤ j ∧ j < M.F7.next + a + b))
    (others : ∀ j, (j < M.F7.next + a ∨ M.F7.next + a + b ≤ j) →
      M.G8.vp.getD j zeroE = M.F7.vp.getD j zeroE ∧ M.G8.mf.getD j zeroE = M.F7.mf.getD j zeroE)
    (hZ : Sized M.G8) (hlv : M.lv.first = M.F7.next) : PadLeft (M.h pub) F F' g := by
  rw [h4] at s5 l5
  exact pad_left P (n5 + n6 + n7) b ((s5.trans s6).trans s7) (stretch_skip ha same filled others)
    (((l5.trans l6).trans l7).trans l8) hZ hlv


end Fo.Tp
