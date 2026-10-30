-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/OpenedKeeps.lean: THE FRAME's HALF AT THE 25 LINKS' FIRST
HEARING MEMBERS. Such a member is a lot's own sub-protocol with the frame's «opened» joined behind
it (the library's `IM.Joined`). `keeps_joined` (Honest/Law/NoHouse/Join.lean) takes a clause from
each half. Here the frame's: `keepsOpened`; its payer at all four arms of the library's row of
frames at once (`keepsOpened_of`); so the joined member's clause with the frame's half paid
(`keeps_joined_opened`); and what readers of the state get of it.

WHAT THIS IS. A definition that fills half of a letter of the thread and that whoever rides past
such a member spends; lemmas: calls of the library's `IM.frames_arms` (Johnson/IMR/FrameSeat.lean)
and `openedZeroGives`, `openedAttGives`, `openedLayGives` (Johnson/Top/H0/Walk/FrameTiedRec.lean).
None of the library's goals. THE LIBRARY's KIN: `OpenedKeeps` and its `opened_keeps`
(Johnson/Top/H0/Walk/FrameOpened.lean) say at every row: the statement, the book, the number of
roots, the count of rows that is owed, the mark and the request are as they were. THEY DO NOT SPEAK
OF WHAT GOES ON TO THE LATER CHAINS (`out`), which whoever rides past such a member reads: that, the
mark behind, and, in its second arm, the state of the calls, are what `keepsOpened` adds;
`keepsOpened_lib` gives the library's clause back.

  `keepsOpened`, `keepsOpened_of`, `keeps_joined_opened`
  `keepsOpened_lib`, `keepsOpened_st`, `keepsOpened_book`, `keepsOpened_reply`,
  `keepsOpened_pending`, `keepsOpened_out`

Limits. What «opened» LAYS (where the chain stands behind it, the link's number, the ledger, the
range proof's state) is in the library's three laws and is not taken over here. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Join
import Johnson.IMR.FrameSeat
import Johnson.Top.H0.Walk.FrameOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes OpenedLeaves OpenedKeeps keeps_of_leaves openedZeroGives
  openedAttGives openedLayGives)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open ProofFile (Cl)

/-- **WHAT THE FRAME's «OPENED» KEEPS AT LINK l**: the frame's half of the clause of keeps at a
link's first hearing member (the second clause of `keeps_joined`, Honest/Law/NoHouse/Join.lean). m:
the state behind the lot's own sub-protocol; t: behind «opened». No mark behind; and EITHER «opened»
hands the state on, OR the library's `OpenedLeaves` (Johnson/Top/H0/Walk/FrameGives.lean: the state
of the calls, the statement, the book, the number of roots, the count of rows that is owed, the mark
and the request are as they were; the open segment's copy of the state of the calls is laid); and
what goes on to the later chains is as it was, whole, but at link 0, which lays the index masks'
message. The payer `keepsOpened_of` pays the first arm at the head's link and the second at the
others; THE CLAUSE ITSELF DOES NOT SAY WHICH ARM HOLDS AT WHICH LINK: at every l it can hold by the
first. -/
def keepsOpened (l : Nat) (m t : S) : Prop :=
  t.failed = none ∧ (t = m ∨ (OpenedLeaves m t ∧
    (∃ im, t.out = { m.out with indexMasks := im }) ∧ (l ≠ 0 → t.out = m.out)))

/-- **Its payer, at all four arms of the row of frames**; «no mark behind» is taken as a premise
(`h0`). -/
theorem keepsOpened_of {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs)
    {l : Nat} {f : LinkFrame} (hi : fs[l]? = some f) {m t : S} (ho : f.opened m = .ok t)
    (h0 : t.failed = none) : keepsOpened l m t := by
  refine ⟨h0, ?_⟩
  rcases IM.frames_arms h l f hi with ⟨X, -, -, rfl⟩ | ⟨rfl, P, -, -, e, -⟩ | ⟨P, n, -, -, e, -⟩ |
    ⟨P, -, -, e, -⟩
  · have ho' : (Except.ok m : Except String S) = .ok t := ho
    cases ho'
    exact Or.inl rfl
  · rw [e] at ho
    obtain ⟨-, -, g3, ⟨im, -, g4⟩, -⟩ := openedZeroGives P _ _ m t ho
    exact Or.inr ⟨g3, ⟨im, g4⟩, fun hne => absurd rfl hne⟩
  · rw [e] at ho
    obtain ⟨-, -, g3, g4, -⟩ := openedAttGives P m t ho
    exact Or.inr ⟨g3, ⟨m.out.indexMasks, by rw [g4]⟩, fun _ => g4⟩
  · rw [e] at ho
    obtain ⟨-, -, g3, g4, -⟩ := openedLayGives P m t ho
    exact Or.inr ⟨g3, ⟨m.out.indexMasks, by rw [g4]⟩, fun _ => g4⟩

/-- **THE JOINED MEMBER's CLAUSE, THE FRAME's HALF PAID.** -/
theorem keeps_joined_opened {Z : ProofFile.Pub} {l : Nat} {b b' : Block S Cl} {a : Place}
    (hj : IM.Joined Z l b b' a) (ft : Nat) (C₁ : S → S → Prop)
    (h₁ : ∀ s m, StepYes ft b' s m → m.failed = none → C₁ s m) (s s' : S)
    (h : StepYes ft b s s') : ∃ m, C₁ s m ∧ keepsOpened l m s' :=
  keeps_joined hj ft C₁ (keepsOpened l) h₁
    (fun _ _ _ _ g1 g2 _ g5 g6 _ => keepsOpened_of g1 g2 g5 g6) s s' h

/-! ## What readers get -/

/-- The library's own clause at every row follows. -/
theorem keepsOpened_lib {l : Nat} {m t : S} (h : keepsOpened l m t) : OpenedKeeps m t := by
  rcases h.2 with rfl | ⟨g, -⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact keeps_of_leaves g

theorem keepsOpened_st {l : Nat} {m t : S} (h : keepsOpened l m t) : t.st = m.st := by
  rcases h.2 with rfl | ⟨g, -⟩
  · rfl
  · exact g.2.2.1

theorem keepsOpened_book {l : Nat} {m t : S} (h : keepsOpened l m t) : t.book = m.book := by
  rcases h.2 with rfl | ⟨g, -⟩
  · rfl
  · exact g.2.2.2.1

theorem keepsOpened_reply {l : Nat} {m t : S} (h : keepsOpened l m t) :
    t.out.reply = m.out.reply := by
  rcases h.2 with rfl | ⟨-, ⟨im, e⟩, -⟩
  · rfl
  · rw [e]

theorem keepsOpened_pending {l : Nat} {m t : S} (h : keepsOpened l m t) :
    t.out.pending = m.out.pending := by
  rcases h.2 with rfl | ⟨-, ⟨im, e⟩, -⟩
  · rfl
  · rw [e]

/-- At every link but the first what goes on to the later chains is as it was, whole. -/
theorem keepsOpened_out {l : Nat} {m t : S} (h : keepsOpened l m t) (hl : l ≠ 0) :
    t.out = m.out := by
  rcases h.2 with rfl | ⟨-, -, g⟩
  · rfl
  · exact g hl

end ProofFile.Honest

#print axioms ProofFile.Honest.keepsOpened_of
#print axioms ProofFile.Honest.keeps_joined_opened
#print axioms ProofFile.Honest.keepsOpened_lib
#print axioms ProofFile.Honest.keepsOpened_st
#print axioms ProofFile.Honest.keepsOpened_book
#print axioms ProofFile.Honest.keepsOpened_reply
#print axioms ProofFile.Honest.keepsOpened_pending
#print axioms ProofFile.Honest.keepsOpened_out
