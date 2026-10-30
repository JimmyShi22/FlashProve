-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/OpenedKeepsR.lean: the clause `keepsOpened`
(Honest/Law/NoHouse/OpenedKeeps.lean) with one relation more: the frame's step "opened" leaves the
pending rows (`S.rows`, Johnson/Desc/First/State.lean). "Opened" is joined after the first
sub-protocol of each segment. The open item `pile` states that every pending row holds of the
witness. What the pending rows are depends on where the chain stands (the field `here` of the
state), and `keepsOpened` states nothing about that field. So `pile` cannot be shown to pass over
such a sub-protocol from `keepsOpened` alone. One definition, and its proof from the step.

  1  `keepsOpenedR`   the definition
  2  `here_between`, `rows_between`, `rows_lay`, `rows_att`   between two segments, in a
     feed-forward segment and in an attention segment, the pending rows are the list `out.pending`
  3  `keepsOpenedR_of`   an accepting "opened" without a failure mark after it gives the clause, for
     all four forms of the library's list of frames. It has the hypotheses of `keepsOpened_of`
  4  `keeps_joined_openedR`   the clause of the joined sub-protocol, in the form of
     `keeps_joined_opened`

Sources. The library shows where the chain stands after "opened" (`openedZero_here`,
`openedLay_here`, `openedAtt_here`, Johnson/Top/H0/Walk/FrameHere.lean) and that it stands between
two segments before it (`openLayZero_ok`, `openLay_ok`, `openAtt_ok`,
Johnson/Top/H0/Walk/FrameLaw.lean).

Limits.
  * One direction: from an accepting step.
  * `keepsOpenedR` is a definition. Nothing is claimed of it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.OpenedKeeps
import Johnson.Top.H0.Walk.FrameHere

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open ProofFile (Cl)

/-! ## 1 The definition -/

/-- **What the frame's step "opened" keeps at segment `l`, with the pending rows.** `keepsOpened`
(Honest/Law/NoHouse/OpenedKeeps.lean), and the pending rows are as they were. It is a definition: a
part of a clause of `keeps`. -/
def keepsOpenedR (l : Nat) (m t : S) : Prop := keepsOpened l m t ∧ t.rows = m.rows

/-! ## 2 What the pending rows are -/

/-- The test "between two segments" says where the chain stands. -/
theorem here_between {s : S} (e : s.atBetween = true) : s.here = .between := by
  unfold S.atBetween at e
  cases hh : s.here <;> simp [hh] at e ⊢

theorem rows_between {s : S} (e : s.atBetween = true) : s.rows = s.out.pending := by
  simp [S.rows, here_between e]

theorem rows_lay {s : S} {a : VerifiableInference.Desc.First.LayOwn} (e : s.here = .lay a) :
    s.rows = s.out.pending := by
  simp [S.rows, e]

theorem rows_att {s : S} {a : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att a) :
    s.rows = s.out.pending := by
  simp [S.rows, e]

/-! ## 3 From the step -/

/-- **An accepting "opened" gives the clause**, for all four forms of the list of frames. -/
theorem keepsOpenedR_of {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs)
    {l : Nat} {f : LinkFrame} (hi : fs[l]? = some f) {m t : S} (ho : f.opened m = .ok t)
    (h0 : t.failed = none) : keepsOpenedR l m t := by
  have K := keepsOpened_of h hi ho h0
  refine ⟨K, ?_⟩
  rcases IM.frames_arms h l f hi with ⟨X, -, -, rfl⟩ | ⟨rfl, P, -, -, e, -⟩ | ⟨P, n, -, -, e, -⟩ |
    ⟨P, -, -, e, -⟩
  · have ho' : (Except.ok m : Except String S) = .ok t := ho
    cases ho'
    rfl
  · rw [e] at ho
    rw [rows_lay (Johnson.Desc.First.Walk.Tied.openedZero_here ho),
      rows_between (Johnson.Desc.First.Walk.Law.openLayZero_ok ho).1]
    exact keepsOpened_pending K
  · rw [e] at ho
    rw [rows_att (Johnson.Desc.First.Walk.Tied.openedAtt_here ho),
      rows_between (Johnson.Desc.First.Walk.Law.openAtt_ok ho).1]
    exact keepsOpened_pending K
  · rw [e] at ho
    rw [rows_lay (Johnson.Desc.First.Walk.Tied.openedLay_here ho),
      rows_between (Johnson.Desc.First.Walk.Law.openLay_ok ho).1]
    exact keepsOpened_pending K

/-! ## 4 The joined sub-protocol -/

/-- The clause of the joined sub-protocol, with the frame's half shown. -/
theorem keeps_joined_openedR {Z : ProofFile.Pub} {l : Nat} {b b' : Block S Cl} {a : Place}
    (hj : IM.Joined Z l b b' a) (ft : Nat) (C₁ : S → S → Prop)
    (h₁ : ∀ s m, StepYes ft b' s m → m.failed = none → C₁ s m) (s s' : S)
    (h : StepYes ft b s s') : ∃ m, C₁ s m ∧ keepsOpenedR l m s' :=
  keeps_joined hj ft C₁ (keepsOpenedR l) h₁
    (fun _ _ _ _ g1 g2 _ g5 g6 _ => keepsOpenedR_of g1 g2 g5 g6) s s' h

end ProofFile.Honest

#print axioms ProofFile.Honest.here_between
#print axioms ProofFile.Honest.rows_between
#print axioms ProofFile.Honest.rows_lay
#print axioms ProofFile.Honest.rows_att
#print axioms ProofFile.Honest.keepsOpenedR_of
#print axioms ProofFile.Honest.keeps_joined_openedR
