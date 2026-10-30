-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/DoorsFrame.lean: THE FRAME's STEP "OPENED" BEHIND A SEGMENT's FIRST PLACE
LEAVES WHAT
THE OPEN CLAIMS READ. Five theorems. A law file: no sub-protocol imports it.

Why. At 23 of its 25 places the code switch's decision is followed by the frame's quiet step
"opened",
which enters the segment. `left_opened` (Doors.lean) takes "the state stands outside the members'
places, in front and behind" as premises. Here they are paid, and the step is taken as the list of
frames gives it.

What is said.
  `notMem_of_between`, `notMem_of_link`: a state between two segments, or inside one, does not stand
  at
    the members' places.
  `left_openAtt`, `left_openLay`: the two texts of "opened" behind a later segment's first place
  give
    `Left` (Left.lean): from `openedAttGives`, `openedLayGives`
    (Johnson/Top/H0/Walk/FrameTiedRec.lean) and `openAtt_ok`, `openLay_ok` (FrameLaw.lean).
  `left_frameOpened`: at the l-th entry of the list of frames, l ≠ 0: whichever text it holds.

Limits. Not at segment 0: there "opened" lays the number of the index masks' message, and no code
switch stands in front of it. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.H0.K2Ties.Doors
import Johnson.Top.H0.Walk.FrameOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Tied
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf framesOf_arms)

theorem notMem_of_between {s : S} (h : s.atBetween = true) : ∀ a, s.here ≠ .mem a := by
  intro a e
  unfold S.atBetween at h
  rw [e] at h
  cases h

theorem notMem_of_link {s : S} {L : LinkCtx} (h : s.link? = some L) : ∀ a, s.here ≠ .mem a := by
  intro a e
  unfold S.link? at h
  rw [e] at h
  cases h

theorem left_openAtt {P : AttPar} {s t : S} (h : openAtt P s = .ok t) : Left s t := by
  obtain ⟨_, ⟨L, hL, _⟩, h1, h2, _⟩ := openedAttGives P s t h
  exact left_opened h1 h2 (notMem_of_between (Law.openAtt_ok h).1) (notMem_of_link hL)

theorem left_openLay {P : LayPar} {s t : S} (h : openLay P s = .ok t) : Left s t := by
  obtain ⟨_, ⟨L, hL, _⟩, h1, h2, _⟩ := openedLayGives P s t h
  exact left_opened h1 h2 (notMem_of_between (Law.openLay_ok h).1) (notMem_of_link hL)

/-- **"Opened" behind a later segment's first place leaves what the open claims read.** -/
theorem left_frameOpened {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs)
    (hf : fs[l]? = some f) (hl : l ≠ 0) {m u : S} (hy : f.opened m = .ok u) : Left m u := by
  rcases framesOf_arms h hf with ⟨X', _, _, e⟩ | ⟨h0, _, _, Q, _, _, _, _, _, e, _⟩ |
    ⟨_, _, _, Q, _, _, _, _, _, e, _⟩ | ⟨_, _, _, Q, _, _, _, _, _, e, _⟩
  · subst e
    obtain rfl : m = u := Except.ok.inj hy
    exact Left.refl _
  · exact absurd h0 hl
  · rw [e] at hy
    exact left_openAtt hy
  · rw [e] at hy
    exact left_openLay hy

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.left_openAtt
#print axioms VerifiableInference.Desc.First.K2Ties.left_openLay
#print axioms VerifiableInference.Desc.First.K2Ties.left_frameOpened
