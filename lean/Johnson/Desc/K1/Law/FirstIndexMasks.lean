-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/FirstIndexMasks.lean: kind K1: WHICH MESSAGE THE FRAME's TEST ON THE INDEX MASKS
FINDS BEHIND THE FIRST SEGMENT's OPENING. Statements and proofs.
  `firstOwn_sent`: an accepting decision of the opening has compared what the state's frame
    announces with what the sub-protocol's rounds declare: so the sending has as many messages as
    the segment's own of moment 0, one more (the fold's mask), and the shape's messages "at the
    start".
  `firstAtS_im`: where the shape in front has a message "at the start" and, behind, the test
    `IndexMasksAt` (Johnson/Top/H0/Walk/FrameProps.lean) finds im: the state in front had none in
    its list, the shape has just one, and im is THE SENDING's LAST MESSAGE: the number of messages
    in front plus the sending's size less one.
The premise on the shape cannot be dropped: where the shape has no message "at the start" nothing is
appended to the list, and what the test finds is an older message.
Nothing on soundness.

-/
import Johnson.Desc.K1.Law.OpeningZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Props (IndexMasksAt)

variable {Cl : Type}

/-- How many messages the opening sends. -/
theorem firstOwn_sent (P : Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (rs : List Fmt.RoundView) (h : firstOwn P owed c d rs = .ok (c', d')) :
    P.sent.size = (c.frame.atMoment 0).length + 1 + c.frame.shape.atStart.length := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, hq, _⟩ := (bind_ok _ _ _).1 h
  have e := beq_iff_eq.1 ((need_ok _ _ _).1 hq)
  clear * - e
  have e2 := congrArg Array.size e
  simp only [Array.size_append, ReqFrame.notices, List.size_toArray, List.length_map] at e2
  rw [← e2]
  rfl

/-- **The test finds the sending's last message.** -/
theorem firstAtS_im (q : Params.First) (gp : GPar) (s m : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok m)
    (hne : s.check.frame.shape.atStart ≠ []) (room im : Nat)
    (hi : IndexMasksAt room m.check m.st.oracles im) :
    0 < (firstPar q gp).sent.size ∧ im = s.st.oracles.size + ((firstPar q gp).sent.size - 1) := by
  obtain ⟨c, d', h1, _, _⟩ := firstAtS_ok q gp s m _ gs h
  have hn := firstOwn_sent _ _ _ _ _ _ _ h1
  have ha := firstAtS_atStart q gp s m r₁ r₂ gs h
  obtain ⟨z1, z2, _⟩ := hi
  have hpos : 0 < s.check.frame.shape.atStart.length := List.length_pos_iff.2 hne
  rw [ha] at z1 z2
  have hsz : (((Array.range (firstPar q gp).sent.size).map (· + s.st.oracles.size)).extract
      ((s.check.frame.atMoment 0).length + 1) (firstPar q gp).sent.size).size =
      s.check.frame.shape.atStart.length := by
    rw [Array.size_extract, Array.size_map, Array.size_range, Nat.min_self, hn]
    omega
  rw [Array.size_append, hsz] at z1
  have h0 : s.check.frame.atStart.size = 0 := by omega
  have h1' : s.check.frame.shape.atStart.length = 1 := by omega
  refine ⟨by omega, ?_⟩
  clear h h1 ha
  rw [Array.getElem?_append_right (by omega), h0, Nat.sub_zero, Array.getElem?_extract_of_lt
    (by rw [Array.size_map, Array.size_range]; omega)] at z2
  have z3 := Option.some.inj z2
  rw [Array.getElem_map, Array.getElem_range] at z3
  omega

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.firstOwn_sent
#print axioms VerifiableInference.Desc.K1.firstAtS_im
