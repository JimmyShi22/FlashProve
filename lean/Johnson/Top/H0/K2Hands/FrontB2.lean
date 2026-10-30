-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontB2.lean: all that is public in what the law of the switch
of groups asks of the statement in front, from ONE test with code on the front that the text makes
of the record, three facts on one written front, one on the place's written numbers, and `Tied` at
the front's own announcements. Definitions with code, and theorems with their proofs.

The frame of the place is not the written front's frame W₀ but W₀
WITH THE PLACE's OWN NUMBERS (`placeFrame`): the number n0 of messages in front, the kept old
messages' numbers olds, and the new numbers n0 + 1, n0 + 2, … ; `Tied` is a premise at x itself.

  `newsAt n0 k`, `anew_is`: the numbers of the messages that take the kept rows at a front.
  `placeFrame W₀ n0 olds`: A CLOSED TERM where W₀, n0 and olds are written values.
  `real_place`: at the two tests' yes the frame with the front's own numbers (FrameOne.lean's
     `realOf`) is that term.
  `carriedB W₀ x`, `carried_of_test`: mainVars, d0, d1 of `FrontAt`.
  `frontB2 x₀ W₀ grp rows n0 olds x`: THE ONE TEST: `pinB`, `numsB` (FramePin.lean), `carriedB`.
     IT CAN FAIL.
  `front_twelve`: the twelve public clauses of `FrontAt` at x and at `placeFrame W₀ n0 olds`; the
     number of messages in front; the group's number and how many rows it has.

Limits. x₀, W₀ and the numbers are letters: they are not made of the plan here. `frontB2` is a
test on the front of a record: who makes it true along the chain is not said. Four clauses of
`FrontAt` are not public and are not touched: strIs, target, vector, sample. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrameOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open _root_.Tw.K2 (switchNotices)

/-- The numbers that a switch's sending gives the k messages for the kept rows, behind g's number
n0. -/
def newsAt (n0 k : ℕ) : Array ℕ := (Array.range k).map fun i => 1 + i + n0

theorem anew_is (x : _root_.Tw.K2.Front) : anewOf x = newsAt x.st.oracles.size x.T.kept.size := by
  refine Array.ext (by rw [anew_size]; simp [newsAt]) fun i h1 h2 => ?_
  unfold anewOf K2.idsOf newsAt
  simp

/-- **The written frame with the place's own numbers.** -/
def placeFrame (W₀ : SwitchFrame) (n0 : ℕ) (olds : List ℕ) : SwitchFrame :=
  renumber W₀ n0 olds.toArray (newsAt n0 W₀.kept.length)

theorem real_place {x₀ x : _root_.Tw.K2.Front} {W₀ : SwitchFrame} {grp rows n0 : ℕ}
    {olds : List ℕ} (h0 : K2.frameAt x₀ = some W₀) (hp : pinB x₀ x = true)
    (hn : numsB grp rows n0 olds x = true) : realOf W₀ x = placeFrame W₀ n0 olds := by
  have P := pin_facts hp
  obtain ⟨-, -, n3, n4⟩ := nums_of_test hn
  have k1 : x.T.kept.size = x₀.T.kept.size := by
    have := congrArg List.length P.kept
    simpa using this
  have k2 : W₀.kept.length = x₀.T.kept.size := by
    obtain ⟨-, -, -, -, -, -, -, hK⟩ := Johnson.Top.H.frame_fields _ _ _ _ _ W₀ h0
    have g0 : (anewOf x₀).size = (switchKept x₀.f.rows).size := frame_guard h0
    rw [hK, List.length_map, List.length_range, ← g0, anew_size]
  unfold realOf placeFrame
  rw [anew_is, n3, k1, k2, ← n4]

/-- **A test with code on the carried rows' sizes**: every tensor of the form on the main row's
message has as many variables as the old main code's messages have index bits; the two vectors on
the mask rows are no longer than the old mask code's messages. IT READS NUMBERS OF VARIABLES AND
LENGTHS ALONE: no element. -/
def carriedB (W₀ : SwitchFrame) (x : _root_.Tw.K2.Front) : Bool :=
  (x.f.rows.c.tensors.all fun v => v.vars == W₀.code.logEll) &&
    decide ((x.f.rows.d.getD 0 #[]).size ≤ W₀.zk.ell) &&
    decide ((x.f.rows.d.getD 1 #[]).size ≤ W₀.zk.ell)

theorem carried_of_test {W₀ : SwitchFrame} {x : _root_.Tw.K2.Front} (h : carriedB W₀ x = true) :
    (∀ v ∈ x.f.rows.c.tensors, v.vars = W₀.code.logEll) ∧
      (x.f.rows.d.getD 0 #[]).size ≤ W₀.zk.ell ∧ (x.f.rows.d.getD 1 #[]).size ≤ W₀.zk.ell := by
  simp only [carriedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **THE ONE TEST ON THE FRONT THAT THE TEXT MAKES OF A RECORD**: it has the public side of the
written front x₀, by place; its numbers are the place's; the carried rows have the frame's sizes. -/
def frontB2 (x₀ : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (grp rows n0 : ℕ) (olds : List ℕ)
    (x : _root_.Tw.K2.Front) : Bool :=
  pinB x₀ x && numsB grp rows n0 olds x && carriedB W₀ x

/-- **ALL THAT IS PUBLIC IN WHAT THE LAW ASKS OF THE STATEMENT IN FRONT**, at the written frame with
the place's own numbers. -/
theorem front_twelve {cs : Codes} {l : List (OracleShape × ℕ)} {W₀ : SwitchFrame}
    {x₀ x : _root_.Tw.K2.Front} {grp rows n0 : ℕ} {olds : List ℕ}
    (h0 : K2.frameAt x₀ = some W₀) (hcs : x₀.st.codes = cs) (hb : frontPubB l.length x₀ = true)
    (hnd : olds.Nodup) (ht : Tied l (switchNotices x.T x.others))
    (h : frontB2 x₀ W₀ grp rows n0 olds x = true) :
    (K2.frameAt x = some (placeFrame W₀ n0 olds) ∧ (placeFrame W₀ n0 olds).zk.logN ≤ 32 ∧
      (∀ (a a' : ℕ) (k k' : KeptPlace), (placeFrame W₀ n0 olds).kept[a]? = some k →
        (placeFrame W₀ n0 olds).kept[a']? = some k' → k.old = k'.old → a = a') ∧
      x.st.codes = cs ∧ K2.KeptPos x.T ∧
      x.f.rows.keptRows = ((placeFrame W₀ n0 olds).kept.map (·.rows)).sum ∧
      (∀ (a : ℕ) (k : KeptPlace), (placeFrame W₀ n0 olds).kept[a]? = some k →
        (x.st.codes.base.getD (x.st.oracles.getD k.old default).shape.code default).ell =
          (placeFrame W₀ n0 olds).code.ell) ∧
      (∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = x.T.shape) ∧
      (∀ i (hi : i < x.T.kept.size), ∃ h : 1 + i < l.length,
        (l.get ⟨1 + i, h⟩).1 = x.T.kept[i].shape) ∧
      (∀ v ∈ x.f.rows.c.tensors, v.vars = (placeFrame W₀ n0 olds).code.logEll) ∧
      (x.f.rows.d.getD 0 #[]).size ≤ (placeFrame W₀ n0 olds).zk.ell ∧
      (x.f.rows.d.getD 1 #[]).size ≤ (placeFrame W₀ n0 olds).zk.ell) ∧
    x.st.oracles.size = n0 ∧
    x.f.group = grp ∧ ∃ G, x.st.groups[grp]? = some G ∧ G.rows.size = rows := by
  simp only [frontB2, Bool.and_eq_true] at h
  obtain ⟨⟨hp, hn⟩, hc⟩ := h
  obtain ⟨n1, n2, n3, n4⟩ := nums_of_test hn
  have once : keptOnceB x.f.rows = true := by
    unfold keptOnceB
    rw [n4]
    exact decide_eq_true hnd
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := front_nine h0 hcs hb hp once ht
  obtain ⟨c1, c2, c3⟩ := carried_of_test hc
  rw [real_place h0 hp hn] at p1 p2 p3 p6 p7
  exact ⟨⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, c1, c2, c3⟩, n3, n1, n2⟩

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.front_twelve
#print axioms VerifiableInference.Desc.First.K2Hands.real_place
