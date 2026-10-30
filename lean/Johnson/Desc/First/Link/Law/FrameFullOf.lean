-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrameFullOf.lean: `FrameFull` (TieFronts.lean: the frame of the open
link's check holds a number for every oracle message of the link) FROM ANOTHER FILE's LIST OF FACTS
ON REACHED STATES (`FoldFacts`, Johnson/Desc/First/FoldFacts.lean:
its fields frameIs and liveShape) AND ONE CLOSED TEST ON THE PLAN. So
the premise hno of t4_batch (TieFourBatch.lean: "nothing is ahead in front of the batching") stands
on that list. Theorems.

What is said.
  `link_of_seg`: the part that K9.segAt? reads holds the state's open link.
  `frameFull_of_facts`: **FrameFull at a reached state without a mark, in front of a sub-protocol of
    segment m at a piece from 7 + shift to 11 + 2 shift** (the batching's is 8 + 2 shift): next:
    frameIs' last clause · all: frameIs says that the frame's own list IS the plan's d.ownAt m 3
    there; liveShape that its shape is the plan's; hall: the plan's list is long enough.
  `ahead_none_of_facts`: so nothing is ahead there (ahead_none).

Limits. PREMISES: FoldFacts itself (other files': frameIs is among the fields that, not shown here,
ride true at the full size at all borders; its proof along "reached" is other files')
· hall: A CLOSED TEST ON THE PLAN's NUMBERS: NOT EVALUATED HERE. Nothing on soundness.

-/
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.First.Link.Law.TieFronts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart FoldFacts FoldData momentAt shiftAt)

/-- The part that K9.segAt? reads holds the state's open link. -/
theorem link_of_seg (s : S) (x : K9.Part) (h : K9.segAt? s = some x) : s.link? = some x.L := by
  unfold K9.segAt? at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨L, hL, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨G, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl, _, h⟩ := Option.bind_eq_some_iff.1 h
  rw [← Option.some.inj h]
  exact hL

variable {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
  {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}

/-- **THE FRAME IS FULL FROM THE THIRD MOMENT ON.** -/
theorem frameFull_of_facts (FF : FoldFacts Rch at_ d reqW links ps) (k : ℕ) (a : X) (p : Place)
    (m : ℕ) (x : K9.Part) (hR : Rch k a) (hf : (at_ a).2.failed = none) (hp : ps[k]? = some p)
    (hl : p.link = some m) (hx : K9.segAt? (at_ a).2 = some x)
    (h7 : 7 + shiftAt links m ≤ p.piece) (h11 : p.piece ≤ 11 + 2 * shiftAt links m)
    (hall : ∀ ms, (d.sent.shape.link[m]?).map (·.messages) = some ms →
      ms.length ≤ (d.ownAt m 3).size) : FrameFull x.L.check.frame := by
  have hL := link_of_seg _ _ hx
  obtain ⟨_, hown, _, h4⟩ := FF.frameIs k a p m x.L hR hf hp hl hL
  obtain ⟨hlink, hnext⟩ := h4 h11
  have hm3 : momentAt (shiftAt links m) p.piece = 3 := by
    unfold momentAt
    rw [if_neg (by omega), if_neg (by omega)]
  have hsh : x.L.check.frame.shape = d.sent.shape := by
    have h0 := FF.liveShape k a hR hf
    unfold S.live at h0
    rw [hL] at h0
    exact h0
  refine ⟨hnext, fun ms hms => ?_⟩
  rw [hown, hm3]
  rw [hsh, hlink] at hms
  exact hall ms hms

/-- **So nothing is ahead there.** -/
theorem ahead_none_of_facts (FF : FoldFacts Rch at_ d reqW links ps) (k : ℕ) (a : X) (p : Place)
    (m : ℕ) (x : K9.Part) (hR : Rch k a) (hf : (at_ a).2.failed = none) (hp : ps[k]? = some p)
    (hl : p.link = some m) (hx : K9.segAt? (at_ a).2 = some x)
    (h7 : 7 + shiftAt links m ≤ p.piece) (h11 : p.piece ≤ 11 + 2 * shiftAt links m)
    (hall : ∀ ms, (d.sent.shape.link[m]?).map (·.messages) = some ms →
      ms.length ≤ (d.ownAt m 3).size) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) :
    ∀ b, K9.aheadIn sent own x b = none :=
  ahead_none sent own x (frameFull_of_facts FF k a p m x hR hf hp hl hx h7 h11 hall)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.link_of_seg
#print axioms VerifiableInference.Desc.LinkJoin.frameFull_of_facts
#print axioms VerifiableInference.Desc.LinkJoin.ahead_none_of_facts
