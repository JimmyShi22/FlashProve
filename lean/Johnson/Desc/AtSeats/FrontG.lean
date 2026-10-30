-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FrontG.lean: THE OWED SENTENCE HashBuild.Queue.FrontGOwed
(Johnson/Desc/AtSeats/Queue/FrontGOwed.lean), PROVED AT ALL LETTERS: the
three premises of openingZero_sentIs on the verifier's state in front of kind K1's first sending, at
the data sentDataAt shape N links ps built, out of the seven plain facts.

  atMoment_zero    at a frame of the shape, at link 0: the frame's messages of moment 0 are the
                   shape's link 0's
  own_zero         the first k of K1's new numbers from 0 are the range of k, each plus 0
  frontG           the sentence
  trees_zero       beside it: openingZero_treesAre's premise at the same data, by looks_startFork,
                   where the planned ledger of built's entry 0 is X's

Limits. THREE UNFOLDINGS. That a state meets the seven facts is shown nowhere here. The letters q, gp,
N, links, ps, built are free; of N, links and ps only baseAt N links ps 0 = 0 is read; built is
read by trees_zero alone. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.Queue.FrontGOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open VerifiableInference.Desc
open OnBytes OnBytes.Params OnBytes.Model
open Desc.Plain
open VerifiableInference.Desc.First (S ModelPart Numbers)
open VerifiableInference.Desc.First.FillSent (sentDataAt baseAt)

/-- At a frame of the shape, at link 0. -/
theorem atMoment_zero (f : ReqFrame) (shape : Params.ReqShape) (hs : f.shape = shape)
    (hl : f.link = 0) :
    f.atMoment 0 =
      ((shape.link[0]?.map (·.messages)).getD []).filter fun x => x.moment == 0 := by
  unfold ReqFrame.atMoment
  rw [hs, hl]

/-- The first k of the new numbers, counted from 0. -/
theorem own_zero (P : K1.Par) (k : Nat) (hk : k ≤ P.sent.size) :
    (K1.idsOf P 0).extract 0 k = (Array.range k).map (· + (0 + 0)) := by
  refine Array.ext ?_ fun i h1 _ => ?_
  · rw [Array.size_extract, K1.idsOf_size, Array.size_map, Array.size_range]
    omega
  · have hi : i < k := by
      rw [Array.size_extract, K1.idsOf_size] at h1
      omega
    have e := K1.ownIds_get P 0 k i hk hi
    rw [Array.getElem?_eq_getElem h1] at e
    rw [Option.some.inj e]
    simp

/-- **THE SENTENCE.** -/
theorem frontG : Queue.FrontGOwed := by
  intro q gp shape N links ps built s h0 hsh hl hg hk hb hlen
  refine ⟨?_, ?_, ?_⟩
  · rw [hg, hsh]
    rfl
  · rw [hk]
    rfl
  · have e : (sentDataAt shape N links ps built).own 0 =
        (Array.range (((shape.link[0]?.map (·.messages)).getD []).filter
          fun x => x.moment == 0).length).map (· + (baseAt N links ps 0 + 0)) := rfl
    rw [e, hb, h0, own_zero _ _ hlen, atMoment_zero _ shape hsh hl]

/-- **The one line beside**: openingZero_treesAre's premise at the same data: the fresh ledger's arrays
have the data's looks at segment 0, where the planned ledger of built's entry 0 is X's. -/
theorem trees_zero (shape : Params.ReqShape) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (built : Array Stages.LinkH) (X : Johnson.Desc.First.Walk.LinkPub) (ns : Nat)
    (Y : Stages.LinkH) (hY : built[0]? = some Y) (hF : Y.Fp = X.Fp) :
    (Johnson.Desc.First.Walk.startFork X ns).trees.toList.map
      VerifiableInference.Desc.First.FillSent.treeLook =
        (sentDataAt shape N links ps built).trees 0 := by
  rw [VerifiableInference.Desc.First.FillSent.looks_startFork]
  show _ = ((built[0]?).map fun Z => VerifiableInference.Desc.First.FillSent.looksOf Z.Fp).getD []
  rw [hY, Option.map_some, Option.getD_some, hF]

end HashBuild

#print axioms HashBuild.trees_zero
#print axioms HashBuild.atMoment_zero
#print axioms HashBuild.own_zero
#print axioms HashBuild.frontG
