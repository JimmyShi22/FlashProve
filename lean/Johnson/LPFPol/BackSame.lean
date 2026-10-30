-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/BackSame.lean: four steps of `ProofFile.onlineDescriptionFromPublicPart`'s back (no fault; nothing lacking; the
blocks at the places; the first chain) return at one base and seat just as at another with the same
skeletons. A statement and its proof.
  `back_same`: where the places, the shape, the batchings' places, the segments' sorts, the lots'
      skeletons and the two later seats' names and stand-ins are one, and the four steps return at
      the first: they return at the second, and the two chains' flat lists have one list of
      skeletons. Further premises, at each of the two: the base's blocks are the lots' (hB, hB'),
      and every lot is `Steady` (hS, hS').
It is `back_of_skel` (Johnson/LPFPol/SkR/SkelEnd.lean) at the second, its four closed facts read off
the first by the equations of SkelFaults.lean (`faultsAt_skel`), SkelParts.lean (`road_skel` …
`base_skel`) and SkelChain.lean (`chainBy_skel`) in that folder.
Limits. None of the premises is paid here. A skeleton is blind to what a block decides. Nothing on
soundness.

-/
import Johnson.LPFPol.SkR.SkelEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFPol
open LPFPol.SkR ProofFile
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)

theorem back_same (Z Z' : Pub) (T T' : PureSeat) (B B' : PureBase)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hB' : B'.all = T'.lots.map fun L => (L, L.blocks B'.G₀))
    (hS : ∀ L ∈ T.lots, Steady B.G₀ L) (hS' : ∀ L ∈ T'.lots, Steady B'.G₀ L)
    (e1 : B'.spots = B.spots) (e2 : B'.shape = B.shape) (e3 : B'.batchAt = B.batchAt)
    (e4 : subsOf Z' = subsOf Z)
    (ek : T'.lots.map (lotSk B'.G₀) = T.lots.map (lotSk B.G₀))
    (e6 : (T'.shared.map fun A => (A.lot, A.standIns)) = T.shared.map fun A => (A.lot, A.standIns))
    (e7 : (T'.second.map fun A => (A.lot, A.standIns)) = T.second.map fun A => (A.lot, A.standIns))
    (f : faultsAt T B = []) (l : lackingAt T (partsAt T B) = [])
    {base : List (Block S Cl)} {c : Chain S Cl} (hb : (partsAt T B).base = .ok base)
    (hc : chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c) :
    faultsAt T' B' = [] ∧ lackingAt T' (partsAt T' B') = [] ∧
      ∃ base', (partsAt T' B').base = .ok base' ∧ base'.map skel = base.map skel ∧
        ∃ c', chainBy Z' base' (partsAt T' B').frames (partsAt T' B').road = .ok c' ∧
          c'.blocksInOrder.map skel = c.blocksInOrder.map skel := by
  have hr : (partsAt T B).frames.map (·.1) =
      (framesSk B.shape (T.lots.map (lotSk B.G₀))).map (·.1) := by
    rw [← frames_skel T B hB, List.map_map]
    rfl
  refine back_of_skel Z' T' B' (T.lots.map (lotSk B.G₀)) (base.map skel) (c.blocksInOrder.map skel) hB' ek
      hS'
    ?_ ?_ ?_ ?_
  · rw [e1, e2, e3, ← faultsAt_skel T B hB]
    exact f
  · rw [e1, e2, e3, e6, e7]
    rw [lackingAt_skel, places_skel T B hB, hr, onRoad_skel, eachAt_skel, testsAt_skel] at l
    exact l
  · rw [e1]
    have h4 := base_skel (partsAt T B)
    rw [places_skel T B hB, hb] at h4
    exact h4.symm
  · rw [e1, e2, e4]
    have h5 := chainBy_skel Z base (partsAt T B).frames (partsAt T B).road _ (road_skel T B hS)
    rw [frames_skel T B hB, hc] at h5
    exact h5.symm

end LPFPol

#print axioms LPFPol.back_same
