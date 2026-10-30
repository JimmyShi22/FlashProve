-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K8ByPlace.lean: THE SMALLNESS TEST'S LOT, ITS SECOND ROW, IN THE FORM "BY THE
PLACE": each block's declared rounds are the list that the written table `listAt` bears at the name
that the written table `nameW` gives the block's place. At hypotheses by field.
No soundness is claimed.

Why. The row link by link is `k8_rounds_at` (Johnson/AtFull/Rounds/K8.lean): the rounds are `listAt`
of the written name "the link's name and :5 | :6". The laws that spend the lots' rows
(Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean, `rows_by_place`) ask them at `nameW b.place`. Here
the two names are shown to be one at the draw's 25 places, and the row is said in that form.

Main names.
  `k8Names_full` [BY THE KERNEL]: at each of the 25 written pairs (kind, name) with its link's
    number: `nameW` of the draw's place is the written name.
  `k8Names_full_next` [BY THE KERNEL; NEGATIVE]: asked at the next link's place: no, at none of the
    25. Well-formed wrong data: a table that named two links' places alike would accept it there.
  `k8_lists_by_place`: **THE ROW: where the built links' kinds and names are the written ones and
    `k8TritsB G` says yes: of each block b of the lot: `b.rounds = listAt (nameW b.place)`.** That
    is the right arm of `ProofFile.Sk.Lst listAt (nameW b.place) b.rounds`.

Limits. THE TWO HYPOTHESES ARE SHOWN AT NO GROUND HERE. IT STANDS ON THESE FILES:
Names.lean and what it imports; ListAt.lean and what
it imports. The full size alone; the example's weights are synthetic. No soundness is claimed.

-/
import Johnson.AtFull.Rounds.K8
import Johnson.Desc.ProofFile.Law.Skel.Full.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8L
open VerifiableInference.Desc.First (K8.whole)
open Johnson.AtFull.Rounds (listAt)
open ProofFile.Sk.Full (nameW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At the draw's 25 places the two written names are one. -/
theorem k8Names_full :
    (k8KindsW.zipIdx.all fun x =>
      decide (nameW (k8PlaceW x.1.1 x.2) = k8NameW x.1.1 x.1.2)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Asked at the next link's place: at none. -/
theorem k8Names_full_next :
    (k8KindsW.zipIdx.any fun x =>
      decide (nameW (k8PlaceW x.1.1 (x.2 + 1)) = k8NameW x.1.1 x.1.2)) = false := by decide +kernel

variable {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- **The row, by the place.** -/
theorem k8_lists_by_place (hk : G.built.toList.map (fun X => (X.kind, X.name)) = k8KindsW)
    (ht : k8TritsB G = true) :
    ∀ b ∈ (ProofFile.P1K8.lot Z).blocks G, b.rounds = listAt (nameW b.place) := by
  intro b hb
  have hb' : b ∈ ProofFile.k8Whole Z G := hb
  unfold ProofFile.k8Whole at hb'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb'
  have hm : ((x.1.kind, x.1.name), x.2) ∈ k8KindsW.zipIdx := by
    rw [← hk, List.zipIdx_map]
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  have e : nameW (k8PlaceW x.1.kind x.2) = k8NameW x.1.kind x.1.name :=
    of_decide_eq_true (List.all_eq_true.1 k8Names_full _ hm)
  show (K8.whole (ProofFile.k8ParW Z G x.1 x.2)).rounds =
    listAt (nameW (K8.whole (ProofFile.k8ParW Z G x.1 x.2)).place)
  rw [k8Place_whole, e]
  exact k8_rounds_at hk ht x hx

end P1K8L

#print axioms P1K8L.k8Names_full
#print axioms P1K8L.k8Names_full_next
#print axioms P1K8L.k8_lists_by_place
