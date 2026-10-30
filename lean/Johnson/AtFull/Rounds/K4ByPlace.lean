-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K4ByPlace.lean: K4's row of the rounds' column in the form that
`ProofFile.Sk.Full.rows_by_place` (Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean) takes: the rounds of
each block of K4's lot are the written table's list at the written name of the block's place.

  `k4_names`: BY THE KERNEL: at chain 1, link 2 g, piece 3, kind K4, for g below 12, the written
    name (`ProofFile.Sk.Full.nameW`) is "G‹g›:3". `k4_names_bent`: a negative test: at the link's next
    place it is not.
  **`k4_rounds_by_place`**: under `k4_rounds_row`'s premises (Johnson/AtFull/Rounds/K4.lean: the
    scope, the two returns, and (hn) the fifteen numbers): for each block b of K4's lot:
    `ProofFile.Sk.Lst listAt (nameW b.place) b.rounds`.

Limits. As K4.lean's: IT PAYS NONE OF ITS PREMISES. Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.Rounds.K4
import Johnson.Desc.ProofFile.Law.Skel.Full.Names
import Johnson.Desc.ProofFile.Law.Skel.SkelLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open ProofFile.Sk.Full (nameW)

set_option maxRecDepth 100000 in
/-- BY THE KERNEL: the written names at K4's twelve places. -/
theorem k4_names :
    ((List.range 12).all fun g => nameW ⟨1, some (2 * g), 3, .K4⟩ == k4Name g) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A negative test, stated positively: at the link's next place (piece 4, kind K1) the written name
is another. -/
theorem k4_names_bent : (nameW ⟨1, some 0, 4, .K1⟩ == k4Name 0) = false := by
  decide +kernel

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **K4's row, by the place**: under the scope, the two returns and (hn) the fifteen numbers: the
rounds of each block of K4's lot are the table's list at the written name of its place. -/
theorem k4_rounds_by_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hn : ∀ g < 12, ∀ hp, G₀.W.G[g]? = some hp → numsOf G₀.W.layers hp = numsW g) :
    ∀ b ∈ (ProofFile.k4Lot Z).blocks G₀, ProofFile.Sk.Lst listAt (nameW b.place) b.rounds := by
  intro b hb
  obtain ⟨g, hg, hp, hr⟩ := k4_rounds_row hS hR hZ hG hn b hb
  have hN : nameW b.place = k4Name g := by
    rw [hp]
    exact eq_of_beq (List.all_eq_true.1 k4_names g (List.mem_range.2 hg))
  rw [hN]
  exact Or.inr hr

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.k4_names
#print axioms Johnson.AtFull.Rounds.k4_names_bent
#print axioms Johnson.AtFull.Rounds.k4_rounds_by_place
