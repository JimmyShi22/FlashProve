-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K4NumsAtFull.lean: THE PREMISE hn OF K4's ROW OF THE ROUNDS' COLUMN
(`k4_rounds_row`, Johnson/AtFull/Rounds/K4.lean; n4 of `ProofFile.Sk.Full.second_rows`) AT THE STORED
FULL-SIZE PUBLIC FILES, UNDER ONE PREMISE ON THE LAYOUT FILE's SIZE AND THE TWO RETURNS.

  `k4Nums_zFull`: (hsz) the stored layout file has 224975 bytes; (hX) `publicOfO`, at the format's
    second hash function, returns X at `VerifierAndGoals.storedPublicFiles`: at each group g below 12 and each plan hp at
    g in X.G: `numsOf X.layers hp = numsW g`. It is the ninth conjunct of `publicOfO_zFull_more`
    (Johnson/AtFull/Public/AtX0Shape.lean), which says it of a value X₀ that the maker returns: a
    maker is a function: so X is that value.
  **`n4_zFull`**: (hsz); (hZ) `ProofFile.pubPlain` returns Z there; (hG) the blank ground G₀ is returned:
    hn at G₀.W. By `IM.ground_public` (Johnson/IMR/PureJoin.lean).
  `len_written`: BY THE KERNEL: at the written numbers K4's table has 170 rounds in the first group
    and 168 in each of the groups 1 to 11. `len_written_bent`: a negative test.
  **`hlen_zFull`**: so, under the same three, the number of rounds of K4's table at each group: the
    premise hlen of `k4_lot_skel` (Johnson/AtFull/K4Sent/LotSkel.lean), whose `roundsW g` is
    `if g == 0 then 170 else 168`.
  **`k4_rounds_zFull`**: K4's row by the place (`k4_rounds_by_place`) at these files, under the same
    three.

Limits. UNDER hsz, hZ AND hG, WHICH ARE NOT PAID HERE. At the stored full-size files and the second
hash function `OnBytes.secondHashFunction` alone. Not an example of the head. Nothing on soundness.
On hiding nothing.
-/
import Johnson.AtFull.Rounds.K4ByPlace
import Johnson.AtFull.Public.AtX0Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Desc.First.K4 (rounds)
open VerifiableInference.PlanWritten (publicOfO)
open Johnson.AtFull.Public (publicOfO_zFull_more)

/-- **The fifteen numbers at the public part's value at the stored full-size files**, under (hsz)
the layout file's size and (hX) the maker's return. -/
theorem k4Nums_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X) :
    ∀ g < 12, ∀ hp, X.G[g]? = some hp → numsOf X.layers hp = numsW g := by
  obtain ⟨X₀, hX₀, -, -, -, -, -, -, -, hn, -⟩ := publicOfO_zFull_more hsz
  obtain rfl : X₀ = X := Except.ok.inj (hX₀.symm.trans hX)
  exact hn

variable {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **hn at the blank ground of the stored full-size files**, under (hsz) and the two returns. -/
theorem n4_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ g < 12, ∀ hp, G₀.W.G[g]? = some hp → numsOf G₀.W.layers hp = numsW g :=
  k4Nums_zFull hsz (IM.ground_public hZ hG).1

set_option maxRecDepth 100000 in
/-- BY THE KERNEL: at the written numbers K4's table has 170 rounds in the first group, 168 in each
of the groups 1 to 11. -/
theorem len_written :
    ((List.range 12).all fun g =>
      (roundsN (numsW g) g).length == if g == 0 then 170 else 168) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A negative test, stated positively: with lamS lowered by one the second group has not 168. -/
theorem len_written_bent : ((roundsN ((numsW 1).set 8 22) 1).length == 168) = false := by
  decide +kernel

/-- **The number of rounds of K4's table at each group**, under (hsz) and the two returns. -/
theorem hlen_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ g < 12, ∀ hp, G₀.W.G[g]? = some hp →
      (rounds G₀.W.layers hp g).length = if g == 0 then 170 else 168 := by
  intro g hg hp h
  rw [rounds_eq, n4_zFull hsz hZ hG g hg hp h]
  exact eq_of_beq (List.all_eq_true.1 len_written g (List.mem_range.2 hg))

/-- **K4's row, by the place, at the stored full-size files**, under (hsz) and the two returns. -/
theorem k4_rounds_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ b ∈ (ProofFile.k4Lot Z).blocks G₀, ProofFile.Sk.Lst listAt (ProofFile.Sk.Full.nameW b.place) b.rounds := by
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  exact k4_rounds_by_place VerifierAndGoals.inScope_full hF hZ hG (n4_zFull hsz hZ hG)

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.k4Nums_zFull
#print axioms Johnson.AtFull.Rounds.n4_zFull
#print axioms Johnson.AtFull.Rounds.len_written
#print axioms Johnson.AtFull.Rounds.len_written_bent
#print axioms Johnson.AtFull.Rounds.hlen_zFull
#print axioms Johnson.AtFull.Rounds.k4_rounds_zFull
