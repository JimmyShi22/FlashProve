-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ReachAtFlat.lean: THE PREMISE `reach` OF `PileWalk`
(Johnson/Desc/K13/Honest/PileInduction.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN
IN LEAN, AT THE CHAIN's OWN SITES AND THE BORDER 355: SHOWN. Statements with their proofs:
arithmetic on the tables of rounds.

The pile's filler (`pileBySites`, Johnson/Desc/K13/Honest/PileDefs.lean) reads for a site's row
(`pileRowAt`) the challenges of 2 + lk rounds from the merge's batching round on. `reach` asks that
these stand among the first n rounds; whoever pays it takes n := the number of rounds in front of
the border (`roundsAhead c.blocksInOrder 355`). They are rounds of the merging sub-protocol itself:
at a layers' site the last lk + 4 of the table of the layers' own rounds (`K4.rounds`,
OnBytes/Desc/First/K4/Rounds.lean); at the head's all lk + 4 of `mergeEntries`
(Johnson/Desc/First/Fork/MergeKind.lean). Called: `IM.k4_of` (Johnson/IMR/K4Seat.lean), `IM.k11_of`
(IMR/K11Seat.lean), `IM.hear_at_flat` (IMR/FlatIx.lean), `IM.flatIx_scope` (IMR/FlatScope.lean),
`IM.alone_rounds` (IMR/SeatForm.lean), `IM.Open.W` (IMR/SeatOpen.lean), `K11.blkAt_fields`
(Johnson/Top/H0/MergeLaw/LotIs.lean), `roundsAhead_succ` (Johnson/Desc/K13/Honest/FoldCut.lean),
`layersSigmaAt_eq` (Johnson/Desc/K13/Honest/MergeLayersJoin.lean).
Main names:
  `k4_rounds_length`: **the table of the layers' own rounds has `layersSigmaAt` + lk + 4 rows**: at
    every plan.
  `roundsAhead_mono`: the count of the rounds in front grows with the number.
  `hreach_at_flat`: **In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening
    of the proof file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's
    holder, the first chain): for every site σ of `sitesAt c Z` (SitesAtFlat.lean of this folder):
    σ.m.sigmaAt + (2 + lk) ≤ `roundsAhead c.blocksInOrder 355`**, lk the one layout's. No other premise.

What is not claimed. What these numbers are, as numerals. Nothing on soundness, completeness or
hiding.

-/
import Johnson.Desc.ProofFile.Honest.K13.SitesAtFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (roundsAhead roundsAhead_succ layersSigmaAt
  layersSigmaAt_eq)
open ProofFile (Cl)

/-- **The table of the layers' own rounds**: behind the merge's batching round stand lk + 3 more. -/
theorem k4_rounds_length (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) :
    (OnBytes.Desc.First.K4.rounds P hp g).length = layersSigmaAt P hp g + (P.wsLay.lk + 4) := by
  rw [layersSigmaAt_eq]
  unfold OnBytes.Desc.First.K4.rounds OnBytes.Desc.First.K4.layerRds OnBytes.Desc.First.K4.masked
    OnBytes.Desc.First.K4.k0
  by_cases h : (g == 0) = true
  · simp only [h, if_true, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate]
    omega
  · simp only [h, if_false, Bool.false_eq_true, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate]
    omega

/-- The count of the rounds in front grows with the number. -/
theorem roundsAhead_mono {Cl' : Type} (bs : List (Block S Cl')) {j k : Nat} (h : j ≤ k) :
    roundsAhead bs j ≤ roundsAhead bs k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold roundsAhead
  rw [List.take_add, List.flatMap_append, List.length_append]
  omega

variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`reach` AT THE CHAIN's OWN SITES**: each site's batching round, and the 1 + lk rounds behind
it that the filler reads, stand in front of number 355. -/
theorem hreach_at_flat (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) :
    ∀ σ ∈ sitesAt c Z, σ.m.sigmaAt + (2 + Z.p.X.layers.wsLay.lk) ≤ roundsAhead c.blocksInOrder 355 := by
  intro σ hσ
  rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
  · obtain ⟨Lk, b₀, x, e1, e2, -, hla, -, h2, h3, h4, -, -⟩ := IM.k4_of hS hR O g hg
    rw [O.W] at h3 h4
    have hb₀ := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 2,
      show 14 * (2 * g) + 2 + 2 = 28 * g + 4 by omega] at hb₀
    have hlen : b₀.rounds.length =
        (OnBytes.Desc.First.K4.rounds x.2.P x.2.hp x.2.g).length := by
      rw [IM.alone_rounds hla]
      show ((OnBytes.Desc.First.K4.entries x.2.P x.2.hp x.2.g).map _).length = _
      rw [List.length_map]
      unfold OnBytes.Desc.First.K4.entries
      rw [List.length_map]
    have hsig : (layerSite c Z g).m.sigmaAt =
        roundsAhead c.blocksInOrder (28 * g + 4) + layersSigmaAt x.2.P x.2.hp x.2.g := by
      show sigAt c Z (2 * g) = _
      unfold sigAt
      rw [if_neg (by omega), show 14 * (2 * g) + 4 = 28 * g + 4 by omega,
        show 2 * g / 2 = g by omega, h4, h3, h2]
      rfl
    have h5 := roundsAhead_succ hb₀
    have hm := roundsAhead_mono c.blocksInOrder (show 28 * g + 4 + 1 ≤ 355 by omega)
    rw [k4_rounds_length, h3] at hlen
    rw [hsig, h3]
    omega
  · obtain ⟨Lk, b₀, e1, e2, hla, -⟩ := IM.k11_of hS hR O
    have hb₀ : c.blocksInOrder[346]? = some b₀ := by
      have q := IM.hear_at_flat e1 e2
      rw [IM.flatIx_scope hS hR O (by decide) 8] at q
      exact q
    have hlen : b₀.rounds.length = Z.p.X.layers.wsLay.lk + 4 := by
      rw [IM.alone_rounds hla, (K11.blkAt_fields Z Bs.G₀).2.1]
      show ((Johnson.Desc.First.ForkMerge.mergeEntries Bs.G₀.W.layers.wsLay.lk 1 _).map _).length
        = _
      rw [List.length_map, O.W]
      unfold Johnson.Desc.First.ForkMerge.mergeEntries
      simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil]
    have hsig : (headSite c Z).m.sigmaAt = roundsAhead c.blocksInOrder 346 := rfl
    have h5 := roundsAhead_succ hb₀
    have hm := roundsAhead_mono c.blocksInOrder (show 346 + 1 ≤ 355 by omega)
    rw [hsig]
    omega

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k4_rounds_length
#print axioms ProofFile.Honest.K13.roundsAhead_mono
#print axioms ProofFile.Honest.K13.hreach_at_flat
