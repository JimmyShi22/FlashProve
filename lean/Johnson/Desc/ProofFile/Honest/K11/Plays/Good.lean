-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Good.lean: the proofs of `HeadMergeFits` and `HeadMergeGood`
(Honest/K11/Plays/GoodStatement.lean), to the letter. Lemmas; none of the library's goals.

How. fits: the two simulators name their parts' addresses by definition; the row has as many rounds
as the block (`half_rounds`, Honest/K11/Plays/Accepted.lean; `mergeEntries_length`,
Honest/K11/Plays/Proofs.lean). The side's members are two, written out (`headMerge_members`). exact:
at the first, `quietPart_exact` (Honest/Small/Quiet.lean); at the second, the premise. fresh: at
both, `fresh_of_nil` (Honest/Law/ToyLaw.lean). plays, acc: from False.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.GoodStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Accepted
import Johnson.Desc.ProofFile.Honest.Small.Quiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind mergeEntries)
open ProofFile.Honest.Small (quietPart_exact statedOf)

/-- **The field fits.** -/
theorem headMergeFits : HeadMergeFits := by
  intro W₀ Rc Xi Tr X σ P claims weights name hb hr
  unfold Side.fits
  have h1 : σ.half.rounds = P.lay.lk + 4 := by
    unfold Side.half
    rw [hr]
    exact half_rounds (Rc := Rc) (Tr := Tr) (X := X) P claims weights
  have h2 : σ.block.rounds.length = P.lay.lk + 4 := by
    rw [hb]
    show ((mergeEntries P.lay.lk 1 P.work).map _).length = _
    rw [List.length_map, mergeEntries_length]
  have h3 : σ.block.oracles.length = P.lay.lk + 4 := by
    rw [hb]
    show (List.replicate (P.lay.lk + 4) _).length = _
    rw [List.length_replicate]
  have h4 : (σ.row.zipIdx.all fun s => s.1.2.addr == ⟨σ.block.place, s.2⟩) = true := by
    rw [hr, hb]
    simp [headMergeSided, headMergeRow, headMergeSims, headMergeDrawSim, quietSim, sumSim,
      List.zipIdx, IM.seatedAs]
    rfl
  rw [h1, h2, h3, h4]
  simp

/-- The batching round, as the kind's block declares it. -/
def headMergeFirst (P : HeadMergeP) : Fmt.DeclaredRound :=
  { entry :=
      { name := OnBytes.Model.RoundName.batSigma.name, work := P.work, drawE := 1, rows := 1 } }

/-- The side's members: the quiet member, and one more, number 1. -/
theorem headMerge_members {W₀ Rc Xi Tr X : Type}
    (σ : Side S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (name : String)
    (hb : σ.block = IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name (headMergePlace P))
    (hr : σ.row = headMergeSided P claims weights) :
    ∃ u₁ : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi, u₁.number = 1 ∧
      σ.members = [⟨0, [(headMergeFirst P, [])], quietPart 1, quietSim ⟨headMergePlace P, 0⟩ 1⟩,
        u₁] := by
  unfold Side.members
  rw [hr, hb]
  exact ⟨_, rfl, rfl⟩

/-- **`Good`, under the premise on the sumcheck's part and the premise on the book.** -/
theorem headMergeGood : HeadMergeGood := by
  intro W₀ Rc Xi Tr X σ φ Bk ord chain firstTree pre P claims weights name hb hr hown hsum
  obtain ⟨u₁, hn, hm⟩ := headMerge_members σ P claims weights name hb hr
  refine ⟨headMergeFits W₀ Rc Xi Tr X σ P claims weights name hb hr,
    fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim, ?_, ?_⟩
  · intro u hu ca m front ds asks _ hseen _ hd _ hh hs
    have hu' := hu
    rw [hm] at hu'
    rcases List.mem_cons.1 hu' with rfl | h1
    · exact quietPart_exact φ σ chain firstTree (fun _ _ _ _ => True) (fun _ _ _ => True) 0 1
        [(headMergeFirst P, [])] ⟨headMergePlace P, 0⟩
        (by simp [statedOf, headMergeFirst, Fmt.DeclaredRound.items, Fmt.Entry.cut])
        ca m front ds asks trivial hseen hd trivial hh hs
    · obtain rfl := List.mem_singleton.1 h1
      exact hsum _ hu hn ca m front ds asks hseen hd hh hs
  · intro u _ p sp ca m ds asks _ _ _
    exact fresh_of_nil _ (hown u.number p) _ _

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.headMergeFits
#print axioms ProofFile.Honest.K11.headMerge_members
#print axioms ProofFile.Honest.K11.headMergeGood
