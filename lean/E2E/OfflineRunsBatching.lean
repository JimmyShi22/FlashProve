-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsBatching.lean: `BlockPlays` (E2E/OfflineRunsForm.lean) at the key file's batching: what that
sub-protocol owes to "every run returns".

  `batt_block_plays`   the sub-protocol at the batching's place in the key file's description plays, whatever the
                       state, the reader of the weights, the pile's filler and the coins, at 18 variables

It reads no book and no witness, and it spends nothing of `MidForm`. It says that no move errs and that every
message has the declared shape: nothing on what is sent. Nothing on any property.
-/
import E2E.OfflineRunsLookups
import E2E.OfflineBatchingFields

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open VerifiableInference.Desc.K13 (battRounds)
open ProofFile.Honest.Small (plays_quiet)
open ProofFile.Honest.SumLaw (StatedBy statedBy_nums)
open AtPublicFiles.KeyBook (battPlace)
open AtPublicFiles.KeyValues (keyBatt)

variable {W₀ Rc Xi Tr Y Pb : Type}

/-- **The sub-protocol at the batching's place plays**, whatever the state. -/
theorem batt_block_plays {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hk : (keyBatt X).lin.kCol = 18) (weights : W₀ → Weights) (pile : K13.PileOf Xi)
    {φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb} {Bk : ProverCoinCounts}
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y)}
    {b : Block (descriptionFromSource X N P).S₁ (descriptionFromSource X N P).Cl} (hb : b ∈ (descriptionFromSource X N P).first.blocksInOrder)
    (hbp : b.place = battPlace)
    (hf : (hs.find? fun g => g.place == b.place) = some (K13.proverSideOfClaimCombination weights pile (keyBatt X)))
    (Pre : Mid (Local W₀ Rc Xi Tr) Y → Prop) : BlockPlays φ Bk 0 hs b Pre := by
  obtain ⟨e1, e2⟩ := batt_block X N P hb hbp
  have hz : b.rounds.zip b.oracles =
      ({ entry := VerifiableInference.Desc.K13.sigmaEntry (keyBatt X) }, []) ::
        ({ entry := VerifiableInference.Desc.K13.epsEntry (keyBatt X) }, []) ::
          List.replicate 18 ({ entry := VerifiableInference.Desc.K13.roundEntry (keyBatt X) }, []) := by
    rw [e1, e2, hk]
    unfold battRounds
    rw [hk]
    rfl
  have hm : (K13.k13Sum (keyBatt X)).moves.length = 19 := by
    unfold K13.k13Sum
    rw [K3.sumPart_moves]
    show VerifiableInference.Desc.K3.roundsOf (K13.k13Shape (keyBatt X).lin.kCol) = 19
    rw [hk]
    rfl
  have hsh : VerifiableInference.Desc.Part.MaskedSum.shapeOk (K13.k13Shape (keyBatt X).lin.kCol) =
      true := by
    rw [hk]
    rfl
  have hl : ((K13.k13Sum (keyBatt X)).lift (V := Local W₀ Rc Xi Tr) (W := Local W₀ Rc Xi Tr) (X := Y)
      (fun _ => ()) (K13.k13Ask weights pile) (fun _ => ()) (fun x _ => x)).moves.length = 19 :=
    (List.length_map _).trans hm
  refine blockPlays_of_parts hf ?_ Pre
  show RowPartsPlay [quietPart, (K13.k13Sum (keyBatt X)).lift (fun _ => ()) (K13.k13Ask weights pile)
    (fun _ => ()) fun x _ => x] (b.rounds.zip b.oracles)
  rw [hz]
  refine ⟨?_, ?_, trivial⟩
  · intro nm a v c ds back m hd
    exact ⟨_, plays_quiet 1 c nm a _
      (statedBy_nums _ _ rfl fun r hr => by rw [List.mem_singleton.1 hr]) v ds hd back m⟩
  · refine partPlays_sum (fun _ => ()) (K13.k13Ask weights pile) (fun _ => ()) (fun y _ => y)
      (fun _ _ => rfl) (fun _ => rfl) _ _ _ (two_of_shapeOk hsh) _ ?_
    refine statedBy_nums _ _ ?_ ?_
    · show List.map _ (List.take _ (List.drop 1 _)) = _
      rw [hl]
      show _ = List.map _ (scalarsOf (K13.k13Shape (keyBatt X).lin.kCol))
      rw [hk]
      rfl
    · intro r hr'
      have hr'' := List.mem_of_mem_take hr'
      have hr''' := List.mem_of_mem_drop hr''
      simp only [List.mem_cons, List.mem_replicate] at hr'''
      rcases hr''' with rfl | rfl | h
      · rfl
      · rfl
      · rw [h.2]

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.batt_block_plays
