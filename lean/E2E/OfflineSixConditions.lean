-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSixConditions.lean: ONE VALUE OF THE ROWS' LETTERS c SERVES BOTH FIELDS. The field `good` of
`OwedRest` (E2E/OfflineClauses.lean) asks of c, at the three sendings, that the condition on the positions
gives the sender's bound (`SendingPositions`, E2E/OfflineSendingRowsGood.lean); the field `owed` asks that the
bound gives the condition, and that nothing is asked at the two lookups and the batching (`SixLetters`,
E2E/OfflineOwedSix.lean). Here a named value meets both: a test that the two premises have a common member.

  `senderConditions`          at a sending: On says nothing, the positions' condition is the sender's bound
  `sixConditions`             that at the three sendings' places, the letters that say nothing elsewhere
  `sixConditions_positions`   `SendingPositions` at it
  `sixConditions_letters`     `SixLetters` at it
  `first_six_good_and_owed`   the two fields' first clauses together at that one c, at every row of the first
                              chain but the test on the ranges, at the offline prover's own senders and the
                              laid simulators

At the ranges' row, and at every row of the shared and the last chain, `sixConditions` lays the letters that
say nothing: whether `good` holds there at these letters is not said here; whoever pays these rows may
need other letters at their places, and the two premises read c at the six places alone. The limits of
the two fields' files stand: `exact` is the spender's half, with `fresh` at the owners under the kernel's
lines on the book; `owedAt` is conditional on the run's return.

WHERE THE WEIGHT OF HIDING LIES: NOT HERE. By the written book (`carried_on_full`,
E2E/OfflineFirstRowsGood.lean, by the kernel; that each stretch spent of the multiplicities' message
lies within what is carried is a `#guard` there and no theorem) every stretch that the two lookups
and the batching
spend is later CARRIED WHOLE to a proximity test that is not among the six rows: the multiplicities' message to both
parts of the test on the ranges, the index masks' message to both parts of the last chain's test. `fresh` speaks
of what the owner shows and of the owner's coins that go to the spender or to a part in front of it; of a part behind
the spender it says nothing. So that the masked values stay hidden rests on `exact` at these two tests' rows, at the
very masks as carried blocks, under their own On: these rows are not among the six, and nothing is said of them
here. Nothing on any property.
-/
import E2E.OfflineFirstRowsGood
import E2E.OfflineOwedSix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open OnBytes.SendSim.At (budAt)
open AtPublicFiles.KeyFile (KeyInst KeyParts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub idxPlace msgPlace rngPlace wPlace)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

/-- At a sending: the two conditions around the place and the condition at the part's start say nothing;
the condition on the positions is the sender's bound on queried positions. -/
def senderConditions {Bk : ProverCoinCounts} {S V W Y Pb : Type} (P : VerifiableInference.Desc.K1.Par) :
    RowConditions Bk S V W Y Pb :=
  ⟨fun _ _ _ _ => True, fun _ _ _ _ => True, fun _ _ _ _ => True, fun _ _ asks => budAt P asks⟩

section Letters
variable {W₀ Rc X₀ X Wk : Type}

/-- **The one value**: the senders' letters at the three sendings' places; elsewhere the letters that say
nothing. -/
def sixConditions (Fx : FileDescription KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk) :
    ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X :=
  ⟨fun p => (([(idxPlace, senderConditions K.idx.P), (msgPlace, senderConditions K.msg.P),
      (wPlace, senderConditions K.w.P)] : List (Place × _)).lookup p).getD RowConditions.bare,
    fun _ => RowConditions.bare, fun _ => RowConditions.bare⟩

/-- **What `owed` asks of the letters holds at it.** -/
theorem sixConditions_letters (Fx : FileDescription KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk) :
    SixLetters K (sixConditions Fx Bk K) where
  idx := ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h⟩
  msg := ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h⟩
  look0 := RowConditions.bare_asksNothing
  look1 := RowConditions.bare_asksNothing
  batt := RowConditions.bare_asksNothing
  w := ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h⟩

/-- **What `good` asks of the letters holds at it.** -/
theorem sixConditions_positions {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} (Bk : ProverCoinCounts)
    (K : KeyParts W₀ Rc Unit Unit Wk) :
    SendingPositions K (sixConditions (keyFileDescription Xs N Pl) Bk K) where
  indexMasks := fun _ _ _ h => h
  multiplicities := fun _ _ _ h => h
  messageW := fun _ _ _ h => h

end Letters

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **The two fields' first clauses together, at one c**: at every row of the first chain but the test on
the ranges: `goodAt`; and, at every run that has returned at draws that the description's rounds can draw,
`owedAt`. -/
theorem first_six_good_and_owed {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (T : TheirSimulators) :
    (∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
        (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T)
        (sixConditions (keyFileDescription Xs N Pl) Bk
          (valueAt K' Xs N Pl f g inR d pU pO ent groups first))).mute.first,
      L.place ≠ rngPlace →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0 (offlineRows (keyFileDescription Xs N Pl) Bk
                           (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
                           (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T)
                           (sixConditions (keyFileDescription Xs N Pl) Bk
                             (valueAt K' Xs N Pl f g inR d pU pO ent groups first))).mute.falls₁) ∧
    ∀ (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (w₀ : W₀) (rc : Rc) (x : KeyInst)
      (k : Coins Bk) (ρ : Draws) (r : RunC (keyFileDescription Xs N Pl)),
      ρ.due (keyFileDescription Xs N Pl) = true →
      runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk
                   (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
                   (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T)
                   (sixConditions (keyFileDescription Xs N Pl) Bk
                     (valueAt K' Xs N Pl f g inR d pU pO ent groups first))).mute.prover H) w₀ rc x k ρ = .ok r →
      ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
          (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
          (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T)
          (sixConditions (keyFileDescription Xs N Pl) Bk
            (valueAt K' Xs N Pl f g inR d pU pO ent groups first))).mute.first,
        L.place ≠ rngPlace →
        L.owedAt (keyFileDescription Xs N Pl).first.blocksInOrder k 0
          (fun a => orRefused (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk
                       (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
                       (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T)
                       (sixConditions (keyFileDescription Xs N Pl) Bk
                         (valueAt K' Xs N Pl f g inR d pU pO ent groups first))).mute.prover H) w₀ rc x k ρ a))
          r.run (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called :=
  ⟨first_share K' Xs N Pl f g inR d pU pO ent groups first hs scope hK hB T _
      (sixConditions_positions Bk _),
    fun _ _ _ _ _ _ _ hρ h =>
      owed_first_six_at_value K' Xs N Pl f g inR d pU pO ent groups first hs scope hK hB
        (sixConditions_letters _ Bk _) hρ h _⟩

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.sixConditions_letters
#print axioms AtPublicFiles.OfflineRows.sixConditions_positions
#print axioms AtPublicFiles.OfflineRows.first_six_good_and_owed
