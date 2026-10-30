-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFirstRowsGood.lean: the first clause of the field `good` of `OwedRest`
(E2E/OfflineClauses.lean) at six of the seven rows of the offline prover's first chain: one theorem
over the three kinds' rows (E2E/OfflineSendingRowsGood.lean, E2E/OfflineLookupRowsGood.lean,
E2E/OfflineBatchingRowGood.lean).

  `carried_on_full`    by the written book all coins of the index masks' sending that are spent are also
                       carried to the last chain's own test; what the test on the ranges carries of
                       the multiplicities' sending (the kernel)
  `first_row_places`   a row of the first chain stands at one of the seven places
  `six_rows_goodAt`    `goodAt` at every muted row of the first chain but the test on the ranges, at
                       letters K that bear the key file's places, its three sending jobs, its two
                       faces and its batching's numbers, and at lists S whose six lists for these
                       rows are the kinds' own terms
  `six_rows_good_mute`   the same in the form of the field's first clause
  `first_goodAt`       at the offline prover's own senders (`valueAt`, E2E/KeyValueHolds.lean) and at
                       `laidSimulators`, whatever the ten lists that are letters
  `first_share`        the same in the form of the field's first clause

The book is a letter that equals the written book, so that it serves at a constant. No premise on what
the book states at the lookups' parts (`LookupsStated`, E2E/OfflineLaying.lean) is taken, and none on
the lengths or the addresses of the ten lists that are letters: `Side.fits` at these six rows reads
neither. Conditional on `KeySourced`, scope, and `SendingPositions`: at the three sendings the rows'
letter on positions is within the sender's bound. At the lookups and the batching c is free.

Limits. Not the ranges' row, nor any row of the shared or the last chain. `A` and `B` are false at a
muted row, so `plays` and `acc` are vacuous. Each field is one part at a time. The lookups' and the
batching's parts spend coins of the sendings: that these are uniform and apart from what their owner
shows is `fresh` at the three sendings' rows, which are among the six. `fresh` speaks of what is known
to the spender or to a part before it, not after. EVERY STRETCH THAT THE LOOKUPS AND THE BATCHING SPEND IS
LATER CARRIED WHOLE TO A PROXIMITY TEST THAT IS NOT AMONG THE SIX: the index masks' to the last chain's own
test (`carried_on_full`: the kernel), the multiplicities' to the test on the ranges (what that test
carries: `carried_on_full`; that each stretch spent lies within it: a `#guard`, so the evaluator's word
and no theorem). So the weight of
hiding lies on `exact` at these tests' rows, under their On, and not on the six rows here. The joining
of the rows' sentences into one on the file is the frame's rule (`rule_views_mute`,
Honest/Law/Rule/Mute.lean), which asks `Owed` whole, and is not here. Nothing on any property.
-/
import E2E.OfflineSendingRowsGood
import E2E.OfflineLookupRowsAtValue
import E2E.OfflineBatchingRowGood

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver first_places)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull idxPlace msgPlace lookPlace rngPlace battPlace wPlace
  ownTestPlace)
open AtPublicFiles.KeyValues (WitK indexMaskSending multiplicitiesSending batchedRowsSending keyBatt faceAt)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

/-- **By the written book what is spent of the index masks' sending is also carried on, and what the test on
the ranges carries of the multiplicities' sending.** Of the index masks' sending both parts of the last
chain's own test carry the coins 0 to 304 of the extension field, and every entry that spends of it
lies within these. Of the multiplicities' sending both parts of the test on the ranges carry the coins
0 to 97 of the base field and 0 to 37,304 of the extension field. By evaluation. -/
theorem carried_on_full : atFull (fun K =>
    (((keyBook K).ahead.filter fun e => e.owner == ⟨idxPlace, 0⟩ && !e.once).map
      (fun e => (e.spender, e.start.f, e.count.f, e.start.e, e.count.e)) ==
        [(⟨ownTestPlace, 0⟩, 0, 0, 0, 305), (⟨ownTestPlace, 1⟩, 0, 0, 0, 305)]) &&
    (((keyBook K).ahead.filter fun e => e.owner == ⟨idxPlace, 0⟩ && e.once).all
      fun e => e.count.f == 0 && decide (e.start.e + e.count.e ≤ 305)) &&
    (((keyBook K).ahead.filter fun e => e.owner == ⟨msgPlace, 0⟩ && !e.once).map
      (fun e => (e.spender, e.start.f, e.count.f, e.start.e, e.count.e)) ==
        [(⟨rngPlace, 0⟩, 0, 98, 0, 37305), (⟨rngPlace, 1⟩, 0, 98, 0, 37305),
          (⟨rngPlace, 1⟩, 98, 0, 37305, 793)])) = true := by
  decide +kernel

-- every entry by which a lookup's part spends of the multiplicities' sending lies within what the test
-- on the ranges carries: as the evaluator reads it; no theorem
#guard atFull (fun K =>
  ((keyBook K).ahead.filter fun e =>
      e.owner == ⟨msgPlace, 0⟩ && e.once && e.spender.place.link.isSome).all
    fun e => decide (e.start.f + e.count.f ≤ 98) && decide (e.start.e + e.count.e ≤ 37305))

section Letters
variable {W₀ Rc Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- A row of the first chain stands at one of the seven places. -/
theorem first_row_places {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first,
      L.place = idxPlace ∨ L.place = msgPlace ∨ L.place = lookPlace 0 ∨ L.place = lookPlace 1 ∨
        L.place = rngPlace ∨ L.place = battPlace ∨ L.place = wPlace := by
  intro L hL
  have hp : L.place ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first.map (·.place) :=
    List.mem_map_of_mem hL
  have e : (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first.map (·.place) =
      (keyProver K).first.map (·.place) := rowsAt_places _ _ _
  rw [e, first_places K hA] at hp
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hp

/-- **`goodAt` at the muted rows of the first chain, but the test on the ranges.** -/
theorem six_rows_goodAt {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (f : W₀ → Weights)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (hi : K.idx = indexMaskSending Xs)
    (hm : K.msg = multiplicitiesSending f Xs) (hw : K.w = batchedRowsSending f Xs N) (hf0 : K.look0.face = faceAt Xs 0)
    (hf1 : K.look1.face = faceAt Xs 1) (hb : K.batt = keyBatt Xs) (S : OfflineSimulators)
    (si : S.indexMasks = [sendingSimulator K.idx]) (sm : S.multiplicities = [sendingSimulator K.msg])
    (s0 : S.lookup0 = K3.lookSims K.look0) (s1 : S.lookup1 = K3.lookSims K.look1)
    (sb : S.batching = K13.k13Sims K.batt) (sw : S.messageW = [sendingSimulator K.w])
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SendingPositions K c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first, L.place ≠ rngPlace →
      (L.mute.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0 [] := by
  intro L hL hne
  rcases first_row_places K hA S c L hL with hp | hp | hp | hp | hp | hp | hp
  · exact sending_rows_goodAt hs scope hK hB f K hA hi hm hw S si sm sw c hc L hL (Or.inl hp)
  · exact sending_rows_goodAt hs scope hK hB f K hA hi hm hw S si sm sw c hc L hL
      (Or.inr (Or.inl hp))
  · exact lookup_rows_goodAt hs scope hK hB K hA hf0 hf1 S s0 s1 c L hL (Or.inl hp)
  · exact lookup_rows_goodAt hs scope hK hB K hA hf0 hf1 S s0 s1 c L hL (Or.inr hp)
  · exact absurd hp hne
  · exact batching_row_goodAt hs scope hK hB K hA hb S sb c L hL hp
  · exact sending_rows_goodAt hs scope hK hB f K hA hi hm hw S si sm sw c hc L hL
      (Or.inr (Or.inr hp))

/-- **The six rows in the form of `OwedRest.good`'s first clause.** -/
theorem six_rows_good_mute {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (f : W₀ → Weights)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (hi : K.idx = indexMaskSending Xs)
    (hm : K.msg = multiplicitiesSending f Xs) (hw : K.w = batchedRowsSending f Xs N) (hf0 : K.look0.face = faceAt Xs 0)
    (hf1 : K.look1.face = faceAt Xs 1) (hb : K.batt = keyBatt Xs) (S : OfflineSimulators)
    (si : S.indexMasks = [sendingSimulator K.idx]) (sm : S.multiplicities = [sendingSimulator K.msg])
    (s0 : S.lookup0 = K3.lookSims K.look0) (s1 : S.lookup1 = K3.lookSims K.look1)
    (sb : S.batching = K13.k13Sims K.batt) (sw : S.messageW = [sendingSimulator K.w])
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SendingPositions K c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place ≠ rngPlace →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0
        (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.falls₁ := by
  intro L hL hne
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  exact six_rows_goodAt hs scope hK hB f K hA hi hm hw hf0 hf1 hb S si sm s0 s1 sb sw c hc L' hL' hne

end Letters

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **`goodAt` at the muted rows of the first chain, but the test on the ranges**, at the offline
prover's own senders and the laid simulators. -/
theorem first_goodAt {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (T : TheirSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SendingPositions (valueAt K' Xs N Pl f g inR d pU pO ent groups first) c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
        (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T) c).first,
      L.place ≠ rngPlace →
      (L.mute.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0 [] :=
  six_rows_goodAt hs scope hK hB f _
    (value_atPlaces K' Xs N Pl f g inR d pU pO ent groups first hs scope) rfl rfl rfl rfl rfl rfl _
    rfl rfl rfl rfl rfl rfl c hc

/-- **The first clause of `OwedRest.good`, but for the test on the ranges**, at the offline prover's
own senders and the laid simulators. -/
theorem first_share {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (T : TheirSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SendingPositions (valueAt K' Xs N Pl f g inR d pU pO ent groups first) c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
        (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T) c).mute.first,
      L.place ≠ rngPlace →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0 (offlineRows (keyFileDescription Xs N Pl) Bk
                           (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
                           (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T) c).mute.falls₁ := by
  intro L hL hne
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  exact first_goodAt K' Xs N Pl f g inR d pU pO ent groups first hs scope hK hB T c hc L' hL' hne

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.carried_on_full
#print axioms AtPublicFiles.OfflineRows.first_row_places
#print axioms AtPublicFiles.OfflineRows.six_rows_goodAt
#print axioms AtPublicFiles.OfflineRows.six_rows_good_mute
#print axioms AtPublicFiles.OfflineRows.first_goodAt
#print axioms AtPublicFiles.OfflineRows.first_share
