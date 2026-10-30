-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineSendingRowsAtValue.lean: the share of `OwedRest.good` (E2E/OfflineClauses.lean) at the rows of
the three sendings of the key file's first chain, in that field's own form (a member of the muted
rows' first list, at the muted rows' falls), and at the offline prover's own senders (`valueAt`,
E2E/KeyValueHolds.lean).

  `sending_rows_good_mute`   E2E/OfflineSendingRowsGood.lean's `sending_rows_goodAt`, in the field's form
  `sendingConditions`, `sendingConditions_positions`   letters that meet `SendingPositions`: at the three
                             places On says nothing and the positions are the sender's `budAt`
  `sending_rows_at_laid`     the same at `valueAt` and `laidSimulators`, whatever the ten lists that are
                             letters: the three jobs and the three lists are the value's own, by unfolding
  `sending_rows_there`       A TEST OF EMPTINESS: the first list has a row at each of the three places,
                             and each has a side
  `sending_member`, `sending_sides_members`   A TEST OF EMPTINESS: each such side has exactly one member:
                             number 0, two rounds, the part `sendPart` of the row's own job, the
                             simulator `sendingSimulator` of that job: so `exact` and `fresh` are asked
  `fits_same`, `sendings_fit_full`, `sendings_fit`   A TEST OF EMPTINESS: the three jobs pass `sendFits`
                             (the kernel, at the written numbers): where a job fails it both moves of
                             `sendPart` err, and `exact` would compare two errors

The limits are those of E2E/OfflineSendingRowsGood.lean. Nothing on any property.
-/
import E2E.OfflineSendingRowsGood
import E2E.KeyValueHolds

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
open OnBytes.SendSim.At (budAt sendSim memberAt members_seated place_of_seated)
open OnBytes.SendSim.Seat (keyPars seatedAt_key key_member block_of_seated)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub OneFull idxPlace msgPlace wPlace rideMsg rideW)
open AtPublicFiles.KeyValues (WitK oneOf)
open AtPublicFiles.KeyValueHolds (valueAt atPlaces_value)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

section Member
variable {V W Y Pb : Type}

/-- **A side of a sender's row at the key file's description has exactly one member**: number 0, two
rounds, the honest sender of the job, and its simulator. -/
theorem sending_member {Xs : Source} {N : H2U.PlaceNums} {Q : LaterPlaces}
    {x : VerifiableInference.Desc.K1.Par × (Nat → Option K1.Ride)} (hx : x ∈ keyPars Xs)
    (J : K1.SendJob W Y) (hP : J.P = x.1)
    (fs : List (Fall (VerifiableInference.Desc.Key.descriptionFromSource Xs N Q).S₁))
    (σ : Side (VerifiableInference.Desc.Key.descriptionFromSource Xs N Q).S₁
      (VerifiableInference.Desc.Key.descriptionFromSource Xs N Q).Cl V W Y Pb)
    (hσ : Side.seated (VerifiableInference.Desc.Key.descriptionFromSource Xs N Q).first.blocksInOrder J.P.place
      [(K1.sendPart J, sendSim J.P J.first J.ride ⟨J.P.place, 0⟩)] fs = some σ) :
    ∃ u, σ.members = [u] ∧ u.number = 0 ∧ u.rounds.length = 2 ∧ u.part = K1.sendPart J ∧
      u.sim = sendSim J.P J.first J.ride ⟨J.P.place, 0⟩ := by
  have hS := seatedAt_key Xs N Q hx hP hσ
  have hp : σ.block.place = J.P.place := place_of_seated hσ
  obtain ⟨hr, ho⟩ := (key_member Xs N Q x hx).2 σ.block (block_of_seated hσ) (hP ▸ hp)
  refine ⟨memberAt σ J, members_seated hS, rfl, ?_, rfl, ?_⟩
  · show ((σ.block.rounds.zip σ.block.oracles).take 2).length = 2
    rw [hr, ho]
    rfl
  · show sendSim J.P J.first J.ride ⟨σ.block.place, 0⟩ = _
    rw [hp]

/-- The test that a job fits its place reads of a sending's numbers its codes and its notices. -/
theorem fits_same {P P' : VerifiableInference.Desc.K1.Par} (ride : Nat → Option K1.Ride)
    (hc : P.codes = P'.codes) (hs : P.sent = P'.sent) : K1.sendFits P ride = K1.sendFits P' ride := by
  delta K1.sendFits Johnson.Prover.Send.shapeAt
  rw [hc, hs]

/-- **The three sendings' jobs fit their places, at the written numbers.** By evaluation. -/
theorem sendings_fit_full : (K1.sendFits parIndexMasks (fun _ => none) &&
    K1.sendFits parMultiplicities rideMsg && K1.sendFits parMessageW rideW) = true := by
  decide +kernel

/-- A control: with W's table sent along the multiplicities' job does not fit. By evaluation. -/
theorem sendings_fit_full_no : K1.sendFits parMultiplicities rideW = false := by
  decide +kernel

end Member

section Fit
variable {W₀ Rc X : Type} (Xs : Source)

/-- **The key file's own three jobs fit their places**, at the written sizes. -/
theorem sendings_fit (one : OneFull Xs.Y.k.oneTime) (N : H2U.PlaceNums) (f : W₀ → Weights) :
    K1.sendFits (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) Xs).P
        (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) Xs).ride = true ∧
      K1.sendFits (AtPublicFiles.KeyValues.multiplicitiesSending (Rc := Rc) (X := X) f Xs).P
        (AtPublicFiles.KeyValues.multiplicitiesSending (Rc := Rc) (X := X) f Xs).ride = true ∧
      K1.sendFits (AtPublicFiles.KeyValues.batchedRowsSending (Rc := Rc) (X := X) f Xs N).P
        (AtPublicFiles.KeyValues.batchedRowsSending (Rc := Rc) (X := X) f Xs N).ride = true := by
  have h := sendings_fit_full
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨hc, hs, -, hr⟩ := keyW_numbers (Rc := Rc) (X := X) Xs one N f
  refine ⟨?_, ?_, ?_⟩
  · show K1.sendFits _ (fun _ => none) = true
    rw [fits_same (P' := parIndexMasks) _ one.codes ?_]
    · exact h1
    · refine (AtPublicFiles.KeyBook.sendingPar_sent _ _ _ _ _).trans ?_
      rw [one.idx]
      show _ = ([("the index masks", #[keyFull.once.input])].flatMap (·.2.toList)).toArray
      simp
  · show K1.sendFits _ rideMsg = true
    rw [fits_same (P' := parMultiplicities) _ one.codes ?_]
    · exact h2
    · refine (AtPublicFiles.KeyBook.sendingPar_sent _ _ _ _ _).trans ?_
      rw [one.ranges]
      show _ = ([("the lookups' own message and what rides with it",
        OnBytes.Wf.messageOf keyFull.ranges.x)].flatMap (·.2.toList)).toArray
      simp
  · rw [hr, fits_same (P' := parMessageW) _ hc ?_]
    · exact h3
    · rw [hs]
      show _ = ([("W and what rides with it",
        (OnBytes.linMessageW keyFull.once.shape).getD #[])].flatMap (·.2.toList)).toArray
      simp

end Fit

section Letters
variable {W₀ Rc Wk : Type}

/-- **The three rows in the form of `OwedRest.good`'s first clause.** -/
theorem sending_rows_good_mute {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (f : W₀ → Weights) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hA : K.AtPlaces) (hi : K.idx = AtPublicFiles.KeyValues.indexMaskSending Xs) (hm : K.msg = AtPublicFiles.KeyValues.multiplicitiesSending f Xs)
    (hw : K.w = AtPublicFiles.KeyValues.batchedRowsSending f Xs N) (S : OfflineSimulators)
    (si : S.indexMasks = [sendingSimulator K.idx])
    (sm : S.multiplicities = [sendingSimulator K.msg]) (sw : S.messageW = [sendingSimulator K.w])
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SendingPositions K c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first,
      (L.place = idxPlace ∨ L.place = msgPlace ∨ L.place = wPlace) →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0
        (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.falls₁ := by
  intro L hL hp
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  exact sending_rows_goodAt hs scope hK hB f K hA hi hm hw S si sm sw c hc L' hL' hp

/-- Letters that are c's own but at the three sendings' places, where On says nothing and the
positions are the sender's. -/
def sendingConditions {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc Unit Unit Wk)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit :=
  { c with
    first := fun p =>
      if p = idxPlace then { c.first p with
        atPart := fun _ _ _ _ => True, positions := fun _ _ asks => budAt K.idx.P asks }
      else if p = msgPlace then { c.first p with
        atPart := fun _ _ _ _ => True, positions := fun _ _ asks => budAt K.msg.P asks }
      else if p = wPlace then { c.first p with
        atPart := fun _ _ _ _ => True, positions := fun _ _ asks => budAt K.w.P asks }
      else c.first p }

/-- **`SendingPositions` has a member at every K and c.** -/
theorem sendingConditions_positions {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc Unit Unit Wk)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    SendingPositions K (sendingConditions K c) :=
  ⟨fun _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩

/-- **A TEST OF EMPTINESS.** In scope, at letters that bear the first chain's places, the muted rows'
first list has a row at each of the three sendings' places, and that row has a side at the
description's first chain: so the sentence above speaks of three sides. -/
theorem sending_rows_there {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) (p : Place)
    (hp : p = idxPlace ∨ p = msgPlace ∨ p = wPlace) :
    ∃ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place = p ∧
      ((L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder
        []).isSome = true := by
  obtain ⟨r1, -, -⟩ := AtPublicFiles.KeyBook.places_named scope hs.named
  have hin : ∀ q ∈ ([idxPlace, msgPlace, wPlace] : List Place),
      q ∈ AtPublicFiles.KeyBook.fullFirst.map (·.1) := by decide
  have hq : p ∈ AtPublicFiles.KeyBook.fullFirst.map (·.1) := by
    rcases hp with rfl | rfl | rfl
    · exact hin _ (by simp)
    · exact hin _ (by simp)
    · exact hin _ (by simp)
  have hmem : ∀ h ∈ (keyProver K).first, h.place = p →
      ∃ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place = p ∧
        ((L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder
          []).isSome = true := by
    intro h hh hpl
    refine ⟨(rowOf h (S.byChain.first h.place) (c.first h.place)).mute,
      List.mem_map.2 ⟨_, List.mem_map.2 ⟨h, hh, rfl⟩, rfl⟩, hpl, ?_⟩
    refine side_isSome _ _ _ ?_
    show h.place ∈ _
    rw [hpl, places_of_rows r1]
    exact hq
  rcases hp with rfl | rfl | rfl
  · exact hmem (K1.proverSideOfSending K.idx) (by rw [AtPublicFiles.KeyFile.keyProver_first]; simp) hA.idx
  · exact hmem (K1.proverSideOfSending K.msg) (by rw [AtPublicFiles.KeyFile.keyProver_first]; simp) hA.msg
  · exact hmem (K1.proverSideOfSending K.w) (by rw [AtPublicFiles.KeyFile.keyProver_first]; simp) hA.w

/-- **A TEST OF EMPTINESS.** Every side of a muted row at one of the three places has exactly one
member: number 0, two rounds, the honest sender of the row's own job, and that job's simulator. So
`exact` and `fresh` are asked of a member at each of the three rows. -/
theorem sending_sides_members {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {Bk : ProverCoinCounts} (f : W₀ → Weights)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (hi : K.idx = AtPublicFiles.KeyValues.indexMaskSending Xs)
    (hm : K.msg = AtPublicFiles.KeyValues.multiplicitiesSending f Xs) (hw : K.w = AtPublicFiles.KeyValues.batchedRowsSending f Xs N)
    (S : OfflineSimulators) (si : S.indexMasks = [sendingSimulator K.idx])
    (sm : S.multiplicities = [sendingSimulator K.msg]) (sw : S.messageW = [sendingSimulator K.w])
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first,
      ∀ J ∈ [(idxPlace, K.idx), (msgPlace, K.msg), (wPlace, K.w)], L.place = J.1 →
      ∀ σ, (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder
          [] = some σ →
        ∃ u, σ.members = [u] ∧ u.number = 0 ∧ u.rounds.length = 2 ∧ u.part = K1.sendPart J.2 ∧
          u.sim = sendingSimulator J.2 := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  intro L hL J hJ hp σ hσ
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hL'
  have hp' : h.place = J.1 := hp
  have hσ₀ : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder h.place
      (partsBeside h.parts (S.byChain.first h.place)) [] = some σ := hσ
  have hkind : h.place.kind = .K1 := by
    rw [hp']
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ
    rcases hJ with rfl | rfl | rfl <;> rfl
  rw [AtPublicFiles.KeyFile.keyProver_first] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh hJ
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have e : J = (idxPlace, K.idx) := by
      have hq : J.1 = idxPlace := hp'.symm.trans hA.idx
      rcases hJ with rfl | rfl | rfl
      · rfl
      · exact absurd (show msgPlace = idxPlace from hq) (by decide)
      · exact absurd (show wPlace = idxPlace from hq) (by decide)
    subst e
    have es : S.byChain.first K.idx.P.place = [sendingSimulator K.idx] := by
      rw [hA.idx]
      exact si
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder K.idx.P.place
        (partsBeside [K1.sendPart K.idx] (S.byChain.first K.idx.P.place)) [] = some σ := hσ₀
    rw [es] at hσ'
    obtain ⟨x, hx, hP⟩ := keyIdx_pars (W₀ := W₀) (Rc := Rc) (X := Unit) Xs
    exact sending_member hx K.idx (by rw [hi]; exact hP) [] σ hσ'
  · have e : J = (msgPlace, K.msg) := by
      have hq : J.1 = msgPlace := hp'.symm.trans hA.msg
      rcases hJ with rfl | rfl | rfl
      · exact absurd (show idxPlace = msgPlace from hq) (by decide)
      · rfl
      · exact absurd (show wPlace = msgPlace from hq) (by decide)
    subst e
    have es : S.byChain.first K.msg.P.place = [sendingSimulator K.msg] := by
      rw [hA.msg]
      exact sm
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder K.msg.P.place
        (partsBeside [K1.sendPart K.msg] (S.byChain.first K.msg.P.place)) [] = some σ := hσ₀
    rw [es] at hσ'
    obtain ⟨x, hx, hP⟩ := keyMsg_pars (Rc := Rc) (X := Unit) Xs f
    exact sending_member hx K.msg (by rw [hm]; exact hP) [] σ hσ'
  · exact absurd hkind (by
      show K.look0.place.kind ≠ _
      rw [hA.look0]
      decide)
  · exact absurd hkind (by
      show K.look1.place.kind ≠ _
      rw [hA.look1]
      decide)
  · exact absurd hkind (by
      rw [hA.rng]
      decide)
  · exact absurd hkind (by
      show (K13.k13Place K.batt).kind ≠ _
      rw [hA.batt]
      decide)
  · have e : J = (wPlace, K.w) := by
      have hq : J.1 = wPlace := hp'.symm.trans hA.w
      rcases hJ with rfl | rfl | rfl
      · exact absurd (show idxPlace = wPlace from hq) (by decide)
      · exact absurd (show msgPlace = wPlace from hq) (by decide)
      · rfl
    subst e
    have es : S.byChain.first K.w.P.place = [sendingSimulator K.w] := by
      rw [hA.w]
      exact sw
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder K.w.P.place
        (partsBeside [K1.sendPart K.w] (S.byChain.first K.w.P.place)) [] = some σ := hσ₀
    rw [es] at hσ'
    obtain ⟨x, hx, hP⟩ := keyW_pars (Rc := Rc) (X := Unit) Xs one N f
    exact sending_member hx K.w (by rw [hw]; exact hP) [] σ hσ'

end Letters

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **The three rows at the offline prover's own senders and the laid simulators**, whatever the ten
lists that are letters. -/
theorem sending_rows_at_laid {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (T : TheirSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SendingPositions (valueAt K' Xs N Pl f g inR d pU pO ent groups first) c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
        (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T) c).mute.first,
      (L.place = idxPlace ∨ L.place = msgPlace ∨ L.place = wPlace) →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0 (offlineRows (keyFileDescription Xs N Pl) Bk
                           (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
                           (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T) c).mute.falls₁ := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  obtain ⟨w, hw⟩ := written_message
  have hA : (valueAt K' Xs N Pl f g inR d pU pO ent groups first).AtPlaces :=
    atPlaces_value K' Xs N Pl f g inR d pU pO ent groups first (by
      show (OnBytes.linMessageW Xs.Y.k.oneTime.lin).isSome = true
      rw [el, hw]
      rfl)
  exact sending_rows_good_mute hs scope hK hB f _ hA rfl rfl rfl _ rfl rfl rfl c hc

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.sending_rows_good_mute
#print axioms AtPublicFiles.OfflineRows.sendingConditions_positions
#print axioms AtPublicFiles.OfflineRows.sending_rows_there
#print axioms AtPublicFiles.OfflineRows.sending_member
#print axioms AtPublicFiles.OfflineRows.fits_same
#print axioms AtPublicFiles.OfflineRows.sendings_fit_full
#print axioms AtPublicFiles.OfflineRows.sendings_fit_full_no
#print axioms AtPublicFiles.OfflineRows.sendings_fit
#print axioms AtPublicFiles.OfflineRows.sending_sides_members
#print axioms AtPublicFiles.OfflineRows.sending_rows_at_laid
