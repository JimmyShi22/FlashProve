-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineSendingRowsGood.lean: the field `good` of `OwedRest` (E2E/OfflineClauses.lean) at the rows
of the three sendings of the key file's first chain: the index masks, the multiplicities, W.

  `idx_at_value`, `send_at_value`, `msg_at_value`, `w_at_value`   `GoodAt` at each row's side, at On :=
      True and the sender's own bound `budAt`
  `SendingPositions`     the rows' letter on positions is within the sender's bound, at the three places
  `sending_rows_goodAt`  `goodAt` at the three muted rows, at any letters K whose three sendings are
      the key file's own jobs, and any lists of simulators whose three lists are `sendingSimulator`

What it leans on. `KeySourced`, scope, the written book. THE FIELD `fresh` LEANS ON `BookClearAny` AT
THE WRITTEN BOOK AND THE DESCRIPTION'S ORDER, AT EACH OF THE THREE OWNERS. That is not assumed: it is
paid by three lines of the kernel (`index_fast_full`, `multiplicities_fast_full`, `messageW_fast_full`,
E2E/OfflineClearLines.lean) through `clearAny_of_fast`, `clear_same` and `order_named`.

Limits. `A` and `B` are false at a muted row, so `plays` and `acc` are vacuous. `exact` and `fresh` are
one sender at a time: nothing is said of the coins of two senders together, though one lookup spends
mask entries of the index masks' message and of the multiplicities' (Johnson/SendSim/Seat/AtKey.lean,
Limits, which all stand). The sending of the index masks holds mask rows alone, so `exact` has no
datum to hide there. The bound on positions is a premise inside `exact` and `fresh`: that a run's
positions meet it is `Owed.owed`, not here. Nothing on any property.
-/
import E2E.OfflineGoodAt
import E2E.OfflineFirstSends

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.SendSim.At (sendSim budAt)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub OneFull idxPlace msgPlace wPlace)
open AtPublicFiles.KeyValues (oneOf)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

section Value
variable {W₀ Rc Pb : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (f : W₀ → Weights)

/-- **The sending of the index masks' row**, at a job that is the key file's. -/
theorem idx_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) (J : K1.SendJob (Local W₀ Rc KeyInst Unit) Unit)
    (hJ : J = AtPublicFiles.KeyValues.indexMaskSending Xs) (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc KeyInst Unit)
      (Local W₀ Rc KeyInst Unit) Unit Pb)
    (hσ : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder J.P.place
      [(K1.sendPart J, sendSim J.P J.first J.ride ⟨J.P.place, 0⟩)] fs = some σ) :
    GoodAt Xs N Pl K₀ σ (fun _ _ _ _ => True) fun _ _ asks => budAt J.P asks := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  intro pre φ chain firstTree
  subst hJ
  obtain ⟨x, hx, hP⟩ := keyIdx_pars (W₀ := W₀) (Rc := Rc) (X := Unit) Xs
  refine send_row_good hx _ hP ?_ fs σ hσ pre φ chain firstTree
  rw [order_named scope hs.named]
  exact index_clear one hK

/-- **The sending of the index masks' row**, at the key file's own job, written out. -/
theorem send_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) :
    (∀ (fs : List (Fall (keyFileDescription Xs N Pl).S₁)) (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl
                   (Local W₀ Rc KeyInst Unit) (Local W₀ Rc KeyInst Unit) Unit Pb),
      Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P.place
        [(K1.sendPart (AtPublicFiles.KeyValues.indexMaskSending Xs), sendSim (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P 0
          (fun _ => none) ⟨(AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P.place, 0⟩)] fs = some σ →
      GoodAt Xs N Pl K₀ σ (fun _ _ _ _ => True)
        fun _ _ asks => budAt (AtPublicFiles.KeyValues.indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P asks) := by
  intro fs σ hσ
  exact idx_at_value Xs N Pl hs scope hK _ rfl fs σ hσ

/-- **The sending of the multiplicities' row.** -/
theorem msg_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) (J : K1.SendJob (Local W₀ Rc KeyInst Unit) Unit)
    (hJ : J = AtPublicFiles.KeyValues.multiplicitiesSending f Xs) (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc KeyInst Unit)
      (Local W₀ Rc KeyInst Unit) Unit Pb)
    (hσ : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder J.P.place
      [(K1.sendPart J, sendSim J.P J.first J.ride ⟨J.P.place, 0⟩)] fs = some σ) :
    GoodAt Xs N Pl K₀ σ (fun _ _ _ _ => True) fun _ _ asks => budAt J.P asks := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  intro pre φ chain firstTree
  subst hJ
  obtain ⟨x, hx, hP⟩ := keyMsg_pars (Rc := Rc) (X := Unit) Xs f
  refine send_row_good hx _ hP ?_ fs σ hσ pre φ chain firstTree
  rw [order_named scope hs.named]
  exact multiplicities_clear one hK f

/-- **The sending of W's row.** -/
theorem w_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) (J : K1.SendJob (Local W₀ Rc KeyInst Unit) Unit)
    (hJ : J = AtPublicFiles.KeyValues.batchedRowsSending f Xs N) (hr : J.ride = AtPublicFiles.KeyBook.rideW)
    (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc KeyInst Unit)
      (Local W₀ Rc KeyInst Unit) Unit Pb)
    (hσ : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder J.P.place
      [(K1.sendPart J, sendSim J.P J.first J.ride ⟨J.P.place, 0⟩)] fs = some σ) :
    GoodAt Xs N Pl K₀ σ (fun _ _ _ _ => True) fun _ _ asks => budAt J.P asks := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  intro pre φ chain firstTree
  subst hJ
  obtain ⟨x, hx, hP⟩ := keyW_pars (Rc := Rc) (X := Unit) Xs one N f
  refine send_row_good hx _ hP ?_ fs σ hσ pre φ chain firstTree
  rw [order_named scope hs.named, hr, (keyW_numbers Xs one N f).2.2.1]
  exact messageW_clear one hK f

end Value

section Rows
variable {W₀ Rc Wk : Type}

/-- **At the three sendings the rows' letter on positions is within the sender's bound.** -/
structure SendingPositions {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc Unit Unit Wk)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) : Prop where
  indexMasks : ∀ n ds asks, (c.first idxPlace).positions n ds asks → budAt K.idx.P asks
  multiplicities : ∀ n ds asks, (c.first msgPlace).positions n ds asks → budAt K.msg.P asks
  messageW : ∀ n ds asks, (c.first wPlace).positions n ds asks → budAt K.w.P asks

/-- **`goodAt` at the muted rows of the three sendings**: the share of `OwedRest.good` at rows 1, 2
and 7 of the first chain. The book is a letter that equals the written book, so that it serves at a
constant. -/
theorem sending_rows_goodAt {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (f : W₀ → Weights) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hA : K.AtPlaces) (hi : K.idx = AtPublicFiles.KeyValues.indexMaskSending Xs) (hm : K.msg = AtPublicFiles.KeyValues.multiplicitiesSending f Xs)
    (hw : K.w = AtPublicFiles.KeyValues.batchedRowsSending f Xs N) (S : OfflineSimulators)
    (si : S.indexMasks = [sendingSimulator K.idx])
    (sm : S.multiplicities = [sendingSimulator K.msg]) (sw : S.messageW = [sendingSimulator K.w])
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SendingPositions K c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first,
      (L.place = idxPlace ∨ L.place = msgPlace ∨ L.place = wPlace) →
      (L.mute.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0 [] := by
  subst hB
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  have apart : ∀ p : Place, p.kind ≠ .K1 → ¬ (p = idxPlace ∨ p = msgPlace ∨ p = wPlace) := by
    intro p hp h
    rcases h with rfl | rfl | rfl <;> exact hp rfl
  intro L hL hp
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hL
  have hp' : h.place = idxPlace ∨ h.place = msgPlace ∨ h.place = wPlace := hp
  rw [keyProver_first] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine goodAt_mute fun σ hσ => ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder K.idx.P.place
        (partsBeside [K1.sendPart K.idx] (S.byChain.first K.idx.P.place)) [] = some σ := hσ
    have es : S.byChain.first K.idx.P.place = [sendingSimulator K.idx] := by
      rw [hA.idx]
      exact si
    rw [es] at hσ'
    refine Good.narrow (fun _ _ _ _ _ => trivial) ?_
      (idx_at_value Xs N Pl hs scope hK K.idx hi [] σ hσ' _ _ _ _)
    show ∀ n ds asks, (c.first K.idx.P.place).positions n ds asks → budAt K.idx.P asks
    rw [hA.idx]
    exact hc.indexMasks
  · refine goodAt_mute fun σ hσ => ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder K.msg.P.place
        (partsBeside [K1.sendPart K.msg] (S.byChain.first K.msg.P.place)) [] = some σ := hσ
    have es : S.byChain.first K.msg.P.place = [sendingSimulator K.msg] := by
      rw [hA.msg]
      exact sm
    rw [es] at hσ'
    refine Good.narrow (fun _ _ _ _ _ => trivial) ?_
      (msg_at_value Xs N Pl f hs scope hK K.msg hm [] σ hσ' _ _ _ _)
    show ∀ n ds asks, (c.first K.msg.P.place).positions n ds asks → budAt K.msg.P asks
    rw [hA.msg]
    exact hc.multiplicities
  · exact absurd hp' (apart _ (by
      show K.look0.place.kind ≠ _
      rw [hA.look0]
      decide))
  · exact absurd hp' (apart _ (by
      show K.look1.place.kind ≠ _
      rw [hA.look1]
      decide))
  · exact absurd hp' (apart _ (by
      rw [hA.rng]
      decide))
  · exact absurd hp' (apart _ (by
      show (K13.k13Place K.batt).kind ≠ _
      rw [hA.batt]
      decide))
  · refine goodAt_mute fun σ hσ => ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder K.w.P.place
        (partsBeside [K1.sendPart K.w] (S.byChain.first K.w.P.place)) [] = some σ := hσ
    have es : S.byChain.first K.w.P.place = [sendingSimulator K.w] := by
      rw [hA.w]
      exact sw
    rw [es] at hσ'
    refine Good.narrow (fun _ _ _ _ _ => trivial) ?_
      (w_at_value Xs N Pl f hs scope hK K.w hw
        (by rw [hw]; exact (keyW_numbers Xs one N f).2.2.2) [] σ hσ' _ _ _ _)
    show ∀ n ds asks, (c.first K.w.P.place).positions n ds asks → budAt K.w.P asks
    rw [hA.w]
    exact hc.messageW

end Rows

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.idx_at_value
#print axioms AtPublicFiles.OfflineRows.send_at_value
#print axioms AtPublicFiles.OfflineRows.msg_at_value
#print axioms AtPublicFiles.OfflineRows.w_at_value
#print axioms AtPublicFiles.OfflineRows.sending_rows_goodAt
