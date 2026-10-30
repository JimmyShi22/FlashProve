-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineFirstSends.lean: the fields `exact` and `fresh` at the three sendings of the first chain.

  `send_row_good`   `Good` at a sender's row, at every job whose numbers are an entry of `keyPars`,
                     under the test on the book at that sender
  `keyIdx_pars`, `keyMsg_pars`, `keyW_pars`   the key file's own three jobs are at such numbers
  `written_message`, `keyW_numbers`   the written shape has a message W; the codes, the notices, the
                     place and the table sent along of W's sending there
  `clear_same`, `order_named`, `index_clear`, `multiplicities_clear`, `messageW_clear`   the test on
      the book there, at the description's order, off the kernel's three lines

Each is one part at a time, at every job; the coins are taken as drawn for this one run
(Johnson/SendSim/Seat/AtKey.lean, Limits, which stand). Nothing on any property.
-/
import E2E.OfflineSides
import E2E.OfflineClearLines
import E2E.KeyFirstSends
import E2E.KeyPublic
import E2E.KeyPlacesNamed
import Johnson.SendSim.Seat.AtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open OnBytes.SendSim.At (BookClearAny sendSim budAt good_of_fields place_of_seated sendExactAt
  sendFreshAtWide)
open OnBytes.SendSim.Seat (keyPars seatedAt_key fields_of_seated)
open AtPublicFiles.KeyValues (indexMaskSending multiplicitiesSending batchedRowsSending)
open AtPublicFiles.AtFiles (KeySourced)

variable {V W Y Pb : Type}

/-- **`Good` at a sender's row.** Conditional on the test on the book, `BookClearAny`. -/
theorem send_row_good {Xs : Source} {N : H2U.PlaceNums} {Q : LaterPlaces}
    {x : VerifiableInference.Desc.K1.Par × (Nat → Option K1.Ride)} (hx : x ∈ keyPars Xs) (J : K1.SendJob W Y)
    (hP : J.P = x.1) {Bk : ProverCoinCounts} {ord : List Place}
    (hB : BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩) (fs : List (Fall (descriptionFromSource Xs N Q).S₁))
    (σ : Side (descriptionFromSource Xs N Q).S₁ (descriptionFromSource Xs N Q).Cl V W Y Pb)
    (hσ : Side.seated (descriptionFromSource Xs N Q).first.blocksInOrder J.P.place
      [(K1.sendPart J, sendSim J.P J.first J.ride ⟨J.P.place, 0⟩)] fs = some σ)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb) (chain firstTree : Nat) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ asks => budAt J.P asks) := by
  have hS := seatedAt_key Xs N Q hx hP hσ
  obtain ⟨h1, h2, h3⟩ := fields_of_seated sendExactAt sendFreshAtWide φ hS chain firstTree
  exact good_of_fields h1 h2 (h3 Bk ord (by rw [place_of_seated hσ]; exact hB))

/-- The test on the book reads of a sending's numbers its codes and its notices. -/
theorem clear_same {P P' : VerifiableInference.Desc.K1.Par} (ride : Nat → Option K1.Ride) (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) :
    OnBytes.SendSim.At.bookClearAnyB P ride Bk ord o =
      OnBytes.SendSim.At.bookClearAnyB P' ride Bk ord o := by
  delta OnBytes.SendSim.At.bookClearAnyB OnBytes.SendSim.At.spenderClearAnyB
    OnBytes.SendSim.At.foldAnyB OnBytes.SendSim.At.maskB OnBytes.SendSim.At.withinB
    OnBytes.SendSim.At.isFreeB OnBytes.SendSim.At.clearB OnBytes.SendSim.At.padNo
    OnBytes.SendSim.At.maskTailNo OnBytes.SendSim.At.maskCodeAt K1.maskStart K1.dueR K1.startR
    Johnson.Prover.Send.shapeAt
  rw [hc, hs]

/-- The written shape has a message W. -/
theorem written_message : ∃ w, OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape = some w := by
  have h := AtPublicFiles.KeyBook.rides_full.2.2
  cases hq : OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape with
  | none => rw [hq] at h; cases h
  | some w => exact ⟨w, rfl⟩

section Pars
variable {W₀ Rc X : Type} (Xs : Source)

/-- The sending of the index masks is at the first entry of `keyPars`. -/
theorem keyIdx_pars : ∃ x ∈ keyPars Xs, (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) Xs).P = x.1 :=
  ⟨_, List.mem_append_left _ List.mem_cons_self, rfl⟩

/-- The sending of the multiplicities is at the second. -/
theorem keyMsg_pars (f : W₀ → Weights) :
    ∃ x ∈ keyPars Xs, (multiplicitiesSending (Rc := Rc) (X := X) f Xs).P = x.1 :=
  ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

/-- The sending of W is at the third, at the written shape. -/
theorem keyW_pars (one : AtPublicFiles.KeyBook.OneFull Xs.Y.k.oneTime) (N : H2U.PlaceNums) (f : W₀ → Weights) :
    ∃ x ∈ keyPars Xs, (batchedRowsSending (Rc := Rc) (X := X) f Xs N).P = x.1 := by
  obtain ⟨w, hw⟩ : ∃ w, OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape = some w :=
    written_message
  have hl : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some w := by rw [one.lin]; exact hw
  refine ⟨(VerifiableInference.Desc.K1.parWKey Xs.Y.k.oneTime w
      (VerifiableInference.Desc.Key.groupsTold Xs.Y.told.1
        (VerifiableInference.Desc.Key.rootsBefore Xs.Y.D.1
          (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1))
        (VerifiableInference.Desc.Key.rootsAt Xs.Y.D.1
          (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1))),
      K1.rideOf (K1.wFold Xs.Y.k.oneTime.lin)), ?_, ?_⟩
  · unfold keyPars
    refine List.mem_append_right _ ?_
    show _ ∈ ((OnBytes.linMessageW Xs.Y.k.oneTime.lin).map _).toList
    rw [hl]
    exact List.mem_singleton.2 rfl
  · unfold batchedRowsSending AtPublicFiles.Key.wJob
    rw [hl]
    rfl

/-- The numbers, the place and the table sent along of W's sending, at the written shape. -/
theorem keyW_numbers (one : AtPublicFiles.KeyBook.OneFull Xs.Y.k.oneTime) (N : H2U.PlaceNums)
    (f : W₀ → Weights) :
    (batchedRowsSending (Rc := Rc) (X := X) f Xs N).P.codes = Lk6.AtPlan.keyFull.codes ∧
      (batchedRowsSending (Rc := Rc) (X := X) f Xs N).P.sent =
        (OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape).getD #[] ∧
      (batchedRowsSending (Rc := Rc) (X := X) f Xs N).P.place = AtPublicFiles.KeyBook.wPlace ∧
      (batchedRowsSending (Rc := Rc) (X := X) f Xs N).ride = AtPublicFiles.KeyBook.rideW := by
  obtain ⟨w, hw⟩ : ∃ w, OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape = some w :=
    written_message
  have hl : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some w := by rw [one.lin]; exact hw
  unfold batchedRowsSending AtPublicFiles.Key.wJob
  rw [hl, hw]
  exact ⟨one.codes, AtPublicFiles.KeyBook.sendingPar_sent _ _ _ _ _, rfl, rfl⟩

end Pars

section Clear
variable {W₀ Rc : Type} {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K₀ : AtPublicFiles.KeyBook.KeyPub}

/-- The order of the description's places is the order of the written ones. -/
theorem order_named (scope : VerifierAndGoals.InScope Z = true) (h : AtPublicFiles.AtFiles.KeyNamed Z Xs N Pl) :
    ProofFile.Honest.orderOf (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl) = writtenOrder := by
  obtain ⟨r1, r2, r3⟩ := AtPublicFiles.KeyBook.places_named scope h
  unfold ProofFile.Honest.orderOf writtenOrder
  rw [places_of_rows r1, places_of_rows r2, places_of_rows r3, List.map_append, List.map_append]

/-- **The book is clear at the sender of the index masks, at the key file's own numbers.** -/
theorem index_clear (one : AtPublicFiles.KeyBook.OneFull Xs.Y.k.oneTime)
    (hK : AtPublicFiles.KeyBook.fullPub = some K₀) {X : Type} :
    BookClearAny (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := X) Xs).P (fun _ => none)
      (AtPublicFiles.KeyBook.keyBook K₀) writtenOrder ⟨AtPublicFiles.KeyBook.idxPlace, 0⟩ := by
  refine (OnBytes.SendSim.At.bookClearAnyB_iff _ _).1 ?_
  rw [clear_same (P' := parIndexMasks) _ one.codes ?_]
  · exact AtPublicFiles.KeyBook.of_atFull index_clear_full hK
  · refine (AtPublicFiles.KeyBook.sendingPar_sent _ _ _ _ _).trans ?_
    rw [one.idx]
    show _ = ([("the index masks", #[Lk6.AtPlan.keyFull.once.input])].flatMap (·.2.toList)).toArray
    simp

/-- **The book is clear at the sender of the multiplicities.** -/
theorem multiplicities_clear (one : AtPublicFiles.KeyBook.OneFull Xs.Y.k.oneTime)
    (hK : AtPublicFiles.KeyBook.fullPub = some K₀) {X : Type} (f : W₀ → Weights) :
    BookClearAny (multiplicitiesSending (Rc := Rc) (X := X) f Xs).P AtPublicFiles.KeyBook.rideMsg
      (AtPublicFiles.KeyBook.keyBook K₀) writtenOrder ⟨AtPublicFiles.KeyBook.msgPlace, 0⟩ := by
  refine (OnBytes.SendSim.At.bookClearAnyB_iff _ _).1 ?_
  rw [clear_same (P' := parMultiplicities) _ one.codes ?_]
  · exact AtPublicFiles.KeyBook.of_atFull multiplicities_clear_full hK
  · refine (AtPublicFiles.KeyBook.sendingPar_sent _ _ _ _ _).trans ?_
    rw [one.ranges]
    show _ = ([("the lookups' own message and what rides with it",
      OnBytes.Wf.messageOf Lk6.AtPlan.keyFull.ranges.x)].flatMap (·.2.toList)).toArray
    simp

/-- **The book is clear at the sender of W.** -/
theorem messageW_clear (one : AtPublicFiles.KeyBook.OneFull Xs.Y.k.oneTime)
    (hK : AtPublicFiles.KeyBook.fullPub = some K₀) {X : Type} (f : W₀ → Weights) :
    BookClearAny (batchedRowsSending (Rc := Rc) (X := X) f Xs N).P AtPublicFiles.KeyBook.rideW
      (AtPublicFiles.KeyBook.keyBook K₀) writtenOrder ⟨AtPublicFiles.KeyBook.wPlace, 0⟩ := by
  obtain ⟨hc, hs, -, -⟩ := keyW_numbers (Rc := Rc) (X := X) Xs one N f
  refine (OnBytes.SendSim.At.bookClearAnyB_iff _ _).1 ?_
  rw [clear_same (P' := parMessageW) _ hc ?_]
  · exact AtPublicFiles.KeyBook.of_atFull messageW_clear_full hK
  · rw [hs]
    show _ = ([("W and what rides with it",
      (OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape).getD #[])].flatMap (·.2.toList)).toArray
    simp

end Clear

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.send_row_good
#print axioms AtPublicFiles.OfflineRows.written_message
#print axioms AtPublicFiles.OfflineRows.keyIdx_pars
#print axioms AtPublicFiles.OfflineRows.keyMsg_pars
#print axioms AtPublicFiles.OfflineRows.keyW_pars
#print axioms AtPublicFiles.OfflineRows.keyW_numbers
#print axioms AtPublicFiles.OfflineRows.clear_same
#print axioms AtPublicFiles.OfflineRows.order_named
#print axioms AtPublicFiles.OfflineRows.index_clear
#print axioms AtPublicFiles.OfflineRows.multiplicities_clear
#print axioms AtPublicFiles.OfflineRows.messageW_clear
