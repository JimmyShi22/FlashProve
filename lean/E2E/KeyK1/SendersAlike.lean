-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyK1/SendersAlike.lean: THE KEY FILE's OFFLINE PROVER's TWO K1 SENDINGS THAT ITS OWN TEST READS (indexMaskSending, batchedRowsSending: E2E/KeyFirstSends.lean) AGAINST THE WRITTEN
PARAMETERS parIK, parWK (E2E/KeyJobW.lean), under ChainPins: FIELD BY FIELD: place, codes, gp, work, parts (so sent) ARE THE SAME; groups IS NOT ASKED, AND DIFFERS.

  idx_alike, w_alike   the five fields, and the ride
  idx_sent, w_sent     so the messages in the order of sending
  ParAlike.eq          so P is P' with P's own groups laid in: one equation, for a law that is general in the groups
  groups_differ        a closed fact on the written list keyParsW and on parIK, parWK
  idx_groups, w_groups, **idx_ne, w_ne**   under ChainPins the two sendings' parameters name groups ([[300]]; [[300], []]): SO THEY ARE NOT parIK, parWK
  par_key              under ChainPins the shared chain's parameters at the key are QK
  **own_senders_fields**   the seven equations of IOP's OwnSenders (K12/AtKey/OwnJob.lean:56), at indexMaskSending, batchedRowsSending and ⟨parKey Xs Pl, 0⟩

Limits. Under ChainPins (paid in scope at what the key file's makers return: chainPins_at_made). Public numbers alone. Nothing on completeness, soundness or hiding.
-/
import E2E.KeyK1.KeyJobsAtPars
import E2E.KeyJobW
import E2E.KeySharedThread
import E2E.KeyShapeSharedFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyK1
open OnBytes OnBytes.Params
open ProofFile.Honest.K1 (SendJob)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.KeyValues (indexMaskSending multiplicitiesSending batchedRowsSending oneOf)
open AtPublicFiles.KeyBook (rideW)
open AtPublicFiles.KeyLay (parIK parWK)
open Johnson.KB4 (ChainPins)
open Lk6.AtPlan (keyFull)

variable {W₀ Rc X : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- Two places' parameters agree in all but the groups. -/
structure ParAlike (P P' : VerifiableInference.Desc.K1.Par) : Prop where
  place : P.place = P'.place
  codes : P.codes = P'.codes
  gp : P.gp = P'.gp
  work : P.work = P'.work
  parts : P.parts = P'.parts

theorem ParAlike.sent {P P' : VerifiableInference.Desc.K1.Par} (h : ParAlike P P') : P.sent = P'.sent := by
  unfold VerifiableInference.Desc.K1.Par.sent
  rw [h.parts]

/-- P is P' with P's own groups. -/
theorem ParAlike.eq {P P' : VerifiableInference.Desc.K1.Par} (h : ParAlike P P') :
    P = { P' with groups := P.groups } := by
  obtain ⟨a, b, c, d, e, g⟩ := P
  obtain ⟨a', b', c', d', e', g'⟩ := P'
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-- **The index masks' sending.** -/
theorem idx_alike (h : ChainPins Xs N Pl) :
    ParAlike (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P parIK ∧
      (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = fun _ => none := by
  refine ⟨⟨rfl, h.codes, ?_, rfl, ?_⟩, rfl⟩
  · show VerifiableInference.Desc.Key.groundParOf Xs.Y.k.oneTime = _
    unfold VerifiableInference.Desc.Key.groundParOf
    rw [h.samples]
    rfl
  · show [("the index masks", #[Xs.Y.k.oneTime.indexMasks])] = _
    rw [h.idx]
    rfl

/-- **W's sending.** -/
theorem w_alike (h : ChainPins Xs N Pl) (f : W₀ → ProofFile.Honest.Weights) :
    ParAlike (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P parWK ∧
      (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = rideW := by
  have hs : (linMessageW Xs.Y.k.oneTime.lin).isSome = true := by
    rw [h.lin]
    have := AtPublicFiles.KeyBook.rides_full.2.2
    cases hm : linMessageW keyFull.once.shape with
    | none =>
      rw [hm] at this
      cases this
    | some _ => rfl
  obtain ⟨msg, hm⟩ := Option.isSome_iff_exists.1 hs
  have hm' : linMessageW keyFull.once.shape = some msg := by rw [← h.lin]; exact hm
  unfold batchedRowsSending AtPublicFiles.Key.wJob
  rw [hm]
  simp only [Option.map_some, Option.getD_some]
  refine ⟨⟨rfl, h.codes, ?_, rfl, ?_⟩, trivial⟩
  · show VerifiableInference.Desc.Key.groundParOf Xs.Y.k.oneTime = _
    unfold VerifiableInference.Desc.Key.groundParOf
    rw [h.samples]
    rfl
  · show [("W and what rides with it", msg)] = [("W and what rides with it", (linMessageW keyFull.once.shape).getD #[])]
    rw [hm']
    rfl

theorem idx_sent (h : ChainPins Xs N Pl) :
    (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.sent = parIK.sent :=
  (idx_alike (W₀ := W₀) (Rc := Rc) (X := X) h).1.sent

theorem w_sent (h : ChainPins Xs N Pl) (f : W₀ → ProofFile.Honest.Weights) :
    (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.sent = parWK.sent :=
  (w_alike (Rc := Rc) (X := X) h f).1.sent

set_option maxRecDepth 1000000 in
/-- **A closed fact**: the description's own parameters at the written sizes name groups; parIK and parWK name none. -/
theorem groups_differ :
    (OnBytes.SendSim.Seat.keyParsW.map fun x => x.1.groups) = [[[300]], [[100], []], [[300], []]] ∧
      parIK.groups = [] ∧ parWK.groups = [] := by
  refine ⟨by decide +kernel, rfl, rfl⟩

set_option maxRecDepth 1000000 in
/-- The groups told at the two places, at the written rounds and tenants. -/
theorem groups_written :
    VerifiableInference.Desc.Key.groupsTold Johnson.KB4.toldKeyFull.1 0
        (VerifiableInference.Desc.Key.rootsAt Johnson.KB8.declKeyFull.1 0) = [[300]] ∧
      VerifiableInference.Desc.Key.groupsTold Johnson.KB4.toldKeyFull.1
        (VerifiableInference.Desc.Key.rootsBefore Johnson.KB8.declKeyFull.1
          (VerifiableInference.Desc.Key.lastSendRound Johnson.KB8.declKeyFull.1))
        (VerifiableInference.Desc.Key.rootsAt Johnson.KB8.declKeyFull.1
          (VerifiableInference.Desc.Key.lastSendRound Johnson.KB8.declKeyFull.1)) = [[300], []] := by
  refine ⟨by decide +kernel, by decide +kernel⟩

theorem idx_groups (h : ChainPins Xs N Pl) :
    (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.groups = [[300]] := by
  show VerifiableInference.Desc.Key.groupsTold Xs.Y.told.1 0
    (VerifiableInference.Desc.Key.rootsAt Xs.Y.D.1 0) = _
  rw [h.told₁, h.D₁]
  exact groups_written.1

theorem w_groups (h : ChainPins Xs N Pl) (f : W₀ → ProofFile.Honest.Weights) :
    (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.groups = [[300], []] := by
  have hs : (linMessageW Xs.Y.k.oneTime.lin).isSome = true := by
    rw [h.lin]
    have := AtPublicFiles.KeyBook.rides_full.2.2
    cases hm : linMessageW keyFull.once.shape with
    | none =>
      rw [hm] at this
      cases this
    | some _ => rfl
  obtain ⟨msg, hm⟩ := Option.isSome_iff_exists.1 hs
  unfold batchedRowsSending AtPublicFiles.Key.wJob
  rw [hm]
  simp only [Option.map_some, Option.getD_some]
  show VerifiableInference.Desc.Key.groupsTold Xs.Y.told.1
    (VerifiableInference.Desc.Key.rootsBefore Xs.Y.D.1 (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1))
    (VerifiableInference.Desc.Key.rootsAt Xs.Y.D.1 (VerifiableInference.Desc.Key.lastSendRound Xs.Y.D.1)) = _
  rw [h.told₁, h.D₁]
  exact groups_written.2

/-- **THE INDEX MASKS' SENDING's PARAMETERS ARE NOT parIK.** -/
theorem idx_ne (h : ChainPins Xs N Pl) :
    (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P ≠ parIK := fun e => by
  have g := idx_groups (W₀ := W₀) (Rc := Rc) (X := X) h
  rw [e] at g
  exact nomatch g

/-- **W's SENDING's PARAMETERS ARE NOT parWK.** -/
theorem w_ne (h : ChainPins Xs N Pl) (f : W₀ → ProofFile.Honest.Weights) :
    (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P ≠ parWK := fun e => by
  have g := w_groups (Rc := Rc) (X := X) h f
  rw [e] at g
  exact nomatch g

/-- Under ChainPins the shared chain's parameters at the key are the written ones. -/
theorem par_key (h : ChainPins Xs N Pl) :
    AtPublicFiles.KeySharedThread.parKey Xs Pl = AtPublicFiles.AtFiles.Full.QK := by
  show VerifiableInference.Desc.Key.sharedPar Xs.chains
    (VerifiableInference.Desc.Key.beforeSharedPoint Pl) = _
  rw [h.P]
  unfold VerifiableInference.Desc.Key.sharedPar
  rw [h.sized]
  rfl

/-- **THE SEVEN EQUATIONS OF OwnSenders**, in its fields' order: idxSent, idxCodes, idxRide, wSent, wCodes, wRide, sendPar. -/
theorem own_senders_fields (h : ChainPins Xs N Pl) (f : W₀ → ProofFile.Honest.Weights) :
    (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.sent = parIK.sent ∧
      (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.codes = parIK.codes ∧
      ((indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = fun _ => none) ∧
      (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.sent = parWK.sent ∧
      (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P.codes = parWK.codes ∧
      (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride = rideW ∧
      (⟨AtPublicFiles.KeySharedThread.parKey Xs Pl, 0⟩ : ProofFile.Honest.K14.SendPub).P = AtPublicFiles.AtFiles.Full.QK :=
  ⟨idx_sent h, (idx_alike (W₀ := W₀) (Rc := Rc) (X := X) h).1.codes, rfl, w_sent h f,
    (w_alike (Rc := Rc) (X := X) h f).1.codes, (w_alike (Rc := Rc) (X := X) h f).2, par_key h⟩

end AtPublicFiles.KeyK1

#print axioms AtPublicFiles.KeyK1.ParAlike.eq
#print axioms AtPublicFiles.KeyK1.idx_ne
#print axioms AtPublicFiles.KeyK1.w_ne
#print axioms AtPublicFiles.KeyK1.own_senders_fields
#print axioms AtPublicFiles.KeyK1.idx_alike
#print axioms AtPublicFiles.KeyK1.w_alike
#print axioms AtPublicFiles.KeyK1.groups_differ
