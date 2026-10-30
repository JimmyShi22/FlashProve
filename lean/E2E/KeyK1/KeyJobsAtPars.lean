-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyK1/KeyJobsAtPars.lean: THE THREE SENDINGS OF THE KEY FILE's HONEST PROVER (indexMaskSending, multiplicitiesSending, batchedRowsSending,
E2E/KeyFirstSends.lean) STAND AT THE PUBLIC NUMBERS keyPars (Johnson/SendSim/Seat/AtKeyPars.lean) AT
WHICH THE SIMULATOR's LAW fieldsAtKey_all (Johnson/SendSim/Seat/AtKey.lean) SPEAKS.

  rideMsg_written, rideW_written   the written rides are the folds' own at the written sizes.
  **keyJobs_in_pars**              under ChainPins: all three are entries of keyPars Xs.

Limits. At the written sizes alone (ChainPins). On the jobs' public numbers alone: their data are
free in the law. Nothing on any property of a protocol.
-/
import E2E.KeyFirstSends
import Johnson.SendSim.Seat.KeyReadsAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyK1
open OnBytes OnBytes.Params
open ProofFile.Honest.K1 (SendJob rideOf wFold)
open OnBytes.SendSim.Seat (keyPars msgFold)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.KeyValues (indexMaskSending multiplicitiesSending batchedRowsSending oneOf)
open AtPublicFiles.KeyBook (rideMsg rideW)
open Johnson.KB4 (ChainPins)
open Lk6.AtPlan (keyFull)

theorem ride_of_fold {x : Option (Nat × FoldShape)} {a b c : Nat}
    (e : x.map (fun y => (y.1, y.2.layout.k, y.2.layout.h)) = some (a, b, c)) (k : Nat) :
    rideOf x k = if k == a then some ⟨b, c⟩ else none := by
  cases x with
  | none => cases e
  | some y =>
    obtain ⟨n, s⟩ := y
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    rfl

theorem rideMsg_written : rideOf (msgFold keyFull.ranges.x) = rideMsg := by
  have e : (msgFold keyFull.ranges.x).map (fun y => (y.1, y.2.layout.k, y.2.layout.h)) =
      some (1, 4, 4) := by decide +kernel
  funext k
  rw [ride_of_fold e]
  rfl

theorem rideW_written : rideOf (wFold keyFull.once.shape) = rideW := by
  have e : (wFold keyFull.once.shape).map (fun y => (y.1, y.2.layout.k, y.2.layout.h)) =
      some (1, 5, 1) := by decide +kernel
  funext k
  rw [ride_of_fold e]
  rfl

variable {W₀ Rc X : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

theorem keyIdx_mem : ((indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P,
    (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride) ∈ keyPars Xs := by
  apply List.mem_append_left
  exact List.mem_cons_self

theorem keyMsg_mem (h : ChainPins Xs N Pl) (f : W₀ → ProofFile.Honest.Weights) :
    ((multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P,
      (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride) ∈ keyPars Xs := by
  have e : rideOf (msgFold Xs.Y.k.oneTime.ranges) = rideMsg := by
    rw [h.ranges]
    exact rideMsg_written
  apply List.mem_append_left
  apply List.mem_cons_of_mem
  show _ ∈ [(_, rideOf (msgFold Xs.Y.k.oneTime.ranges))]
  rw [e]
  exact List.mem_cons_self

theorem keyW_mem (h : ChainPins Xs N Pl) (f : W₀ → ProofFile.Honest.Weights) :
    ((batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P,
      (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride) ∈ keyPars Xs := by
  have e : rideOf (wFold Xs.Y.k.oneTime.lin) = rideW := by
    rw [h.lin]
    exact rideW_written
  have hs : (linMessageW Xs.Y.k.oneTime.lin).isSome = true := by
    rw [h.lin]
    have := AtPublicFiles.KeyBook.rides_full.2.2
    cases hm : linMessageW keyFull.once.shape with
    | none =>
      rw [hm] at this
      cases this
    | some _ => rfl
  obtain ⟨msg, hm⟩ := Option.isSome_iff_exists.1 hs
  apply List.mem_append_right
  unfold batchedRowsSending AtPublicFiles.Key.wJob
  rw [hm]
  simp only [Option.map_some, Option.getD_some, Option.toList_some]
  show _ ∈ [(_, rideOf (wFold Xs.Y.k.oneTime.lin))]
  rw [e]
  exact List.mem_cons_self

/-- **THE THREE SENDINGS STAND AT keyPars.** -/
theorem keyJobs_in_pars (h : ChainPins Xs N Pl) (f : W₀ → ProofFile.Honest.Weights) :
    ((indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P,
        (indexMaskSending Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride) ∈ keyPars Xs ∧
      ((multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P,
        (multiplicitiesSending f Xs : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride) ∈ keyPars Xs ∧
      ((batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).P,
        (batchedRowsSending f Xs N : SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X).ride) ∈ keyPars Xs :=
  ⟨keyIdx_mem, keyMsg_mem h f, keyW_mem h f⟩

end AtPublicFiles.KeyK1

#print axioms AtPublicFiles.KeyK1.rideMsg_written
#print axioms AtPublicFiles.KeyK1.rideW_written
#print axioms AtPublicFiles.KeyK1.keyJobs_in_pars
