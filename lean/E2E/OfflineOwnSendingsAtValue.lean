-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnSendingsAtValue.lean: WHAT THE THREE SENDINGS BEHIND THE KEY FILE's OWN PROXIMITY TEST SEND, AT THE OFFLINE PROVER's
OWN SENDERS (`valueAt`, E2E/KeyValueHolds.lean), in scope: the written public data. These are the three premises hI, hW, hO
of E2E/OfflineOwnFolds.lean's `asks_reached` and of what stands on it.

  `parIK_sent`, `parWK_sent`, `omega_shape_written`   the written side: two by unfolding, one a kernel line
  `own_sendings_at_value`   the index masks' sending, W's sending, Omega's shape
  `own_half_at_value`       the value's field `own` is the pair behind the guard at these three: by unfolding

Limits. In scope (`KeySourced`, `InScope`). On public data alone: what is sent as a notice, not what a table holds.
Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineRowsAtValue
import E2E.KeyValueHolds
import E2E.KeyJobW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14 (jobOmega)
open ProofFile.Honest.K12.Light (askOf)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open OnBytes.Slice (GF)
open Lk6.AtPlan (keyFull)
open AtPublicFiles.KeyFile (KeyInst KeyParts randK14)
open AtPublicFiles.KeyBook (OneFull sendingPar_sent)
open AtPublicFiles.KeyValues (WitK oneOf batchedRowsSending indexMaskSending)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.KeyLay (parIK parWK shapeOK proverSideOfGuardedSending)
open AtPublicFiles.AtFiles (KeySourced five_sourced)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open VerifierAndGoals (PublicFiles InScope)

/-- What the written index masks' sending sends. -/
theorem parIK_sent : parIK.sent = #[keyFull.once.input] := by
  show ([("the index masks", #[keyFull.once.input])].flatMap (·.2.toList)).toArray = _
  simp

/-- What the written sending of W sends. -/
theorem parWK_sent : parWK.sent = (OnBytes.linMessageW keyFull.once.shape).getD #[] := by
  show ([("W and what rides with it", (OnBytes.linMessageW keyFull.once.shape).getD #[])].flatMap
    (·.2.toList)).toArray = _
  simp

/-- Omega's shape at the written plan. -/
theorem omega_shape_written : ((jobOmega ⟨QK, 0⟩).Q.sent.getD 0 default).shape = shapeOK := by
  decide +kernel

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **The three sendings send the written public data.** -/
theorem own_sendings_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (indexMaskSending (W₀ := W₀) (Rc := Rc) (X := Unit) Xs).P.sent = parIK.sent ∧
      (batchedRowsSending (Rc := Rc) (X := Unit) f Xs N).P.sent = parWK.sent ∧
      ∀ n, ((jobOmega ⟨parKey Xs Pl, n + 0⟩).Q.sent.getD 0 default).shape = shapeOK := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  obtain ⟨J, eJ, -, -, -, hsent, -⟩ := keyW_written (W₀ := W₀) (Rc := Rc) Xs N f one
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [parIK_sent, ← one.idx]
    exact sendingPar_sent _ _ _ _ _
  · rw [parWK_sent, eJ]
    exact hsent
  · have e : parKey Xs Pl = QK := par_sourced hs scope
    rw [e]
    exact omega_shape_written

/-- **The value's own half.** -/
theorem own_half_at_value :
    (valueAt K' Xs N Pl f g inR d pU pO ent groups first).own =
      proverSideOfGuardedSending Xs N Pl (indexMaskSending Xs) (batchedRowsSending f Xs N) ⟨parKey Xs Pl, 0⟩ id
        (askOf ⟨parKey Xs Pl, 0⟩ (fun w => f w.w₀) fun w => randK14 (g w.rc 0)) := rfl

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.parIK_sent
#print axioms AtPublicFiles.OfflineRows.parWK_sent
#print axioms AtPublicFiles.OfflineRows.omega_shape_written
#print axioms AtPublicFiles.OfflineRows.own_sendings_at_value
#print axioms AtPublicFiles.OfflineRows.own_half_at_value
