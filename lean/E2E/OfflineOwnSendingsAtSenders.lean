-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwnSendingsAtSenders.lean: E2E/OfflineOwnSendingsAtValue.lean's three equations AT THE OFFLINE FILE's SENDERS AT A DESCRIPTION
(`offlineSenders d`, E2E/KeyArgumentsAt.lean), in these senders' own fields: what the index masks' sending and the sending of W
send, and Omega's shape at every number, are the written public data. In scope.

  `senders_three`             the senders' fields idx, w, send are the description's own: by unfolding
  `own_sendings_at_senders`   the statement

Limits. In scope (`KeySourced`, `InScope`). On public data alone: what is sent as a notice, not what a table holds.
Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineOwnSendingsAtValue
import E2E.KeyArgumentsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest.K14 (jobOmega)
open ProofFile.Honest.Term
open AtPublicFiles.KeyValues (batchedRowsSending indexMaskSending)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyLay (parIK parWK shapeOK)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope)

variable {files : PublicFiles}

/-- The senders' three fields are the description's own. -/
theorem senders_three (d : OfflineDescription) :
    (offlineSenders (files := files) d).idx = indexMaskSending d.source ∧
      (offlineSenders (files := files) d).w = batchedRowsSending matrixReader d.source d.numbers ∧
      (offlineSenders (files := files) d).send = ⟨parKey d.source d.later, 0⟩ := ⟨rfl, rfl, rfl⟩

/-- **The three sendings send the written public data.** -/
theorem own_sendings_at_senders {Z : PublicFiles} (d : OfflineDescription)
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true) :
    (offlineSenders (files := files) d).idx.P.sent = parIK.sent ∧
      (offlineSenders (files := files) d).w.P.sent = parWK.sent ∧
      ∀ n, ((jobOmega ⟨(offlineSenders (files := files) d).send.P,
        n + (offlineSenders (files := files) d).send.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK :=
  own_sendings_at_value d.source d.numbers d.later matrixReader hs scope

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.senders_three
#print axioms AtPublicFiles.OfflineRows.own_sendings_at_senders
