-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineObjectIsProver.lean: the named value's prover is the prover of the offline file's rows, in the
five equations of `IsProvK` (E2E/KeyExact.lean), at the rows `rowsAtTheTerm`
(E2E/OfflineObjectAtTheTerm.lean).

  `object_stores`      the prover's stored columns are the committer's (`cmKey files`, E2E/KeyExact.lean), at
                       item 0 and nowhere else: by `stored_at_parts` (E2E/KeyStoredAtValue.lean)
  `object_isProver`    `IsProvK` at `thePartsAt files`: the key by unfolding, the stored columns by the line
                       above, the three lists by `object_rows`

In scope, at a description that is sourced at the public files. Equations between terms. Nothing says that
any row is good. Nothing on any property.
-/
import E2E.OfflineObjectAtTheTerm
import E2E.KeyStoredAtValue
import E2E.KeyExact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open OnBytes (TableKey)
open AtPublicFiles.KeyStoredTie (stored_at_parts)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope)

variable {files : PublicFiles}

/-- **The named value's prover stores the committer's table**, at item 0 and nowhere else. -/
theorem object_stores {d : OfflineDescription} (h : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true) :
    ∀ w rc it x, ((thePartsAt files).prover d).stored w rc it x =
      if it == 0 then (cmKey files).enc w rc x else none :=
  fun w rc it x => stored_at_parts h (sized_sourced hs scope) w rc it x

/-- **The named value's prover is the prover of the offline file's rows.** -/
theorem object_isProver {d : OfflineDescription} (h : offlineDescription files = .ok d)
    (hs : KeySourced files d.source d.numbers d.later) (scope : InScope files = true)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
      Unit Unit Unit) :
    IsProvK files (keyFileDescription d.source d.numbers d.later) (thePartsAt files).book
      (rowsAtTheTerm (files := files) d S c) ((thePartsAt files).prover d) where
  key := rfl
  stored := object_stores h hs scope
  first := (object_rows h S c).1
  shared := (object_rows h S c).2.1
  second := (object_rows h S c).2.2.1

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.object_stores
#print axioms AtPublicFiles.OfflineRows.object_isProver
