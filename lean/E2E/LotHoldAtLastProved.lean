-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotHoldAtLastProved.lean: THE PREMISE hold OF last_done | last_laid AT THE LAST THREAD AT THE VALUE: LotHoldAtLast
(E2E/LotHoldAtLast.lean) holds.

  lotHoldAtLast   THE JOIN of two laws: a stand at border 2 has the thread's (H) as its first clause; tables_of_hand
                  (E2E/OfflineTablesLaid.lean: at ownThread, of which lastThread is an instance) turns it into TablesAreLaid; lot_p3
                  (E2E/LotTreesSentBeforeOwnTestProved.lean) gives OldAt

No new content: three calls. lot_p3's other premises: scope, KeySourced (sourced_of_ok), the description's return, fullPub, the own
test's place (place_own, E2E/KeyLastChain), the book's lending: the statement's own.
Limits. Those of the two laws: lot_p3 rests on takenAtTheOwnTest (Johnson/Desc/ProofFile/Honest/K12/Part4/OwnTaken.lean); beneath it 60 lines are
closed by evaluation in Lean's kernel («decide +kernel»: 30 in OwnTakenVectorW.lean, 16 in OwnTakenOmega.lean, 14 in OwnTakenIndexMasks.lean, the same
folder). That a stand at border 2 exists, or that the book lends there, is not shown here: where neither holds the statement is idle.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotHoldAtLast
import E2E.KeyThePartsFacts
import E2E.OfflineTablesLaid
import E2E.LotTreesSentBeforeOwnTestProved

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.Lots

theorem lotHoldAtLast : LotHoldAtLast := by
  intro Z d K₀ P₁ Wt live hd scope hK ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ Q S₁ w x k st m E c hT hc
  have hs := sourced_of_ok live hd
  exact AtPublicFiles.KeyLastChain.Lots.lot_p3 (files := Z) (D := d) (K₀ := K₀) k m E c scope hs hd hK
    (AtPublicFiles.KeyLastChain.place_own hs scope)
    hc (AtPublicFiles.OfflineRows.tables_of_hand Z₀ d Q _ _ _ _ tk tt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs scope k m E
      hT.1.1)

end AtPublicFiles.AtFiles.HonestTerm.Lots

#print axioms AtPublicFiles.AtFiles.HonestTerm.Lots.lotHoldAtLast
