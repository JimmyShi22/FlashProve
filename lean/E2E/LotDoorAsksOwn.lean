-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotDoorAsksOwn.lean: our copy of the structure «what the door asks of an earlier thread and its letter» (AtPublicFiles.LotField.DoorAsks, E2E/LotFieldFirstLaw.lean) gives the door's own
(AtPublicFiles.KeyLastChain.DoorAsks, E2E/KeyLastTerm.lean): the four fields are the same. General in the thread, the letter and the border. Nothing on any property.
-/
import E2E.LotFieldFirstLaw
import E2E.KeyLastTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.LotField
open ProofFile.Honest

/-- **Our copy of the structure gives the door's own.** -/
theorem doorAsks_own {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} {T : Thread Bk S Cl V W Y Pb}
    {Said : Nat → Coins Bk → Mid W Y → Prop} {n : Nat} (D : DoorAsks T Said n) :
    AtPublicFiles.KeyLastChain.DoorAsks T Said n :=
  ⟨D.one, D.state, D.field, D.next⟩

end AtPublicFiles.LotField

#print axioms AtPublicFiles.LotField.doorAsks_own
