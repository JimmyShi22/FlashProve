-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/ShareSlot.lean: THE SMALLNESS TEST: ITS SHARE OF THE TESTS BEHIND
THE ADDING (`k8First`, `k8Second`: Johnson/Desc/ProofFile/Honest/K8/Share.lean) DOES NOT READ THE
FIELD lsTail OF THE TEST's DATA: so it says the same in front of the run that lays that field and
behind it. Lemmas on this library's own definitions; none of its goals.

  `k8First_slot`, `k8Second_slot`   each at { tl with lsTail := x } is what it is at tl
Limits. The data alone: what a run that stands between changes in the ledger F is not looked at.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Share

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model

theorem k8First_slot (tl : HTailF2) (x : Array E) (nU : Array Nat) (F : Fork) :
    k8First { tl with lsTail := x } nU F = k8First tl nU F := rfl

theorem k8Second_slot (tl : HTailF2) (x : Array E) (F : Fork) :
    k8Second { tl with lsTail := x } F = k8Second tl F := rfl

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8First_slot
#print axioms ProofFile.Honest.K8.k8Second_slot
