-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RunTied.lean: THE TIE `Tied` (Honest/K9/RunFrame.lean) BETWEEN A KIND's OWN RUN OF CLAIMS AND THE RUN
THAT STANDS IN THE DESCRIPTION's LIST, wherever the segment's hearing block is the kind's block laid alone
(`IM.LaidAlone`, Johnson/IMR/SeatForm.lean). The description's makers wrap each run of such a block in one guard: behind
the run the reply must be as it was in front (`IM.guardRun`, `IM.claims_lookup`). So the run in the list is the kind's own
run behind that guard, and the tie holds both ways.

  **`tied_of_alone`**   entry j of the order names block number o.1 and the run o.2; that block is b' laid alone; b' states
                      the run f under the name o.2 ⊢ `Tied Lk j f`

Limits. Which block is laid alone at which number of which segment is said by the library's theorems on the seats
(Johnson/IMR/K3Seat.lean, K4Seat.lean, K5Seat.lean, K6Seat.lean, K8Seat.lean); none is called here. This file proves no
property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.RunFrame
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **The tie, at a block that is laid alone.** -/
theorem tied_of_alone {Lk : Link S Claim} {j : ℕ} {o : ℕ × String} {b b' : Block S Claim} {name : String}
    {a : Place} {f : ClaimsRun} (ho : Lk.order[j]? = some o) (hb : Lk.hear[o.1]? = some b)
    (hl : IM.LaidAlone ProofFile.sameReply b b' name a) (hf : b'.claims.lookup o.2 = some f) : Tied Lk j f := by
  have hrun : claimsRunOf Lk.hear o = some (IM.guardRun ProofFile.sameReply f) := by
    unfold claimsRunOf
    rw [hb]
    show b.claims.lookup o.2 = _
    rw [IM.claims_lookup hl, hf]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro o' ho'
    obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
    exact ⟨_, hrun⟩
  · intro o' r ho' hr
    obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
    obtain rfl : IM.guardRun ProofFile.sameReply f = r := Option.some.inj (hrun.symm.trans hr)
    exact guardedRun_under ProofFile.sameReply f
  · intro o' r ho' hr m t z hz hrep
    obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
    obtain rfl : IM.guardRun ProofFile.sameReply f = r := Option.some.inj (hrun.symm.trans hr)
    refine guardedRun_yes ProofFile.sameReply f m t z hz ?_
    unfold ProofFile.sameReply
    rw [hrep]
    exact beq_self_eq_true _

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.tied_of_alone
