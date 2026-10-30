-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingWordsHeard.lean: at a stand the challenges that the
job's rows read are those that the switch's lot reads: heardL drops the last two of what is heard,
and the lot takes the first fx.

  heardL_at_stand   the equation of lists

By what. The thread's clause on rounds (Thread.Fit), drawsFit_length (Honest/Law/Along.lean).

Hypotheses. hF: that clause at the stand; h0: nothing stands in front of the chain; hlen: the blocks
in front declare fx + 2 rounds: front_rounds_L (AtProof/CutAtL.lean) has 48237 at 354.

Limits. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobL
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- **The job and the lot read the same challenges.** -/
theorem heardL_at_stand (T : Thread Bk S Cl V W X Pb) {b fx : ℕ} {m : Mid W X} (hF : T.Fit b m)
    (h0 : T.ahead = []) (hlen : (declsTo T.bs b).length = fx + 2) :
    heardL (frontOf m) = (m.st.heard ++ []).take fx := by
  have e := ProofFile.Honest.drawsFit_length _ _ hF
  rw [h0, List.nil_append, hlen] at e
  show m.st.heard.take (m.st.heard.length - 2) = _
  rw [List.append_nil, e, Nat.add_sub_cancel]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.heardL_at_stand
