-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ChainErr.lean: the error counts of the rounds after the link's fifth, written out.

This file has the blocks' error counts of those rounds in a row (`tailErr`), for rounds that are
variables, so that no number is computed.


Main definitions: `wOf d`, the sampler's number for the written round d; `tailErr`.
Main theorem.


 `err1_one`        the count of a sending is 0 where the list has at most one member.

Not claimed. Nothing on the sizes of the entries.
-/
import OnBytes.Slice.BaseAt
import OnBytes.Slice.BatAt
import OnBytes.Slice.ChainOf
import OnBytes.Slice.CsJoint
import OnBytes.Slice.FoldAt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run
open scoped ENNReal

/-- The number in the law of the format's sampler, for the written round d. -/
abbrev wOf (d : PQ.RD) : ℕ := (bsRound .two d.entry d.kind).w

/-- The count of a sending is 0 where the list has at most one member. -/
theorem err1_one {s s' : Sg} (hf : CsFit s s') : (csSw hf).W.err1 1 = 0 :=
  Nat.zero_mul _

section
variable (S : Sz) (hf12 : CsFit toySg1 toySg2) (hf23 : CsFit toySg2 toySg3) (eU e2 e3 : ℕ)
  (dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB : PQ.RD)

/-- The blocks' error counts in a row, for any rounds. -/
def tailErr :
    Err (PQ.uL (ckP .two) (Tail.all ⟨dA, dE1, dT1, dS2, dC1, dE2, dT2, dS3, dC2, dL, dB⟩)) :=
  (batErr S 1 dA,
    Err.app (foldErr toySg1 dE1 dT1 (fun _ => 1) (fun _ => eU + 1) (fun _ => eU + 1)
      (fun _ => eU + 1))
    (Err.app (csErr hf12 eU 1 dS2 dC1)
    (Err.app (foldErr toySg2 dE2 dT2 (fun _ => 1) (fun _ => e2 + 1) (fun _ => e2 + 1)
      (fun _ => e2 + 1))
    (Err.app (csErr hf23 e2 1 dS3 dC2) (baseErr toySg3 e3 (e3 + 1) 1 dL dB)))))

end



end OnBytes.Slice

#print axioms OnBytes.Slice.err1_one
