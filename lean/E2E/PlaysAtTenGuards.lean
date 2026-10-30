-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/PlaysAtTenGuards.lean

What the test on G_omega opens of older trees, against the sendings' tables: closed numbers, first by
Lean's evaluator, then by the kernel. It can say no.

  `wide3`    every opening with an old source is own n below 3, at the width `tblW`
  `wide_O`, `wide_O_bent`   at `piKOFull`, seven trees in front: yes; at eight, own 7 would be old: no

Limits. Public numbers at QK. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.PlaysAtNineGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.PlaysAtNine
open ProofFile.Honest.K12 (oldSrc)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc (Block)
open H2K.Member (piKOFull)

/-- Every old opening is own n below 3, at the width `tblW`. -/
def wide3 (p : P12) (sent : Nat) : Bool :=
  (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.all fun d => d.opens.all fun o =>
    !oldSrc sent o.2 || match o.2 with
      | .own n => decide (n < 3) && o.1.W == tblW n
      | .taken _ _ => false

#eval ((proximityTestKind guardedProximityTestParts piKOFull : Block T12 Unit).rounds.flatMap (·.opens)).map fun o =>
  (AtPublicFiles.KeyOpens.srcNum o.2, o.1.W)

-- Foretold: yes at 7. Control: no at 8.
#guard wide3 piKOFull 7
#guard !wide3 piKOFull 8

theorem wide_O : wide3 piKOFull 7 = true := by decide +kernel

theorem wide_O_bent : wide3 piKOFull 8 = false := by decide +kernel

end AtPublicFiles.PlaysAtNine

#print axioms AtPublicFiles.PlaysAtNine.wide3
#print axioms AtPublicFiles.PlaysAtNine.wide_O
#print axioms AtPublicFiles.PlaysAtNine.wide_O_bent
