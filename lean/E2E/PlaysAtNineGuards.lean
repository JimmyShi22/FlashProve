-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/PlaysAtNineGuards.lean

The declared widths of what the test on G_u opens of older trees, against the tables that the two
sendings send, as closed numbers, first by Lean's evaluator, then by the kernel. It can say no.

  `shapeWords`  the words of each table that a sending's messages make: no row is read
  `tblW`        the width of own tree n, at the two sendings' tables
  `wideAt`      every opening with an old source is own n, at that width
  `wide_U`, `wide_bent`   at `piKUFull`, three trees in front: yes; widths bent by one: no

Limits. Public numbers at QK. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyOpensGuards
import Johnson.Desc.ProofFile.Honest.K12.ColsReturn
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full
import E2E.KeyFixedLines

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.PlaysAtNine
open ProofFile.Honest.K14 (jobU jobOmega treesU)
open ProofFile.Honest.K12 (oldSrc)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc (Block)
open AtPublicFiles.AtFiles.Full (QK)
open H2K.Member (piKUFull)

/-- The words of each table of a sending. -/
def shapeWords (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) : List Nat :=
  ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).shapes.toList.map fun t =>
    t.mainWidth + t.maskWidth

/-- The width of own tree n. -/
def tblW (n : Nat) : Nat :=
  if n < treesU QK then
    (shapeWords (jobU ⟨QK, 0⟩).Q.codes (jobU ⟨QK, 0⟩).Q.sent).getD n 0
  else
    (shapeWords (jobOmega ⟨QK, 0⟩).Q.codes (jobOmega ⟨QK, 0⟩).Q.sent).getD (n - treesU QK) 0

/-- Every opening of the place's rounds with an old source is own n, at the width f n. -/
def wideAt (p : P12) (f : Nat → Nat) (sent : Nat) : Bool :=
  (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.all fun d => d.opens.all fun o =>
    !oldSrc sent o.2 || match o.2 with
      | .own n => o.1.W == f n
      | .taken _ _ => false

-- The widths, and what the rounds declare.
#eval (List.range 3).map tblW
#eval ((proximityTestKind guardedProximityTestParts piKUFull : Block T12 Unit).rounds.flatMap (·.opens)).map fun o =>
  (AtPublicFiles.KeyOpens.srcNum o.2, o.1.W)

-- Foretold: yes. Control: no.
#guard wideAt piKUFull tblW 3
#guard !wideAt piKUFull (fun n => tblW n + 1) 3

theorem wide_U : wideAt piKUFull tblW 3 = true := by decide +kernel

theorem wide_bent : wideAt piKUFull (fun n => tblW n + 1) 3 = false := by decide +kernel

end AtPublicFiles.PlaysAtNine

#print axioms AtPublicFiles.PlaysAtNine.shapeWords
#print axioms AtPublicFiles.PlaysAtNine.tblW
#print axioms AtPublicFiles.PlaysAtNine.wideAt
#print axioms AtPublicFiles.PlaysAtNine.wide_U
#print axioms AtPublicFiles.PlaysAtNine.wide_bent
