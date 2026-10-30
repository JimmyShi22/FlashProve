-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesLinesGuards.lean: the closed lines of the key file's
test on the ranges at its written place piKRFull, as tests with code, first by Lean's evaluator.
Each can say no.

  msgWords     the width of the table of the sending of the multiplicities
  seedsB       the test's tree number τ is sent in the round seedRound τ of its own rounds
  oldOpensB    every opening of the test's rounds with a source behind the trees sent in front is
               tree number 1, at the width w

Limits. Public numbers at piKRFull. Nothing is played, no coin, no table. Nothing on completeness,
soundness or hiding.
-/
import E2E.KeyThreadBase
import Johnson.Desc.K12.Law.PlaceKeyRangesFull
import Johnson.Desc.ProofFile.Honest.K12.FrontPlainAtKey
import Johnson.Desc.ProofFile.Honest.K12.ScriptLots
import Johnson.Desc.ProofFile.Honest.K12.ColsReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Block sendRound)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piKRFull)

/-- The words of the sending's first table. -/
def msgWords : Nat := (parKR.trees.getD 0 {}).mainWidth + (parKR.trees.getD 0 {}).maskWidth

/-- Each of the test's trees is sent in the round that seedRound names, and in no other. -/
def seedsB (p : P12) : Bool :=
  (List.range (p.nums.stages.length - 1)).all fun τ =>
    sendRound (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds τ == some (seedRound p.nums.stages τ)

/-- Every opening with an old source is tree number 1, at the width w. -/
def oldOpensB (p : P12) (w sent : Nat) : Bool :=
  (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.all fun d => d.opens.all fun o =>
    !oldSrc sent o.2 || match o.2 with
      | .own n => n == 1 && o.1.W == w
      | .taken _ _ => false

#eval msgWords
#eval (List.range 3).map fun τ =>
  (sendRound (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds τ, seedRound piKRFull.nums.stages τ)
#eval (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds.length

-- Foretold: yes. Then the controls: no.
#guard seedsB piKRFull
#guard oldOpensB piKRFull msgWords 2
#guard !oldOpensB piKRFull (msgWords + 1) 2
#guard !oldOpensB piKRFull msgWords 3
#guard (List.range 3).all fun τ =>
  sendRound (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds τ !=
    some (seedRound piKRFull.nums.stages τ + 1)
#guard piKRFull.nums.stages.length == 4
#guard ((proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).oracles.flatMap id).length + 1 ==
  piKRFull.nums.stages.length

end ProofFile.Honest.K12.AtKey
