-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/COracles.lean: what the three chains' blocks of WK
(Johnson/HB/LLHARD/KB4/WK.lean) say of the oracle messages that they send: 6, 11 and 4, and that,
with every tenant's groups struck, they are the tenants as told (toldKeyFull,
Johnson/HB/LLHARD/KB4/Told.lean) with the groups struck: a value typed by hand, tested against what
the blocks say. By evaluations in Lean's kernel, with one negative test (oracles_told_no).
What it is for. oracles_told holds the words of toldKeyFull (log-lengths, words, tenants' words,
degrees, flags) against what WK's blocks say. The three clauses "opened", "alone" and "grouped" in
the proof of key_planOk (Johnson/HB/LLHARD/KB4/Row.lean) read of a tree as told its place in the
chain, the number of its tenants, and each tenant's flag and groups: no log-length, no number of
words, no degree. The clause "made", which reads toldKeyFull whole, is a premise there (hmade).
Neither that file nor a file beneath it imports this one: it stands beside that theorem.
Limits. At the closed description WK alone. That Key.toldOfMade returns toldKeyFull is shown by
no theorem in this file or in the files that it imports. In another file,
Johnson.AtFull.KeyBack.toldOfMade_in_scope (Johnson/AtFull/KeyBack/InScopeNamed.lean) shows that
Key.toldOfMade m returns it, under three premises: the public files are in scope of the goals
(VerifierAndGoals.InScope), publicOfO returns on them, and m is what Key.madeAt then returns at the constant
digest Key.fixedDigest. The three premises are met at the library's written copy of the full-size
public files (VerifierAndGoals.storedPublicFiles: three terms written in Lean; no theorem
ties them to the repository's files): the first by VerifierAndGoals.inScope_full
(Johnson/Goal/Files/ScopeExample.lean), the other two by AtFullSide.Planner.theKeyLaid_zFull_returns
(AtFullSide/Planner/KeyLaidReturns.lean), at the format's second hash function (OnBytes.secondHashFunction) and
the same constant digest, not the files' own, in a side library outside the main library (one
constant beneath it passes Lean's kernel only at a larger thread stack; Lean's re-checker,
leanchecker, was run on it and fails there at each shell stack limit that was tried; the toolchain's
own replay passes it at a larger thread stack; so that constant has been checked by the kernel in
the build and by that replay, and by no independent program); no independent checker has replayed
any of the closed facts beneath it, and the full-size example's weights are synthetic. These last
two theorems speak of VerifierAndGoals.storedPublicFiles alone, not of other files in scope.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.WK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

/-- What the three chains' blocks say of the oracle messages that they send. -/
def oraclesW : List Oracle × List Oracle × List Oracle :=
  (oraclesOf WK.first.blocksInOrder, oraclesOf WK.shared.blocksInOrder, oraclesOf WK.second.blocksInOrder)

set_option maxRecDepth 1000000 in
theorem oracles_count :
    (oraclesW.1.length, oraclesW.2.1.length, oraclesW.2.2.length) = (6, 11, 4) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With every tenant's groups struck, they are the tenants as told with the groups struck. -/
theorem oracles_told :
    (oraclesW.1.map withoutGroups, oraclesW.2.1.map withoutGroups,
      oraclesW.2.2.map withoutGroups) =
    (toldKeyFull.1.map withoutGroups, toldKeyFull.2.1.map withoutGroups,
      toldKeyFull.2.2.map withoutGroups) := by decide +kernel

/-- The first sending's block where the index-mask message has one mask row more. -/
def sendRowMore : Block FirstState Claim :=
  sendIndexMasks (oneAt OnBytes.Params.recordSet.samples
    { Lk6.AtPlan.keyFull.once.input with shape := { Lk6.AtPlan.keyFull.once.input.shape with
        maskRows := Lk6.AtPlan.keyFull.once.input.shape.maskRows + 1 } }
    Lk6.AtPlan.keyFull.ranges.x Lk6.AtPlan.keyFull.codes Lk6.AtPlan.keyFull.once.shape) pieces
    [[300]]

/-- Bent on the blocks' side: with one mask row more, what that block says is not the first tree as
told. -/
theorem oracles_told_no : ((oraclesOf [sendRowMore]).map withoutGroups ==
    (toldKeyFull.1.take 1).map withoutGroups) = false := by decide +kernel

/-- And at the written values it is. -/
theorem oracles_told_first : ((oraclesOf [firstW.first]).map withoutGroups ==
    (toldKeyFull.1.take 1).map withoutGroups) = true := by decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.oracles_count
#print axioms Johnson.KB4.oracles_told
#print axioms Johnson.KB4.oracles_told_no
#print axioms Johnson.KB4.oracles_told_first
