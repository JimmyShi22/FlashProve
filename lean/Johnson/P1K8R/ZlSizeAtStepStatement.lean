-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ZlSizeAtStepStatement.lean: BEHIND AN ACCEPT OF THE DECISION OF THE OUTPUT HEAD's OWN
SUB-PROTOCOL (K6) THE STATE HOLDS, AS WHAT WAS HEARD AT THE HEAD, AN x WHOSE POINT x.Zl HAS h.ls +
h.lt COORDINATES. STATEMENTS ALONE: three definitions of propositions; no definition of another
kind. NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas'
statements.

WHAT IT IS NOT. A SIZE: nothing on the coordinates of x.Zl, which are the last of the point that the
lookup on the head's calls left. Nothing of the sub-protocol's own hearing is read: the hearing is a
letter. No reached state, no member of a chain.

  `ZlSizeAtDecision`   general in the shape h, the number of the reads' array, the bits of work, the
                       rounds, the hearing and the weights: where `decideBy`
                       (Johnson/Desc/Kinds/HeadFrame.lean) accepts at the seat at S, and h.ls is at
                       most the number of column coordinates of call 0: the title
  `ZlSizeAtBlock`      the same where the kind's block at S (`blockAt`,
                       Johnson/Stored/HeadSeatAt.lean) decides yes
  `LsFitsInScope`      that premise in the goals' scope, where `publicOf` returns X, at h := X.hS

NEAR. `hz_at`, `hz_of_letters` (Johnson/Desc/Reads/RunIsLean.lean): h.ls + h.lt ≤ x.g1.zx.size from
the kind's test on the points; from the kind's letters at the record. `core_of_kind`
(Johnson/Desc/Reads/HeardSizes.lean) has that bound inside its proof and spends it on another point.
The proof under `Lies` at Johnson/Desc/Reads/HeadAtRecord.lean ends as the first proof here ends.
`Zl_size`, `Zl_parts` (Johnson/Road/HeadPoint.lean), `zl_size`
(OnBytes/Tie/Pv/Lookup/Ends/FoSlFactsB.lean [not in this library]): the size at a run of
`verify-on-bytes`. `ls_le_lJ` (HeadPoint.lean): the second statement's inequality at every call of a
layout that `Head.layout` returns. `heard_of_onOut` (Johnson/Desc/Kinds/Law/K6HeardOfLookOut.lean):
the size of the lookup's point from an accept of its own public test behind its sub-protocol.

Limits. A size. Nothing on any property.
-/
import Johnson.Desc.Reads.HeardSizes
import Johnson.Goal.Meaning.HeadColsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (callKeys)

/-- **The statement of the title.** Not proved here; a lemma's statement, none of the library's
goals. -/
def ZlSizeAtDecision : Prop :=
  ∀ (h : OnBytes.Model.Head.Shape) (iU3 work : Nat) (rounds : Given → List Round)
    (hear : Given → Hear HeardAll) (weights : Given → Behind → SumOnMatrix) (s0 s2 : S)
    (rs : List Fmt.RoundView),
    decideBy rounds hear weights (parOf h work) (seatAt h iU3) s0 rs = .ok s2 →
    h.ls ≤ @lJ (sizesOf h) (OnBytes.Model.Head.keyFloor h) (callKeys 0) →
    ∃ o x, s2.here = .head o ∧ o.x = some x ∧ x.Zl.size = h.ls + h.lt

/-- The same at the kind's block at S. Not proved here; a lemma's statement, none of the library's
goals. -/
def ZlSizeAtBlock : Prop :=
  ∀ (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))), (blockAt h iU3 work l).decide s rs gs = .ok s' →
    h.ls ≤ @lJ (sizesOf h) (OnBytes.Model.Head.keyFloor h) (callKeys 0) →
    ∃ o x, s'.here = .head o ∧ o.x = some x ∧ x.Zl.size = h.ls + h.lt

/-- The premise, in scope. Not proved here; a lemma's statement, none of the library's goals. -/
def LsFitsInScope : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : Option ByteArray) (X : Verify.Public),
    VerifierAndGoals.InScope Z = true → VerifierAndGoals.readFiles Z = .ok pp →
    Verify.publicOf Z.pol Z.KL lay = .ok X →
    X.hS.ls ≤ @lJ (sizesOf X.hS) (OnBytes.Model.Head.keyFloor X.hS) (callKeys 0)

end P1K8

#print axioms P1K8.ZlSizeAtDecision
#print axioms P1K8.ZlSizeAtBlock
#print axioms P1K8.LsFitsInScope
