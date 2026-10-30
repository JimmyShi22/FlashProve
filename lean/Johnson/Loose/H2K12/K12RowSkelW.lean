-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12RowAlone
import Johnson.Desc.ProofFile.Law.Skel.Skel
/-
Johnson/Loose/H2K12/K12RowSkelW.lean:
THE PROXIMITY TEST's (the kind K12's) ROW AMONG THE ROWS THAT "the proof file's IOP as
written in Lean returns, with its cut" WANTS OF EACH LOT, IN ProofFile.Sk's FORM "the lot's skeleton is
the written one": THE WRITTEN SKELETON, AND THE ONE CLOSED FACT. Alone in its file, since it is an
evaluation in Lean's kernel. A skeleton (ProofFile.Sk.Skel, Johnson/Desc/ProofFile/Law/Skel/Skel.lean)
is a sub-protocol less its functions: name, place,
how many rounds, the length of its list of oracle messages, the rounds that tell a tree, before, the
test on the list of rounds, the names of its runs of claims and of the runs behind them.
  k12ToldW         the rounds that tell a tree: READ OFF the written cut's row number 354
                   (cutFirstFull, Johnson/Desc/Ok/PlanWritten/CutLit.lean): no second literal. Where
                   that list had no such row: the empty list: never met (rowL_full,
                   Johnson/Loose/H2K12/K12RowAlone.lean)
  k12SkelW         the written skeleton. WHICH OF ITS NINE VALUES IS READ OFF AND WHICH IS TYPED:
                   told: read off, as said; the place, 33, 33 and [(1, 76)]: TYPED HERE, after the
                   same row's text; the name: typed, after nameAt's text at that place
                   (Johnson/Desc/K12/Frame.lean): THE LOT's OWN NAME, not "F:2", under which the
                   seat lays the sub-protocol; planOk := true, no run of claims, none behind: typed
  skelL_full       the skeleton of the lot's sub-protocol at the written member piLFull is k12SkelW:
                   all nine, decided by the kernel. With it: Skel.lean's routine for the
                   rounds that tell a tree (toldFrom) and the cut's own (toldRounds) agree at this
                   member
WHAT IT IS NOT: that the list of rounds gives the written member is not said here
(H2K12/K12MemberWritten.lean). The full size alone. No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Oracle)
open VerifiableInference.PlanWritten (cutFirstFull)
open H2K.Member (piLFull)

/-- The rounds that tell a tree, off the written cut's row number 354. -/
def k12ToldW : List (Nat × List Oracle) :=
  match cutFirstFull[354]? with
  | some y => y.2.2.2.2.1
  | none => []

/-- **The written skeleton of the lot's one sub-protocol.** -/
def k12SkelW : ProofFile.Sk.Skel :=
  { name := "the proximity test (chain 1, piece 2)", place := ⟨1, none, 2, .K12⟩, nRounds := 33
    nOracles := 33, told := k12ToldW, before := [(1, 76)], planOk := true, claims := []
    after := [] }

/-- **AT THE WRITTEN MEMBER: THE WRITTEN SKELETON.** -/
theorem skelL_full : ProofFile.Sk.skel (lotB piLFull) = k12SkelW := by
  decide +kernel

end H2K12

#print axioms H2K12.skelL_full
