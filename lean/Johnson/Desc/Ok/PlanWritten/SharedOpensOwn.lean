-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/PlanWritten/SharedOpensOwn.lean: a test at written values, with its negative tests.
At the library's written lists of the full size, no round of a file's second chain opens a tree of
the first chain. A closed fact on the data of the two files' written lists (`writtenPFull`,
`writtenKFull`, Johnson/Flat/Dec/FitAtWritten.lean).

What it is for. Three rules of the library give clauses that a chain shared by the requests of a
batch asks of one block (`leadsK_of_lift`, `keyLaw_of_lift`, `leadsBN_of_lift`,
Johnson/Desc/Plain/KeyAlone.lean); the first and the third start from a law on that block for one
statement. Their premise on openings, ho, reads: for every round's data d of the piece and every j
among `d.opens`, lo ≤ j; lo is the number of the chain's first own tree. A round's `opens` are the
numbers, over the whole file, of the trees that are opened at its drawn positions, and `D.t₁` is the
number of trees that the first chain sends. So at the written lists, at lo = `D.t₁`, the premise
holds of every piece whose data are among the second chain's.

What it shows: that this premise can be met, at the written lists of both files; that it is not met
idly there (some round opens a tree); and that the test says no once one round is made to open a
tree of the first chain.

Definitions.
  `opensFrom lo ds`: a test with code: every number among the `opens` of every round's data in ds is
    at least lo.
  `openZero ds`: ds with the first round made to open the tree 0 and no other.
Statements.
  `opensFrom_iff`: what a yes says, in the form of the rules' premise.
  `t1_keyFull`: the key file's first chain sends 6 trees. For the proof file: `t1_proofFull`
    (Johnson/G/DryProofTestsFull.lean): 83.
  `opens_proof`, `opens_key`: the test says yes, at 83 and at 6.
  `shared_opens_own`: for every d in `writtenPFull.ds₂` and every j in `d.opens`: `writtenPFull.t₁`
    ≤ j. `shared_opens_own_key`: the like at `writtenKFull`.
  `shared_opens_some`: the statements are not idle: in each of the two second chains some round
    opens a tree.
  `opens_plant`, `opens_plant_key`: the negative tests: at `openZero` of the second chain's data the
    test says no.
By evaluations in Lean's kernel (`decide +kernel`): all but `opensFrom_iff`; `shared_opens_own` and
`shared_opens_own_key` by proof, from evaluated premises.

What of OnBytes/Model/ is used: nothing.

Limits. No rule is called here: that a piece's data are among these lists is left to whoever calls
one. The written lists are those of Johnson/G/DryProofLit.lean and Johnson/G/DryKeyLit.lean: made
once, at the stored full-size public files, one key of the table and, for the proof file, one
request (see their heads). That a description's data are these is not said here. Of the verifier's
description it is said in other files: at all public files in the goals' scope both files' data are
these written data, or the verifier says no to everything (`FlashProve.written_or_no_all`,
Johnson/Goal/Description/KeyWritten.lean). At the library's written copy of the full-size public
files (`VerifierAndGoals.storedPublicFiles`: three terms written in Lean; no theorem ties them to the repository's files)
they are these written data with no premise, by `AtFullSide.Top.written_zFull`
(AtFullSide/Top/WrittenAtFull.lean), at the format's second hash function (`OnBytes.secondHashFunction`) and a
constant digest (`Key.fixedDigest`), not the files' own, in a side library outside the main library
(one constant beneath it passes Lean's kernel only at a larger thread stack; Lean's re-checker,
leanchecker, was run on it and fails there at each shell stack limit that was tried; the toolchain's
own replay passes it at a larger thread stack; so that constant has been checked by the kernel in
the build and by that replay, and by no independent program); no independent checker has replayed
any of the closed facts beneath it, and the full-size example's weights are synthetic. That the data
are the written ones does not show that the verifier accepts any proof.
One changed value for each file, and the number
0 alone: no test at lo - 1. A stored table that a round opens is no tree of the file, and stands in
another field (`stored`): nothing is said of it. Nothing on the third chain. Nothing on soundness.

-/
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.OpensOwn
open OnBytes.Maker Johnson.G

/-- Every tree that a round of ds opens has a number of at least lo. -/
def opensFrom (lo : ℕ) (ds : List RDT) : Bool :=
  ds.all fun d => d.opens.all fun j => decide (lo ≤ j)

theorem opensFrom_iff (lo : ℕ) (ds : List RDT) :
    opensFrom lo ds = true ↔ ∀ d ∈ ds, ∀ j ∈ d.opens, lo ≤ j := by
  simp only [opensFrom, List.all_eq_true, decide_eq_true_eq]

set_option maxRecDepth 1000000 in
/-- The number of trees that the key file's first chain sends, as a numeral. -/
theorem t1_keyFull : dKeyFull.t₁ = 6 := by
  unfold WholeD.t₁
  rw [sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_proof : opensFrom 83 dProofFull.ds₂ = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_key : opensFrom 6 dKeyFull.ds₂ = true := by decide +kernel

/-- **No round of the proof file's second chain opens a tree of the first chain.** -/
theorem shared_opens_own : ∀ d ∈ writtenPFull.ds₂, ∀ j ∈ d.opens, writtenPFull.t₁ ≤ j := by
  rw [writtenPFull_eq, t1_proofFull]
  exact (opensFrom_iff 83 _).1 opens_proof

/-- **The like for the key file.** -/
theorem shared_opens_own_key : ∀ d ∈ writtenKFull.ds₂, ∀ j ∈ d.opens, writtenKFull.t₁ ≤ j := by
  rw [writtenKFull_eq, t1_keyFull]
  exact (opensFrom_iff 6 _).1 opens_key

set_option maxRecDepth 1000000 in
/-- In each of the two second chains some round opens a tree. -/
theorem shared_opens_some : (dProofFull.ds₂.any fun d => !d.opens.isEmpty) = true ∧
    (dKeyFull.ds₂.any fun d => !d.opens.isEmpty) = true := by
  decide +kernel

/-- The data with the first round made to open the tree 0. -/
def openZero : List RDT → List RDT
  | [] => []
  | d :: ds => { d with opens := [0] } :: ds

set_option maxRecDepth 1000000 in
theorem opens_plant : opensFrom 83 (openZero dProofFull.ds₂) = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_plant_key : opensFrom 6 (openZero dKeyFull.ds₂) = false := by decide +kernel

end VerifiableInference.PlanWritten.OpensOwn

#print axioms VerifiableInference.PlanWritten.OpensOwn.opensFrom_iff
#print axioms VerifiableInference.PlanWritten.OpensOwn.t1_keyFull
#print axioms VerifiableInference.PlanWritten.OpensOwn.opens_proof
#print axioms VerifiableInference.PlanWritten.OpensOwn.opens_key
#print axioms VerifiableInference.PlanWritten.OpensOwn.shared_opens_own
#print axioms VerifiableInference.PlanWritten.OpensOwn.shared_opens_own_key
#print axioms VerifiableInference.PlanWritten.OpensOwn.shared_opens_some
#print axioms VerifiableInference.PlanWritten.OpensOwn.opens_plant
#print axioms VerifiableInference.PlanWritten.OpensOwn.opens_plant_key
