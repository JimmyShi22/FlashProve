-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/BookBent.lean: NEGATIVE TESTS FOR THE TESTS ON THE PLAN FOR THE TREES' TENANTS
AND OPENINGS (`BookPlan.allClausesHold`, Johnson/Desc/BookPlan.lean: eleven clauses) at the closed description
of a key file's protocol at the full size (`WK`, Johnson/HB/LLHARD/KB4/WK.lean) and the written
declared rounds (`declKeyFull`, Johnson/HB/LLHARD/KB8/Written.lean). That each clause accepts there
is Johnson/HB/LLHARD/KB4/CBook.lean's. Here one thing that a clause is about is bent, and all eleven
are asked again: so it is seen that the clause can reject, and which of the others reject with it.
By evaluations in Lean's kernel (`decide +kernel`).

  `a_eleven D T`: the eleven clauses' values; `a_eleven_eq`: it is the list of `BookPlan.clauses`'
    values, in its order. `a_bendT T c i f`: the roots as told with f laid on root number i of chain
    c. `a_bendD3 D f`: the declared rounds with f laid on each round of the third chain that opens
    three trees (the first code switch of the own test: it takes over the index masks' tree, W's
    tree and Omega's).
  Bent in what is told: `bent_sum`: a tree's number of words is one higher: "sum" alone rejects.
    `bent_rows`: a tenant's degree is 2: "rows" alone. `bent_alike`: in the multiplicities' tree the
    tenant without an out-of-domain sample is said to have one: "alike" rejects, and "answered" with
    it (one sampled tenant more owes answers). HERE the two are not parted by one bend: at WK no
    tree has two sampled tenants, so "alike" can be made to reject only by a sampled tenant more.
    That is no law on the clauses. `bent_allTold`: a fourth, empty list of roots: "allTold" alone.

The eleven stand in the order of `BookPlan.clauses`: sum, rows, told, range, alike, oneGroup, once,
answered, sentOraclesMatchEntries, inTime, inOrder. The tenth is asked through its eager twin `inTimeE`
(Johnson/HB/LLHARD/KB4/BeforeE.lean; `inTime_eq` ties the two).

Limits. Negative tests alone: nothing is shown of a key file's description at any public files.
Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB4.CBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open VerifiableInference.Desc VerifiableInference.Desc.BookPlan
open Johnson.KB4 (WK inTimeE)
open Johnson.KB8 (declKeyFull)

/-- The eleven clauses' values, in the order of `BookPlan.clauses`; the tenth by its eager twin. -/
def a_eleven (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : List Bool :=
  [sum T, rows T, everyOpenedTreeIsListed D T, range D, alike D T, oneGroup D T, once D T, answered D T, sentOraclesMatchEntries D T,
    inTimeE D T, inOrder D]

/-- **The list is the clauses' own**: the values of `BookPlan.clauses`, in its order. -/
theorem a_eleven_eq (D : DeclaredRoundsByChain) (T : SentOraclesByChain) : a_eleven D T = (clauses D T).map (·.2) := by
  unfold a_eleven clauses
  rw [Johnson.KB4.inTime_eq]
  rfl

/-- The roots as told, with f laid on root number i of chain c. -/
def a_bendT (T : SentOraclesByChain) (c i : Nat) (f : Oracle → Oracle) : SentOraclesByChain :=
  T.zipIdx.map fun x =>
    if x.2 == c then x.1.zipIdx.map fun y => if y.2 == i then f y.1 else y.1 else x.1

/-- The declared rounds, with f laid on each round of the third chain that opens three trees. -/
def a_bendD3 (D : DeclaredRoundsByChain) (f : Fmt.DeclaredRound → Fmt.DeclaredRound) : DeclaredRoundsByChain :=
  (D.1, D.2.1, D.2.2.map fun d => if d.opens.length == 3 then f d else d)

set_option maxRecDepth 1000000 in
/-- Unbent, all eleven accept: so what follows is the bends' doing. -/
theorem unbent : a_eleven declKeyFull WK.roots = List.replicate 11 true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: the first chain's first tree has one word more than its tenants. "sum" alone rejects. -/
theorem bent_sum :
    a_eleven declKeyFull (a_bendT WK.roots 0 0 fun r => { r with words := r.words + 1 }) =
      [false, true, true, true, true, true, true, true, true, true, true] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: the tenants of the first chain's first tree have the degree 2. "rows" alone rejects. -/
theorem bent_rows :
    a_eleven declKeyFull (a_bendT WK.roots 0 0 fun r =>
      { r with tenants := r.tenants.map fun t => { t with degree := 2 } }) =
      [true, false, true, true, true, true, true, true, true, true, true] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: in the first chain's second tree every tenant is said to have an out-of-domain sample; the
one that had none is in no group, so the sampled tenants' groups differ. "alike" rejects, and
"answered" with it. -/
theorem bent_alike :
    a_eleven declKeyFull (a_bendT WK.roots 0 1 fun r =>
      { r with tenants := r.tenants.map fun t => { t with sampled := true } }) =
      [true, true, true, true, false, true, true, false, true, true, true] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Bent: a fourth, empty list of roots. "allTold" alone rejects. -/
theorem bent_allTold :
    a_eleven declKeyFull (WK.roots ++ [[]]) =
      [true, true, true, true, true, true, true, true, false, true, true] := by decide +kernel

end Johnson.KB9

#print axioms Johnson.KB9.a_eleven_eq
#print axioms Johnson.KB9.unbent
#print axioms Johnson.KB9.bent_sum
#print axioms Johnson.KB9.bent_rows
#print axioms Johnson.KB9.bent_alike
#print axioms Johnson.KB9.bent_allTold
