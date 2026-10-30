-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/SubRounds.lean: the rounds of the model's three kinds of sub-proof, as plans.

A request's first chain has one link for each sub-proof: a group of layers, its attention, the
output head. Between the frame's rounds of a link (OnBytes/Params/DeriveReq.lean) come the
sub-proof's own. They are planned moment by moment: what follows the sending of a moment's oracle
messages, which are named here by what they hold.
 - moment 0, after the cells: the lookup of the sub-proof's calls, then its own rounds;
 - moment 1, after the reads: the matrix of the smallness test;
 - moment 2, after the digits: the lookup on the digits, then the sub-proof's end, with the
   element that batches all its claims.
The file renders prover/prover/plan_rounds.h, prover/attn/plan_rounds.h, prover/head/plan_rounds.h
and prover/hiding/token_plan.h, and the routines by which the C++ verifier puts them together
(forestPlan, planRounds and the three routines named rounds in verifier/src). Each kind is given
by a record of a few numbers, which follow from the model's lines of the parameter file. The records
are filled in OnBytes/Model/ (VerifySubproofs.lean, AttentionPlan.lean, HeadRounds.lean).

Main definitions: `ForestSize`, `SmallSize`, `LayerRounds`, `AttentionRounds`, `HeadRounds`,
`layerRounds`, `attentionRounds`, `headRounds`.
What is not claimed: no theorem is stated here. A plan states an error for each of its rounds. Four
tests of the sub-proofs have no round of their own (`planLayerOwn`, `planAttentionOwn`,
`planHeadOwn`), and neither have the equations of the smallness test (`planSmall`).
-/
import OnBytes.Params.Planner

namespace OnBytes.Params

/-- A lookup of a group of calls by product trees: 2 ^ v keys, a table of 2 ^ d entries. The plan
says v, d, the number of planes and whether there is a shift, and no more. Two lookups that divide v
between a tree's number and the place in a tree, or d between a call's number and a row of its
table, in different ways have one plan (vf_lookup_argument.h, "What the caller must ensure"). -/
structure ForestSize where
  v : Nat
  d : Nat
  /-- the group has several calls, whose tables are joined by a shift -/
  shifted : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The rounds of a lookup of a group of calls (forestPlan). The multiplicities are in 2 ^ 5
planes of bits. -/
def planForest (x : ForestSize) : Planning Unit :=
  planLookup { v := x.v, d := x.d, mu := 5, shifted := x.shifted }

/-- The smallness test of a sub-proof. -/
structure SmallSize where
  /-- the columns of all its matrices together -/
  columns : Nat
  /-- the number of random combinations of a row's cells for which the sub-proof is built -/
  tau : Nat
  /-- the lookup on the digits -/
  digits : ForestSize
  deriving DecidableEq, Repr, Inhabited

/-- The rounds of the smallness test (planRounds, vf_smallness_test_members.inc). `which` = 0, after
the reads' sample: the matrix. `which` = 1, after the sample of the digits and the planes: the
lookup on the digits. The test's equations have no round of their own: they are under powers of the
sub-proof's batching element, whose round must count them with the sub-proof's claims. The number of
combinations that follows from the setting must be the sub-proof's; else the public files are
refused under the name plan-tau. Any other `which` is refused under parameters-not-admitted, where
the C++ verifier says internal-plan-moment, a fault of the program. -/
def planSmall (x : SmallSize) (which : Nat) : Planning Unit := do
  if which == 0 then
    needs (rngCombinations (← theSetting) (← theScope) == x.tau) "plan-tau"
    planRng x.columns
  else
    needs (which == 1)
    planForest x.digits

/-- A product of two halves under equality weights: a sumcheck and the point of a line. -/
def planProductLayer (variables : Nat) : Planning Unit := do
  planPsc { degree := List.replicate variables 3, degreeY := 2, values := 2 }
  planLine

/-- A claimed sum (one scalar) and the sumcheck over the lt token bits that starts from it. -/
def planTokenSumcheck (lt degreeY shown : Nat) : Planning Unit := do
  planScalars 1
  planPsc { degree := List.replicate lt 3, degreeY := degreeY, values := shown }

/-- A claimed sum (one scalar) and the sumcheck that starts from it: lt rounds over the token bits
and `more` rounds over an index that is summed plainly (plan_token_sum). `shown`: the end values.
`degreeInY`: the degree of the summand in the maps whose values they are. Without end values there
is no further variable. The arguments come in a different order from `planTokenSumcheck`'s. -/
def planTokenSum (lt shown degreeInY : Nat) (more : Nat := 0) : Planning Unit := do
  planScalars 1
  planPsc { degree := List.replicate (lt + more) 3, degreeY := degreeInY, values := shown,
            withY := decide (0 < shown) }

/-! ## A group of layers -/

/-- The numbers of a layer sub-proof's own rounds. -/
structure LayerRounds where
  /-- token bits -/
  lt : Nat
  /-- bits of a block of features in a long read -/
  ls : Nat
  /-- bits of the number of norm instances -/
  lNI : Nat
  /-- bits of the padded model width -/
  lPd : Nat
  /-- bits of the number of layers in the group -/
  ll : Nat
  /-- bits of the padded hidden width -/
  lPf : Nat
  /-- bits of a routed expert's hidden width -/
  lfe : Nat
  /-- rounds of the batched inner-product sumcheck -/
  lamS : Nat
  /-- rounds of the merge -/
  lkW : Nat
  /-- norm instances -/
  NI : Nat
  /-- for each instance: sums of limb products -/
  NS : Nat
  /-- for each instance: row products -/
  NP : Nat
  /-- for each instance: row values that the token sumcheck shows -/
  NO : Nat
  /-- the call list has terms for the second token sumcheck -/
  withTerms : Bool
  /-- how many values the second token sumcheck shows -/
  shownByTheTerms : Nat
  /-- values of never-sent vectors that the batched sumcheck shows -/
  neverSent : Nat
  /-- the panels' weight claims -/
  weightClaims : Nat
  /-- the group that also proves the embedding's claim -/
  firstGroup : Bool
  /-- the group has layers with routed experts -/
  routed : Bool
  deriving DecidableEq, Repr, Inhabited

/-- A layer sub-proof's own rounds, from the norms' token point to the merge's shown value. One test
has no round of its own: with routed experts, that the selector's entries sum to 1 at every token is
tested at the last lt coordinates of the lookup's key point, and its error is carried by the rounds
that draw these coordinates. The conditions on which that rests are written above plan_layer_own
(prover/prover/plan_rounds.h). Nothing here or in the C++ programs tests them. -/
def planLayerOwn (x : LayerRounds) : Planning Unit := do
  planZero x.lt
  if x.firstGroup then
    planZero (x.ls + x.lt)
    planZero (x.lPd - x.ls)
  planScalars (x.NS * x.NI)
  planBatSigma x.NS
  if x.lNI != 0 then planJoin x.lNI
  planProductLayer (x.lNI + x.lPd + x.lt)
  planScalars (x.NP * x.NI)
  planBatSigma (x.NP * x.NI)
  planTokenSumcheck x.lt 2 (x.NO * x.NI)
  if x.withTerms then
    planTokenSumcheck x.lt 1 x.shownByTheTerms
    planBatSigma 2
  planPsc { degree := List.replicate x.lamS 3, degreeY := 2,
            values := 2 + x.neverSent + x.weightClaims }
  planProductLayer (x.ll + x.lPf + x.lt)
  if x.routed then
    if 1 < x.ll then planJoin (x.ll - 1)
    planProductLayer (x.ll - 1 + x.lfe + x.lt)
  if x.firstGroup then planScalars 1
  planBatSigma (x.weightClaims + (if x.firstGroup then 1 else 0))
  planPsc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 }

/-- The rounds of a layer sub-proof after a moment. `claims`: all its linear claims and the
equations of its smallness test, which the last round batches. -/
def layerRounds (look : ForestSize) (x : LayerRounds) (small : SmallSize) (claims : Nat)
    (moment : Nat) : Planning Unit := do
  if moment == 0 then
    planForest look
    planLayerOwn x
  else
    planSmall small (moment - 1)
    if moment == 2 then planBatSigma claims

/-! ## Attention -/

/-- A sum over nv variables of a weight times a product of two maps, for several pairs of maps:
degree 3 in each variable (`PscSize.degree` says one more than the degree); both end values of each
pair are shown, and the summand has degree 2 in them. -/
def attentionSc3 (nv pairs : Nat) : PscSize :=
  { degree := List.replicate nv 4, degreeY := 2, values := 2 * pairs }

/-- The sumcheck for the key at the index: rounds over the lt bits of a position j (degree 2), the
lgk bits of a head g of keys and values (degree lt + 2) and the lt bits of a position i
(degree lt + 1). Shown: one value for each of the Lam layers and the lt index bits of each pair; the
summand has degree lt + 1 in them. -/
def attentionScd (lt lgk pairs Lam : Nat) : PscSize :=
  { degree := List.replicate lt 3 ++ List.replicate lgk (lt + 3) ++ List.replicate lt (lt + 2),
    degreeY := lt + 1, values := Lam + pairs * lt }

/-- The numbers of an attention sub-proof's own rounds. lt: token bits. There are 2 ^ lgk heads of
keys and values. -/
structure AttentionRounds where
  lt : Nat
  lgk : Nat
  /-- layers times heads -/
  pairs : Nat
  /-- layers -/
  Lam : Nat
  /-- segments of plane values that are present: three values each -/
  planeMessages : Nat
  /-- for each score segment that is present, in the order of the calls: variables and pieces -/
  score : List (Nat × Nat)
  /-- variables of the sumcheck for the denominator times the output -/
  e : Nat
  /-- variables of the value product off the diagonal -/
  valueM : Nat
  /-- variables of the value product on the diagonal -/
  valueD : Nat
  /-- variables of the sumcheck for query times key at the maximum -/
  attained : Nat
  /-- variables of the sumcheck for the index bits -/
  bits : Nat
  /-- what the last round batches: all linear claims and the equations of the smallness test -/
  rows : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An attention sub-proof's own rounds (plan_attention_own). One test has no round of its own: that
the denominator is the sum of the weights, at every head and position, is tested at a point that the
lookup has drawn, and its error is carried by the rounds that draw these coordinates. The conditions
on which that rests are written above plan_attention_own (prover/attn/plan_rounds.h). -/
def planAttentionOwn (x : AttentionRounds) : Planning Unit := do
  if x.planeMessages != 0 then planScalars (3 * x.planeMessages)
  forEach x.score fun s => do
    planScalars 7
    planPsc (attentionSc3 s.1 s.2)
  planScalars (5 + x.lt + 2)
  planPsc (attentionSc3 x.e x.pairs)
  planBatSigma 2
  planScalars 2
  planPsc (attentionSc3 x.valueM x.pairs)
  planPsc (attentionSc3 x.valueD x.pairs)
  planZero (2 * x.lgk + 2 * x.lt + 4)
  planScalars x.pairs
  planBatSigma x.pairs
  planPsc (attentionSc3 x.attained x.pairs)
  planBatSigma x.pairs
  planPsc (attentionScd x.lt x.lgk x.pairs x.Lam)
  planBatSigma x.pairs
  planPsc (attentionSc3 x.bits x.pairs)

/-- The rounds of an attention sub-proof after a moment. -/
def attentionRounds (look : ForestSize) (x : AttentionRounds) (small : SmallSize)
    (moment : Nat) : Planning Unit := do
  if moment == 0 then
    planForest look
    planAttentionOwn x
  if 1 ≤ moment then planSmall small (moment - 1)
  if moment == 2 then planBatSigma x.rows

/-! ## The output head -/

/-- The numbers of the head sub-proof's own rounds. -/
structure HeadRounds where
  /-- bits of a position -/
  lt : Nat
  /-- bits of a feature, padded -/
  lPd : Nat
  /-- bits of a column of the committed weights -/
  lkW : Nat
  /-- of the norm: sums of limb products -/
  sums : Nat
  /-- of the norm: row products -/
  products : Nat
  /-- of the norm: row values in the row products -/
  rowValues : Nat
  /-- what the last round batches: all linear claims and the equations of the smallness test -/
  rows : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The head sub-proof's own rounds after its lookup (plan_head_own). Two tests have no round of
their own: two lines of the acceptance policy, which must hold at every position that has a cost,
are tested at one point that the lookup has drawn, and their errors are carried by the rounds that
draw its coordinates. The conditions on which that rests are written above plan_head_own
(prover/head/plan_rounds.h). -/
def planHeadOwn (x : HeadRounds) : Planning Unit := do
  planZero x.lt
  planScalars x.sums
  planBatSigma x.sums
  planPsc { degree := List.replicate (x.lPd + x.lt) 3, degreeY := 2, values := 2 }
  planLine
  planScalars x.products
  planBatSigma x.products
  planTokenSum x.lt x.rowValues 2
  planTokenSum x.lt 2 2
  planTokenSum x.lt 2 2 x.lPd

/-- After the smallness test: the merge of the one weight claim, and the batching. -/
def planHeadEnd (x : HeadRounds) : Planning Unit := do
  planBatSigma 1
  planPsc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 }
  planBatSigma x.rows

/-- The rounds of the head sub-proof after a moment. -/
def headRounds (look : ForestSize) (x : HeadRounds) (small : SmallSize) (moment : Nat) :
    Planning Unit := do
  if moment == 0 then
    planForest look
    planHeadOwn x
  if 1 ≤ moment then planSmall small (moment - 1)
  if moment == 2 then planHeadEnd x

end OnBytes.Params
