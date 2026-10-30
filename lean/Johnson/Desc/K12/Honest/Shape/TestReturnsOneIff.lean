-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestReturnsOneIff.lean: the converse of `k12_returns_one`
(Johnson/Desc/K12/Honest/Shape/TestReturnsOne.lean), and so an equivalence: under that theorem's
hypotheses on the shape, the plan, the structure before the test and the view, the proximity test's
block accepts if and only if the base case's test holds at the claim that the test's own parts make.
"The block accepts" means: the decision of the test's block (`proximityTestKind`, Johnson/Desc/K12/Frame.lean, at
the parts `guardedProximityTestParts`, Johnson/Desc/K12/JoinGuarded.lean) returns `.ok`. The statements are on the
verifier's decision only: none speaks of a prover. Two definitions, which give the hypotheses of
`k12_returns_one` names, and three theorems. General in the place, the structure before the test,
the rounds and the columns.

In the list and below: a file that is named without a folder is in this folder, and Link/ is short
for Johnson/Prover/Link/. p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of a
test: the plan. cur and nxt (`Fmt.M1.Stage`) are its first two stages and rest the others, by the
field `stages`. A part (`Part`, same file) is a piece of the test with a decision of its own: the
front, which has no round; the batching; at each stage but the last a fold, a switch and a batching
after it; at the last stage the base case. t (`T12`, Johnson/Desc/K12/Join.lean) is the verifier's
structure inside a test, here before the front: `t.st` is its statement, `t.g` the number of the
group under test, and `t.mask` the number of the message that holds the present stage's mask, if it
has come. "Mask" is the library's name for a message: nothing is said of what a mask does. The shape
of t is `testSh t` (Test.lean). The door of a test is its front, its batching, the question whether
the group is the first stage's, and its first fold. `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean)
lists the place's declared rounds, each with its oracle messages: the first is the batching's, and
`laidS p`, the rest, are the stages'. The view is the rounds (`Fmt.RoundView`) and the groups of columns
that a decision takes as arguments: rB is the batching's round, R and gs are the stages' rounds and
groups of columns. `noDigest` (Johnson/Desc/Block.lean) sets the field `drawn.digest` of a round to
`none`. `batT t G row` (Link/FormFirst.lean) is t with the statement `begun t.st t.g G`
(OnBytes/Slice/BlkBegin.lean), passing on the claim row with the group's layout. A test with code is
a definition of type `Bool`.

  `k12_accept_iff_one`: under `OneAsks`: there is a structure t' such that the block's decision at
    t, the rounds `(rB :: R).map noDigest` and the groups of columns gs returns `.ok t'`, if and
    only if `ValsAsk` holds
  `vals_of_block`: the converse of `k12_returns_one`: under `OneAsks`, an accept of the block at
    these rounds and groups gives `ValsAsk`. The front returns the structure as it is, the batching
    returns `batT t G row`, and the parts' decisions are functions, so what they return is fixed
  `k12_returns_asks`: `k12_returns_one`, with its hypotheses stated as `OneAsks` and `ValsAsk`
  `OneAsks` (definition): all hypotheses of `k12_returns_one` but the one on the values of the
    test's own rounds and columns, as one structure of hypotheses, of thirteen fields
  `ValsAsk` (definition): that hypothesis, under a name: for the group G of number `t.g` and the row
    that `Bat.combine` (OnBytes/Iop/Bat.lean) returns at the element `drawnOf (noDigest rB)`
    (Link/FormFold.lean), `ValsFrom` (TestReturns.lean: the base case's test on values) holds from
    the first stage on at `batT t G row`, `R.map noDigest` and gs

By what. `k12_returns_asks` takes the two lists out of the fields `rounds` and `oracles` and calls
`k12_returns_one`. `vals_of_block` begins as the proof of `k12_returns_one` does. It splits `doorB`
into its four conjuncts; `testFront_of`, `batOwes_of` and `frontOwes_of` (TestDoor.lean) give the
group G, `TestFront` (Link/FormFirst.lean), `BatOwes` (Link/FormBat.lean) and `FrontOwes`
(Link/FormDoor.lean); by `front5_yes` (Link/FormDoorLaws.lean) the front returns t, and by
`bat5_yes` (Link/FormBatLaws.lean) the batching returns `batT t G row`. `k12_ok`
(Johnson/Desc/K12/FrameLaws.lean) takes the block's accept apart: the front, the batching and the
stages accept one after the other. `laid_cons` (Link/LinkJoinD.lean) shows that the batching has one
round and no opening. So the structures that the front and the batching return within the accept are
t and `batT t G row`, and `vals_of_accept` (TestReturns.lean) gives `ValsFrom` from the stages'
accept. `k12_accept_iff_one` puts the two theorems together.

Hypotheses. The fields of `OneAsks`, in the order of the hypotheses of `k12_returns_one`; the head
of TestReturnsOne.lean says of what kind each is. `stages`: the plan's stages are cur, nxt and rest.
`rounds`, `oracles`: the place has declared rounds and oracle messages (`H2U.roundsOfNums` and
`H2U.testOracles`, Johnson/Desc/K12/TestEntries.lean, each return a list). `door`: `doorB`
(TestDoor.lean) passes at the shape of t and the batching's declared round. `mask`:
`t.mask = some id`. `tidy`: `stTidyB` (Johnson/Desc/Ground/Shape/Marks.lean) passes at `t.st`.
`plain`: every row that the test takes in (`runRows`, OnBytes/Slice/BlkBegin.lean) is a `PlainRow`
(OnBytes/Slice/BlkPlain.lean): it has no written-out factor. `claims`: `claimsB` (TestDoor.lean)
passes at t. `seat`: `seat1B` (TestSeat.lean) passes at id and tN. `cutB`: `batCut`
(Link/FormBat.lean) passes at the batching's declared round. `plan`: `planFromOk`
(Link/StepPlanOk.lean) passes from the first stage on, at the codes of t. `fitB`: `roundsFit`
(Johnson/Desc/Block.lean) passes at that declared round and rB. `view`: `viewFromB` (TestView.lean)
passes at the stages' declared rounds, R and gs.

Limits.
- What the equivalence says and what it does not. `ValsAsk` is stated through the decisions of the
  test's own parts: so it is in effect "the block accepts" in other words, and the equivalence says
  so. Its content: at a view of the form none of the front, the batching, the folds, the switches,
  the batchings behind them and the base part's other questions can refuse: the base case's own
  decision alone can. ("A view of the form": rounds and groups of columns at which `fitB` and `view`
  hold. The other eleven fields of `OneAsks` are hypotheses of that sentence too. It is read off
  `k12_accept_iff_one` and the definition of `ValsFrom`: it is not stated as a theorem.)
- `ValsAsk` is a proposition, not a test with code: the claim that the base case is handed is not
  written out as a function here. `valsAskB` (TestValsB.lean) is a test with code for it, which
  makes the claim by running the test's own parts.
- `OneAsks` is not free of values: its field `claims` is a test on the open rows' coefficients, and
  `tidy` reads values at one spot. The head of Marks.lean names the spot.
- All limits of TestReturnsOne.lean stand: one tree at the first stage; the mask has come; no
  written-out factor. In Lean, for these three: the clause `T.parts == G.members ++ [id]` of
  `seat1B`; the field `mask`, `cameB` in `doorB` and `!p.nums.ownMask` in `planFromOk`; the field
  `plain`.
- `ValsAsk` by itself asserts no accept. It holds vacuously where the statement has no group of
  number `t.g` and where `Bat.combine` returns nothing. So does `ValsFrom` where an earlier part
  refuses, where no claim is passed on to the base case, where `stageAt` returns nothing and where
  the claim cannot be written out (`claimAt`).
- `vals_of_block` takes all of `OneAsks`. Its proof uses the fields `stages`, `door`, `mask`,
  `tidy`, `plain`, `claims`, `cutB` and `fitB` only.
- No values that meet `OneAsks` and `ValsAsk` are given in this file.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestReturnsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open Johnson.Prover.Link
open H2K.JointK (laidOf laidS)

/-- All hypotheses of `k12_returns_one` (TestReturnsOne.lean) but the one on the values of the
test's own rounds and columns, as one structure of hypotheses. That theorem's two lists, of declared
rounds and of oracle messages, are here under "there is" (`rounds`, `oracles`). The field `claims`
is itself a test on values: of the rows that are open on the group under test, before the test. -/
structure OneAsks (p : P12) (cur nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (t : T12)
    (i n : ℕ × ℕ) (id tN : ℕ) (rB : Fmt.RoundView) (R : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) : Prop where
  stages : p.nums.stages = cur :: nxt :: rest
  rounds : ∃ ds, H2U.roundsOfNums p.nums = some ds
  oracles : ∃ os, H2U.testOracles p.nums = some os
  door : doorB p cur nxt (((laidOf p).take 1).map (·.1)) i n (testSh t) = true
  mask : t.mask = some id
  tidy : stTidyB t.st = true
  plain : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r
  claims : claimsB t = true
  seat : seat1B cur (laidS p) (coreSh ⟨t.st, t.book, t.roots⟩) t.g id tN = true
  cutB : batCut (((laidOf p).take 1).map (·.1)) = true
  plan : planFromOk p (nxt :: rest) 0 cur (laidS p) t.st.codes = true
  fitB : roundsFit (((laidOf p).take 1).map (·.1)) [rB] = true
  view : viewFromB (nxt :: rest) cur (laidS p) R gs = true

/-- The hypothesis of `k12_returns_one` on the values of the test's own rounds and columns: for the
group G under test and the row that `Bat.combine` returns at `drawnOf (noDigest rB)`, `ValsFrom`
(TestReturns.lean) holds from the first stage on at `batT t G row`, `R.map noDigest` and gs. A
proposition, not a test with code. -/
def ValsAsk (p : P12) (cur nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (t : T12) (rB : Fmt.RoundView)
    (R : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) : Prop :=
  ∀ G row, t.st.groups[t.g]? = some G →
    Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩
      (drawnOf (noDigest rB)) = some row →
    ValsFrom p (nxt :: rest) 0 cur (laidS p) (batT t G row) (R.map noDigest) gs

variable {p : P12} {cur nxt : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {t : T12} {i n : ℕ × ℕ}
  {id tN : ℕ} {rB : Fmt.RoundView} {R : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}

/-- `k12_returns_one`, from `OneAsks` and `ValsAsk`: the block accepts. -/
theorem k12_returns_asks (A : OneAsks p cur nxt rest t i n id tN rB R gs)
    (hv : ValsAsk p cur nxt rest t rB R gs) :
    ∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t ((rB :: R).map noDigest) gs = .ok t' := by
  obtain ⟨ds, hd⟩ := A.rounds
  obtain ⟨os, ho⟩ := A.oracles
  exact k12_returns_one A.stages hd ho A.door A.mask A.tidy A.plain A.claims A.seat A.cutB A.plan
    rB A.fitB R gs A.view hv

/-- **The converse: under `OneAsks`, an accept of the block gives `ValsAsk`.** -/
theorem vals_of_block (A : OneAsks p cur nxt rest t i n id tN rB R gs) {t' : T12}
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t ((rB :: R).map noDigest) gs = .ok t') :
    ValsAsk p cur nxt rest t rB R gs := by
  have hD := A.door
  unfold doorB at hD
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hD
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hD
  have h4' : (match t.mask with
    | some id => cameB cur (testSh t).core t.g i id
    | none => (testSh t).core.st.oracles.length == (testSh t).core.book.place.length) = true := h4
  rw [A.mask] at h4'
  obtain ⟨G, H⟩ := testFront_of h1 A.mask h4' A.tidy A.plain
  have B := batOwes_of h2 H.group
  have F := frontOwes_of h3 A.claims H.group
  obtain ⟨row, hr, hb⟩ := bat5_yes H _ B A.cutB [rB] A.fitB
  have hf := front5_yes B.pass H.group F
  obtain ⟨first, rest0, ds, t₀, t₁, e1, e2, k0, k1, -, k3⟩ := k12_ok guardedProximityTestParts p t t' _ _ h
  obtain ⟨rfl, rfl⟩ := List.cons.inj (e1.symm.trans A.stages)
  obtain rfl : t = t₀ := Except.ok.inj (hf.symm.trans k0)
  have ez : ds.zip p.oracles = laidOf p := by
    unfold H2K.JointK.laidOf
    rw [e2]
    rfl
  obtain ⟨a, hl, ha1, ha2⟩ := laid_cons _ A.cutB
  have q1 : (batAt guardedProximityTestParts p (laidOf p) : Block T12 Unit).rounds.length = 1 := by
    show (((laidOf p).take 1).map (·.1)).length = 1
    rw [hl]
    rfl
  have q2 : (batAt guardedProximityTestParts p (laidOf p) : Block T12 Unit).openings = 0 := by
    show (((laidOf p).take 1).map (·.1)).foldl
      (fun n r => n + r.stored.length + r.opens.length) 0 = 0
    rw [hl]
    show 0 + a.1.stored.length + a.1.opens.length = 0
    rw [ha1, ha2]
    rfl
  rw [ez, q1, q2] at k1 k3
  obtain rfl : batT t G row = t₁ := Except.ok.inj (hb.symm.trans k1)
  intro G' row' hG' hr'
  obtain rfl : G = G' := Option.some.inj (H.group.symm.trans hG')
  obtain rfl : row = row' := Option.some.inj (hr.symm.trans hr')
  exact vals_of_accept p _ 0 first (laidS p) _ t' _ _ k3

/-- **Under `OneAsks` the block accepts if and only if `ValsAsk` holds.** `OneAsks` itself contains
a test on the values of the open rows before the test (`claims`); `ValsAsk` is the hypothesis on the
values of the block's own rounds and columns. -/
theorem k12_accept_iff_one (A : OneAsks p cur nxt rest t i n id tN rB R gs) :
    (∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t ((rB :: R).map noDigest) gs = .ok t') ↔
      ValsAsk p cur nxt rest t rB R gs :=
  ⟨fun ⟨_, h⟩ => vals_of_block A h, k12_returns_asks A⟩

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.k12_returns_asks
#print axioms ProofFile.Honest.Sh.vals_of_block
#print axioms ProofFile.Honest.Sh.k12_accept_iff_one
#print axioms ProofFile.Honest.Sh.OneAsks
#print axioms ProofFile.Honest.Sh.ValsAsk
