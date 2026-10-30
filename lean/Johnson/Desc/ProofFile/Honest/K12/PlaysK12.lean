-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlaysK12.lean: the condition `PlaysOn`
(Johnson/Desc/ProofFile/Honest/Law/ThreadC.lean: the first of two conditions on one sub-protocol of
a chain) is proved, under hypotheses, at every block b that has a proximity test's place, rounds and
oracle messages and whose decision is the test's between two functions `enter` and `leave`
(`SeatOf`, SaysYesSeat.lean in this folder), where the prover's side at that place is the half
`proverSideOfProximityTest J`. `PlaysOn` says of a sub-protocol, at all coins: from A, at challenges that its rounds
can draw and at which nothing of it stops: `play` returns and the columns are filled; and if the
sub-protocol's own step accepts them, B holds after it. That `chainSteps` returns is among its
hypotheses. The theorem is general in b, `enter` and `leave`, the job J, the face φ, the book Bk,
the chain's number, the number ft in the label of its first own tree, the list hs of prover's sides,
and the conditions A and B. Two definitions and two theorems.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean; `play`, `chainSteps`, `lendRow`,
`fillCols` and `drawsFit` are its functions. A block (`Block`, Johnson/Desc/Block.lean) is a
sub-protocol at one place (`Place`) of a description's chain. The job J (`TestJob`, Test.lean in
this folder) is what a caller supplies for its test. The plan is `J.p` (`P12`,
Johnson/Desc/K12/Frame.lean: the test's parameters), with its place `J.p.place` and its list of
stages `J.p.nums.stages`. The test's own block is `proximityTestKind guardedProximityTestParts J.p`, and the declared rounds are
its field `rounds`. `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean) pairs the rounds that
`roundsOfNums` (Johnson/Desc/K12/TestEntries.lean) computes from `p.nums` with the oracle messages
`p.oracles`. The term is `testAll` (Test.lean): the one value of which each move's message is a
round. A part (`Part`, the frame) is the prover's side of a stretch of rounds, with one move for
each. The half is the test's two parts, `firstPart J` and `restPart J`, at the place `J.p.place`
(`proverSideOfProximityTest`, of type `Placed`, Parts.lean in this folder). c is what the two parts are given
(`RowCoins`, the frame). A part's reader makes a family of coins (`TestCoins`, Test.lean) of what
the part is given: `firstRd J` (HalfSteps.lean in this folder) is the first part's, `restCoins J`
(Parts.lean) the second's. φ is the chain's face (`Face`, the frame). Bk is a book (`ProverCoinCounts`, the
frame): public data that goes with a description. A and B are conditions on a whole run's coins k
(`Coins Bk`), the verifier's state, the state m of the prover's run (`Mid`, the frame) and the
available tables E (`Env`, Johnson/Desc/ProofFile/Honest/Side.lean). A source (`Fmt.TreeSource`) names
the tree that a declared opening opens; it is old at a number n (`oldSrc`, ColsReturn.lean in this
folder) if it is `taken`, or `own` with a number below n.

  `playsOn_k12`: under the hypotheses below, `PlaysOn φ Bk chain ft hs b A B`
  `PlanPlays J s rest sent`: a definition: the hypotheses on the plan, in six fields. s and rest are
    meant as the first stage and the later ones, `sent` as the number of trees that the chain has
    sent before the test. No field names a run. `tables` and `wide` also read whether `J.fresh` is
    `none`
  `PlanPlays.plan`: the test's own block passes its test on the plan (`planOk`)
  `PlanPlays.sorts`: the declared rounds ask just the sorts of items that the term shows. As Lean
    has it: `asked` (Johnson/Prover/Link/BodySorts.lean: a declared round's items without the roots)
    of the rounds of `laidOf J.p` is `[] :: bodyItems s rest` (Johnson/Prover/Link/LinkItems.lean).
    Where the stages are s :: rest, `test_sorts` (FitsAll.lean in this folder) equates that list
    with `sortsOf` of the term's rounds
  `PlanPlays.tables`: `tablesFitB J` (FitsAll.lean) is true: each declared oracle message has the
    depth and the width of the tree that the term sends
  `PlanPlays.count`: `termLen` of the stages (TermLen.lean in this folder: the term's number of
    rounds, by `length_test`) is the number of the declared rounds
  `PlanPlays.stored`: no declared round opens a stored table: its field `stored` is empty
  `PlanPlays.wide`: `newWideB J` (ColsReturn.lean) is true at the declared rounds and `sent`: every
    declared opening whose source is not old at `sent` opens the tree of a sending round of the
    test, at that tree's width
  `RunPlays J sent m E c`: a definition: the hypotheses on a run, in three fields. The hypothesis HA
    of `playsOn_k12` requires them wherever A holds
  `RunPlays.agree`: the two parts' readers agree. As Lean has it: `Agree` (CoinsAgree.lean in this
    folder) at the input `m.st.input`, the front `frontOf m` (PlayedTerm.lean in this folder: the
    front at which a play from m begins) and the job's first stage `J.s₀`; the two families of coins
    are `firstRd J c.1` and `restCoins J c.2.1`
  `RunPlays.sent`: `E.sent`, the number of trees that the chain has sent so far, is the parameter
    `sent` of `RunPlays`, which has the field's name
  `RunPlays.old`: for every declared opening whose source is old at `E.sent`, `E.tree` has a table
    at that source, and the table's `words` are the width `W` that the opening declares
  `zip_laid`: where the test's own block at parameters p passes its test on the plan, its rounds
    zipped with its oracle messages are `laidOf p`

By what. `playsOn_k12` joins three theorems of this folder. `half_returns` (HalfReturns.lean):
`play` at the half's steps returns. `played_term` (PlayedTerm.lean): the tables of the rounds as
played are those of the term's messages. `cols_return` (ColsReturn.lean): `fillCols` returns after
that play. `steps_one_half` (Johnson/Desc/ProofFile/Honest/Law/Thread.lean) gives the list that
`chainSteps` returns as the half's steps at the c that `lendRow` returns. The lengths come from
`member_lengths` and `zip_length` (Johnson/Desc/ProofFile/Honest/Small/SaysYesOf.lean),
`drawsFit_length` (Johnson/Desc/ProofFile/Honest/Law/Along.lean), `first_moves` and `rest_moves`
(HalfSteps.lean), `length_test` (TermLen.lean) and `zip_laid`. `zip_laid` rewrites by `k12_rounds`
and `k12_oracles` (Johnson/Desc/K12/FrameLaws.lean).

Hypotheses of `playsOn_k12`. hb: `SeatOf b J enter leave`: b has the place, the rounds and the
oracle messages of the test's own block, and its decision is `enter`, then that block's decision,
then `leave`. hst: the stages are s :: t :: rest: two stages or more. hk: at the first stage, `s.k`
is h + g of `sgOf s` (Johnson/Desc/K12/Law/ChainOf.lean). hf: the first element of hs at the place
`J.p.place` is `proverSideOfProximityTest J`. P: `PlanPlays J s (t :: rest) sent`. HA: wherever A holds at (k, st, m,
E), at every list ds of which `drawsFit` at the declared rounds is true, and at the c that `lendRow`
returns for the two parts at the book's table for the chain and the coins `k.look chain`:
`RunPlays J sent m E c`. HB: wherever A holds at (k, st, m, E), `drawsFit` at the rounds of b is
true of ds, `chainSteps` returns l, `play` at l and ds from m returns y, `fillCols` returns cols and
the step of b at st, `roundsOf y.1` and cols returns (s', n): B holds at (k, s', `y.2.took cols`,
`E.add y.1`): at the state behind the sub-protocol, which has taken the columns read.

Limits.
- `PlanPlays` and `RunPlays` are hypotheses; no value that meets them is given here. For
  `PlanPlays`: values that meet it lie in PlanPlaysAt.lean in this folder (not in the library yet).
  For `RunPlays`, from the frame's `Thr` (Johnson/Desc/ProofFile/Honest/Thread/Thr.lean):
  RunOfThr.lean in this folder (not in the library yet), which derives it under hypotheses of its
  own and gives no value that meets it. So neither condition has a value that meets it in the
  library yet.
- The values in PlanPlaysAt.lean are all at jobs whose fresh table has come earlier (`J.fresh` is
  `some _`), and RunOfThr.lean treats only such a job. Where the first fold sends its own table
  (`J.fresh` is `none`), no file that this head names gives a value that meets `PlanPlays`, or one
  that meets `RunPlays.agree` at the two parts' readers.
- The last hypothesis, HB, is the conclusion's own clause on B: nothing is said of B.
- `PlaysOn` holds vacuously where the frame's `chainSteps` at the block and hs does not return. That
  it returns: StepsReturn.lean in this folder (not in the library yet), in the first and the shared
  chain, under a test on the book and the job; values that pass that test lie in StepsToy.lean (not
  in the library yet) and StepsAtKey.lean (not in the library yet) in this folder. This head names
  no file in the library that shows that it returns.
- `PlaysOn` speaks only where A holds, and A may narrow the coins.
- The field `stored` of `PlanPlays` could be derived; here it is a hypothesis.
- Nothing on whether the step accepts (see SaysYesSeat.lean).
- `PlaysOn` is a definition of ThreadC.lean, meant as a hypothesis; it is none of the library's
  goals.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.HalfReturns
import Johnson.Desc.ProofFile.Honest.K12.ColsReturn
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Johnson.Desc.K12.FrameLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (member_lengths zip_length)

variable {S Cl V W X Pb : Type}

theorem zip_laid (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) :
    (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds.zip (proximityTestKind guardedProximityTestParts p : Block T12 Unit).oracles =
      laidOf p := by
  unfold laidOf
  rw [K12.k12_rounds guardedProximityTestParts p hp, K12.k12_oracles guardedProximityTestParts p hp]
  rfl

/-- The hypotheses on the plan. `sent`: meant as the number of trees that the chain has sent before
the test. -/
structure PlanPlays (J : TestJob W X) (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (sent : ℕ) :
    Prop where
  plan : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true
  sorts : (laidOf J.p).map asked = [] :: bodyItems s rest
  tables : tablesFitB J = true
  count : termLen J.p.nums.stages = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length
  stored : ∀ d ∈ (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds, d.stored = []
  wide : newWideB J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds sent = true

/-- The hypotheses on a run. The hypothesis `HA` of `playsOn_k12` requires them wherever A holds. -/
structure RunPlays (J : TestJob W X) (sent : ℕ) (m : Mid W X) (E : Env)
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) : Prop where
  agree : Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1)
  sent : E.sent = sent
  old : ∀ d ∈ (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds, ∀ o ∈ d.opens,
    oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W

/-- **`PlaysOn` at a block that `SeatOf` ties to a proximity test, under hypotheses.** The prover's
side at the block's place is `proverSideOfProximityTest J`. The file's head has a clause on each hypothesis. -/
theorem playsOn_k12 (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : ℕ) (hs : List (Placed V W X))
    (b : Block S Cl) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave)
    (A B : Coins Bk → S → Mid W X → Env → Prop) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)) (sent : ℕ)
    (P : PlanPlays J s (t :: rest) sent)
    (HA : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m E →
      drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c → RunPlays J sent m E c)
    (HB : ∀ k st m E ds l (y : List Played × Mid W X) cols s' n, A k st m E →
      drawsFit b.rounds ds = true →
      chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs = .ok l →
      play l ds [] m = .ok y →
      fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] = .ok cols →
      b.step ft st (roundsOf y.1) cols = .ok (s', n) → B k s' (y.2.took cols) (E.add y.1)) :
    PlaysOn φ Bk chain ft hs b A B := by
  intro k st m E ds l hA hd _ hl
  have hpl := hb.place
  have hf' : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J) := by
    rw [hpl]
    exact hf
  obtain ⟨ho, hr⟩ := member_lengths hf' hl
  have hl₀ := hl
  obtain ⟨c, hc, rfl⟩ := steps_one_half hf' hl
  rw [hpl] at hc
  have hdr := hd
  rw [hb.rounds] at hdr
  obtain ⟨ag, hsent, hold⟩ := HA k st m E ds c hA hdr hc
  have hs0 : J.s₀ = s := by
    unfold TestJob.s₀
    rw [hst]
    rfl
  rw [hs0] at ag
  have hz := zip_laid J.p P.plan
  have hzl := zip_length ho hr
  rw [hb.rounds, hb.oracles, hz] at hzl
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  have hrs : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    refine hzl.trans ?_
    show (firstPart J : Part V W X).moves.length + ((restPart J : Part V W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  have hzr : (laidOf J.p).length = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length := by
    have ho' := ho
    rw [hb.rounds, hb.oracles] at ho'
    rw [← hz, List.length_zip, ho', Nat.min_self]
  have hlen : ds.length = (laidOf J.p).length := by
    rw [hzr]
    exact drawsFit_length _ _ hdr
  obtain ⟨y, hy⟩ := half_returns J s t rest hst hk b.name (φ.sees m.st.input) hrs c ds [] m ag
    P.sorts P.tables hlen
  have hy' : play ((proverSideOfProximityTest J).steps b (φ.sees m.st.input) c) ds [] m = .ok y := by
    unfold Placed.steps
    rw [hpl, hb.rounds, hb.oracles, hz]
    exact hy
  obtain ⟨-, q2, -, -, -⟩ := played_term J s t rest hst hk _ _ _ hrs c ds [] m y hy ag
    ((length_test J _ _ _ _).trans (P.count.trans hzr.symm))
  rw [hzr] at q2
  obtain ⟨cols, hcols⟩ := cols_return J m.st.input (frontOf m) (restCoins J c.2.1) ds
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds E y.1 chain ft q2 P.stored hold (by
                                     rw [hsent]
                                     exact P.wide)
  have hcols' : fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] =
      .ok cols := by
    rw [hb.rounds]
    exact hcols
  exact ⟨y, cols, hy', hcols', fun s' n hstep =>
    HB k st m E ds _ y cols s' n hA hd hl₀ hy' hcols' hstep⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.zip_laid
#print axioms ProofFile.Honest.K12.playsOn_k12
#print axioms ProofFile.Honest.K12.PlanPlays
#print axioms ProofFile.Honest.K12.RunPlays
