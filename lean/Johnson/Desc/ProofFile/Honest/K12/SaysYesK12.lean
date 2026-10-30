-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SaysYesK12.lean: from "the decision of the test's block accepts
all that the term shows" to the frame's sentence "outside the stops and outside its fall the
member's own step accepts" (`SaysYes`, Johnson/Desc/ProofFile/Honest/Law/ThreadC.lean), at a seated
proximity test with the half `proverSideOfProximityTest J`. The theorem `saysYes_k12` derives `SaysYes` from the
structure `K12At`, which has five clauses, all of them hypotheses. It is general in `enter` and
`leave`, in the book, in the chain's number and in the free parameters A and `fall`. A structure, a
theorem and a lemma, with their proofs.

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean with the files that build on it. The
test's block is `proximityTestKind guardedProximityTestParts J.p` (Johnson/Desc/K12/Frame.lean): the proximity test as a
sub-protocol (`Block`, Johnson/Desc/Block.lean) on a state of type `T12`. "Seated" means wrapped as
`Block.inside enter (proximityTestKind guardedProximityTestParts J.p) leave` (Block.lean), a sub-protocol on a state of any type S:
its decision calls `enter` on the state before the test, then the block's decision, then `leave`
("the seat's leaving"). A member is a sub-protocol of a chain's list; "the member" is the seated
test. A job J (`TestJob`, Test.lean in this folder) is what a caller supplies for its test; `J.p`
has the test's parameters, among them its place (`Place`) and its stages (`Fmt.M1.Stage`). The term
is `testAll` at J (Test.lean); its rounds `rs` and its groups of columns `gs` are read here. The
half `proverSideOfProximityTest J` (Parts.lean) is the prover's side at the test's place (`Placed`, Frame.lean): a
list of two parts (`Part`), `firstPart J` and `restPart J`. The book (`ProverCoinCounts`, Frame.lean) is public
data that goes with a description. A front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean) is what
a job's functions are given of the run besides the input. "The letter A" is a free parameter: a
condition on a run's coins (`Coins`), the state before the member, the state of the chain's run
(`Mid`) and the available tables (`Env`, Johnson/Desc/ProofFile/Honest/Side.lean). `fall` is a
function of the state before the member and of the member's challenges; "outside its fall" is where
it returns `none`. "Outside the stops" is where `chainStopAt`
(Johnson/Desc/ProofFile/Honest/Rule.lean) returns `none`. "In front of" and "behind" mean before and
after, in the order of the run.

  `saysYes_k12`: under the four hypotheses below, `SaysYes` holds at the sub-protocol
    `Block.inside enter (proximityTestKind guardedProximityTestParts J.p) leave`, at `fall` and A
  `K12At`: what is asked where the letter A holds, at the coins that the book lends the two parts
    and at the member's challenges; each clause under its name: see below
  `k12_place`: the block `proximityTestKind guardedProximityTestParts p` has the place `p.place`, at every p

`K12At`'s clauses. w: the input; fr: the front at which the member's play begins; C: what the second
part's reader reads of its coins; D: the member's challenges by number. In Lean: w is `m.st.input`,
fr is `frontOf m` (PlayedTerm.lean in this folder), C is `restCoins J c.2.1` (Parts.lean), D is
`byNo ds` (PlayedTerm.lean).
  `agree`: the two parts' readers agree on what the first part's rounds read (`Agree`). `Agree` is
    defined in CoinsAgree.lean; the readers are `firstRd J` (HalfSteps.lean) and `restCoins J`
  `count`: the term has as many rounds as the block declares. By `length_test` (TermLen.lean) the
    term's number of rounds is computed from the stages only
  `opens`: there are a list of depths and a function src₀ to sources such that three things hold.
    The job's trees (`J.trees₀` at w, fr and C) have these depths. `OpensFit` (ColsTerm.lean) holds
    at the block's declared rounds, the depths, src₀ and `E.sent`; `opensFitB`
    (OpensFitB.lean (not in the library yet)) is an executable test for it. `OldAt` (ColsTerm.lean)
    holds: at the k-th source the tables available before the member (`E.tree`) have the columns of
    the job's k-th tree, at the positions below that tree's length; and a source `.own n` has n
    below `E.sent`
  `enters`: `enter st` returns `J.rec₀ w fr`, the job's state on entry to the test
  `accepts`: two halves: the decision of the test's block accepts all that `testAll` shows; and the
    seat's leaving returns at the state behind. In Lean: `decide` of the block, at `J.rec₀ w fr`, at
    the term's rounds under `noDigest` and at the term's groups, returns some t'; and `leave st t'`
    returns

By what. `saysYes_of_play` (Johnson/Desc/ProofFile/Honest/Small/SaysYesOf.lean) reduces `SaysYes` to
the sub-protocol's decision on the rounds as played and on `colGroups` at the tables after the play.
`played_term` (PlayedTerm.lean): the rounds as played are the term's rounds. `cols_term`
(ColsTerm.lean): these groups are the term's groups. The numbers of rounds: `first_moves` and
`rest_moves` (HalfSteps.lean), `zip_length` (SaysYesOf.lean).

Hypotheses of `saysYes_k12`. `hst`: the job has two stages or more. `hk`: at the first stage s,
`s.k = (sgOf s).h + (sgOf s).g`. `hf`: in the list hs of prover's sides, the first at the place
`J.p.place` is `proverSideOfProximityTest J`. `HA`: `K12At J enter leave st m E ds c` holds wherever A holds at k,
st, m and E, the challenges ds fit the block's declared rounds (`drawsFit`), `fall st ds` is `none`,
and `lendRow` (Frame.lean), at the book, the chain's rows and the coins k, returns c for the two
parts.

Limits.
- Every clause of `K12At` is a hypothesis: five fields. No value that meets it as a whole is given.
- `HA` asks `K12At` at more runs than `SaysYes` speaks of. Of the ten fields of `YesGiven`
  (SaysYesOf.lean), which is what `saysYes_of_play` supplies, the proof hands `HA` four: `stand`,
  `draws`, `noFall` and `lent`. Not handed on: that `rowStopAt` returns `none` (`silent`), and that
  `chainSteps`, `play` and `fillCols` return (`laid`, `played`, `filled`).
- "accepts": its first half is the conclusion of the theorems of WholeShape.lean, WholeAll.lean and
  PlanB.lean in this folder, under their hypotheses and within their reach.
- Its second half: at the key file's test on the ranges the seat's leaving asks that the test has
  run to its end (`testEnded`, Johnson/Desc/Key/Ranges.lean: nothing is passed any more; every group
  from the one under test on has begun its test and holds no open row; every oracle message is
  sampled or spent as a mask): from a test on the shape in front: `leaves_ranges`
  (Ended.lean (not in the library yet) in this folder). `testEnded` also asks that the group under
  test is there; `leaves_ranges` also takes `p.early = true` and `p.answers = 1`, and its test on
  the shape (`endedB`) is a hypothesis.
- "enters": the job's state in front is a function of the input and of the front (the challenges
  heard, what is handed on, the rounds shown). A front holds no column: where a member in front of
  the test has read columns of trees that were sent in the run, and the verifier's state holds
  something of them, no such function can meet this clause.
- `SaysYes` is a definition of the frame's, meant as a hypothesis. It holds vacuously where
  `chainSteps`, `play` or `fillCols` (Frame.lean) returns an error. Under which hypotheses they
  return at a proximity test's half: StepsReturn.lean (not in the library yet) and PlaysK12.lean in
  this folder.
- Where the first fold sends its own table `OldAt` cannot be met: that case is not served.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ColsTerm
import Johnson.Desc.ProofFile.Honest.Small.SaysYesOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (colGroups saysYes_of_play zip_length)

variable {S V W X Pb : Type}

theorem k12_place (p : P12) : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).place = p.place := by
  unfold proximityTestKind
  split <;> rfl

/-- What `saysYes_k12` asks wherever its parameter A holds: five clauses, each described at the top
of this file. st: the state before the test. m: the state of the chain's run. E: the available
tables. ds: the test's challenges. c: the coins that the two parts are given. -/
structure K12At (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (st : S) (m : Mid W X) (E : Env) (ds : List Fmt.Drawn)
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) : Prop where
  agree : Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1)
  count : (testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).rs.length =
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length
  opens : ∃ depths src₀,
    (J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
      (J.first m.st.input (frontOf m) (restCoins J c.2.1))).map (·.1) = depths ∧
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds depths src₀ E.sent ∧
    OldAt E (J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
      (J.first m.st.input (frontOf m) (restCoins J c.2.1))) src₀
  enters : enter st = .ok (J.rec₀ m.st.input (frontOf m))
  accepts : ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ m.st.input (frontOf m))
    ((testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).rs.map noDigest)
    (testAll J m.st.input (frontOf m) (restCoins J c.2.1) (byNo ds)).gs = .ok t' ∧
    ∃ s', leave st t' = .ok s'

/-- **Where A gives `K12At`, `SaysYes` holds at the test wrapped by `Block.inside`.** Hypotheses and
limits: at the top of this file. -/
theorem saysYes_k12 (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : ℕ) (hs : List (Placed V W X))
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (fall : S → List Fmt.Drawn → Option String) (A : Coins Bk → S → Mid W X → Env → Prop)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (HA : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m E →
      drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true → fall st ds = none →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c → K12At J enter leave st m E ds c) :
    SaysYes φ Bk chain ft hs (Block.inside enter (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit) leave) fall
      A := by
  have hpl : (Block.inside enter (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit) leave).place = J.p.place :=
    k12_place J.p
  refine saysYes_of_play (g := proverSideOfProximityTest J) (by rw [hpl]; exact hf) fun k st m E ds c y cols h => ?_
  have hlent := h.lent
  rw [hpl] at hlent
  obtain ⟨ag, cnt, ⟨depths, src₀, hdep, hO, hE⟩, hen, ⟨t', hacc, s', hlv⟩⟩ :=
    HA k st m E ds c h.stand h.draws h.noFall hlent
  have hs0 : J.s₀ = s := by
    unfold TestJob.s₀
    rw [hst]
    rfl
  rw [hs0] at ag
  have hzl := zip_length h.oracles h.rounds
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  have hrs : ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.zip
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    refine hzl.trans ?_
    show (firstPart J : Part V W X).moves.length + ((restPart J : Part V W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  have hzr : ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.zip
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles).length =
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length := by
    have ho : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles.length =
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length := h.oracles
    rw [List.length_zip, ho, Nat.min_self]
  have hplay : play (rowSteps (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).name J.p.place
      (φ.sees m.st.input) [(firstPart J : Part V W X), restPart J] 0
      ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.zip (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
      c) ds [] m = .ok y := by
    have := h.played
    unfold Placed.steps at this
    rw [hpl] at this
    exact this
  obtain ⟨q1, q2, -, -, -⟩ := played_term J s t rest hst hk _ _ _ hrs c ds [] m y hplay ag
    (cnt.trans hzr.symm)
  rw [hzr] at q2
  have q3 := cols_term J m.st.input (frontOf m) (restCoins J c.2.1) ds s (t :: rest) hst
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds depths src₀ E y.1 hdep hO hE q2
    (drawsFit_length _ _ h.draws)
  refine ⟨s', ?_⟩
  show (enter st).bind (fun t₀ => ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide t₀
    ((roundsOf y.1).map noDigest) (colGroups (E.add y.1).stored (E.add y.1).tree
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds)).bind (leave st)) = .ok s'
  rw [hen, q1, q3]
  show ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide _ _ _).bind (leave st) = .ok s'
  rw [hacc]
  exact hlv

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.k12_place
#print axioms ProofFile.Honest.K12.saysYes_k12
#print axioms ProofFile.Honest.K12.K12At
