-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TestYes.lean: the proximity test's block accepts all that
`testAll` shows, where its shares accept theirs. Two theorems with their proofs and one structure
of hypotheses, general in the job, the prover's input, the coins and the challenges. Every
acceptance of a share is a hypothesis, or follows from an invariant that is a free parameter. The
theorems join the library's statements on how the block is composed. WholeTest.lean in this folder
calls both.

In the list: a job J (`TestJob`, Test.lean in this folder) is what a caller supplies for its test.
`J.p` (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place at which the test is,
among them the list of stages (`Fmt.M1.Stage`). w is the prover's input; fr is what precedes the
test (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean). C: the coins that `testAll` reads, by number
(`TestCoins`). D: the sampled challenges by the round's number, "BAT" being round 0. The test's
block is `proximityTestKind guardedProximityTestParts J.p` (`proximityTestKind`: Frame.lean as above; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean;
`Block`: Johnson/Desc/Block.lean). Its shares are the pieces of which it is composed, in order: the
front, which has no round; the batching, at the first declared round; the block's own test that the
group of oracle messages under test is the first stage's (`firstFits`); the stages' block
(`stagesFrom`). The stages' block is composed, for each stage but the last, of a fold, a switch, the
batching after the switch and a test that, where the masks come early (`early`), the next mask has
come; the last stage is the base case. The block cuts the rounds and the groups of opened columns
among its shares. "Accepts": the decision (the field `decide` of a `Block`, or of a `Part` of
Frame.lean) returns `.ok` with a state. It is handed a state of the type `T12`
(Johnson/Desc/K12/Join.lean), rounds without their digests (`noDigest`) and groups of opened
columns. `J.rec₀ w fr` is the state on entry to the test, which the job computes. `J.recB w fr d`
is the state after the batching; where the front or the batching rejects, it keeps the state before
that share.

  `test_yes`: where the place has a first stage, rounds and oracle messages (hs, hr, ho), `DoorYes`
    holds at `D 0`, and the stages' block, from the state after the batching, accepts the rounds
    and groups of `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean) at the arguments at which
    `testAll` calls it and returns t': from the state on entry, the test's block accepts all that
    `testAll` shows, and returns t'. Of what `testAll` returns (`BOut`,
    Johnson/Prover/Link/BodyAll.lean) the decision is handed the rounds and the groups; the trees'
    columns (`tr`) are no argument of a decision
  `stages_yes`: at two stages or more (cur, next, then rest) and any list of first trees, under the
    hypotheses below: the stages' block accepts all that `stagesAll` shows, and `Post` holds of the
    state that it returns. As above, the decision is handed the rounds and the groups
  `DoorYes J w fr d first`: a structure of five hypotheses on what comes before the stages. d: what
    "BAT" sampled. `front`: the front accepts, from the state on entry, on no round and no group.
    `bat`: the batching accepts, from the state that the front returns, its one round, which has no
    value and d as what was sampled, and no group. `nB`, `oB`: two numbers of the block's cut: the
    batching's block (`batAt`, Johnson/Desc/K12/FrameLaws.lean) has one round and no opening.
    `group`: the group in the state after the batching is the first stage's

By what. `stages_yes`: `body_yes_of` (Johnson/Prover/Link/BodyYes.lean), the induction over the
stages, gives from hstep, hbase and hI that the stages' block from the second stage on accepts the
rounds and groups of `bodyAll` (BodyAll.lean as above); `stages_yes_first`
(Johnson/Desc/K12/Honest/FirstYes.lean) is the induction's first step at several trees. `test_yes`
unfolds `testAll` and `TestJob.laid`, replaces by `getD_of_ok` (BodyYes.lean) the states that
`DoorYes` and `recB` name by the states that the front and the batching return, and calls
`k12_yes` (Johnson/Prover/Link/TestYes.lean), the converse of `k12_ok` (FrameLaws.lean).

Hypotheses of `stages_yes`. Inv and Post are free parameters. Y: `FirstYes` (FirstYes.lean): the
first stage's fold, switch and batching after the switch accept their rounds and groups; the test on
the next mask passes; four numbers of the block's cut, the switch having as many openings as there
are first trees. hfit: each stage from the second on fits the next (`FitAll`, Stages.lean). hI: Inv
holds after the first stage, at the state, the prover's state and the new tree's column that the
first stage leaves (`t3At`, `qAt`, `aCol`). hstep: before a stage that is not the last, Inv gives
`StageYes` (BodyYes.lean), which contains that stage's acceptances, and Inv after the stage. hbase:
before the last stage, Inv gives that the base case accepts the rounds and groups of `lastOut`
(BodyAll.lean), and Post of the state that it returns.

Limits. No acceptance of a share is shown here. No values that meet `DoorYes` are given in this
file. No invariant that meets hstep and hbase is given in this file. "Accepts" is the decision's
`.ok` only: the block's test on the plan (`planOk`) and the two tests of `Block.step` (Block.lean)
before the decision, on the rounds' form and on the columns' keys, positions and widths, are not
concluded. The state on entry is whatever the job's function `rec₀` returns at w and fr. It is
compared with nothing here: it is not shown to be the verifier's. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Test
import Johnson.Desc.K12.Honest.FirstYes
import Johnson.Prover.Link.TestYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- **The stages' block accepts the rounds and groups of `stagesAll`**, at two stages or more, and
`Post` holds of the state that it returns. Every acceptance of a share is a hypothesis (Y) or
follows from the invariant Inv, a free parameter (hI, hstep, hbase). hfit: each stage from the
second on fits the next. -/
theorem stages_yes (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn)
    (Inv : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) → Prop)
    (Post : T12 → Prop)
    (hstep : ∀ next rest j cur l o t P col, Inv (next :: rest) j cur l o t P col →
      StageYes p K rest j cur next l o t P col D ∧
        Inv rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
          (sNext K rest.isEmpty j cur next o P (rowOf t) D)
          (sCol K rest.isEmpty j cur next o P (rowOf t) D))
    (hbase : ∀ j cur l o t P col, Inv [] j cur l o t P col →
      ∃ t', (guardedProximityTestParts.base p j cur (l.map (·.1))).decide t
        ((lastOut p j cur o t P col (rowOf t) D).rs.map noDigest)
        (lastOut p j cur o t P col (rowOf t) D).gs = .ok t' ∧ Post t')
    (rest : List Fmt.M1.Stage) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12)
    (P : PS) (trees : List Tree) (Y : FirstYes p K rest j cur next l o t P trees D)
    (hfit : FitAll next rest)
    (hI : Inv rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (t3At p K rest j cur next l o t P trees D) (qAt K rest j cur next o P D)
      (aCol rest.isEmpty next (qAt K rest j cur next o P D))) :
    ∃ t', (stagesFrom guardedProximityTestParts p j cur (next :: rest) l : Block T12 Unit).decide t
      ((stagesAll p K (next :: rest) j cur l o t P trees D).rs.map noDigest)
      (stagesAll p K (next :: rest) j cur l o t P trees D).gs = .ok t' ∧ Post t' := by
  obtain ⟨t', ih, hP⟩ := body_yes_of p K D Inv Post hstep hbase rest _ _ _ _ _ _ _ hI
  exact ⟨t', stages_yes_first p K rest j cur next l o t P trees D Y hfit t' ih, hP⟩

variable {W X : Type}

/-- Hypotheses on what comes before the stages: the front and the batching accept, the batching's
block has one round and no opening, and the group after the batching is the first stage's. d: what
"BAT" sampled. first: the first stage. -/
structure DoorYes (J : TestJob W X) (w : W) (fr : Front X) (d : Fmt.Drawn) (first : Fmt.M1.Stage) :
    Prop where
  front : ∃ t₀, (guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] [] = .ok t₀
  bat : ∃ t₁, (guardedProximityTestParts.bat J.p ((J.laid.take 1).map (·.1))).decide
    (((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD (J.rec₀ w fr))
    [noDigest ⟨[], d⟩] [] = .ok t₁
  nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1
  oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0
  group : (guardedProximityTestParts.group (J.recB w fr d)).any (firstFits first) = true

/-- **The test's block accepts the rounds and groups of `testAll`**, from the state on entry, and
returns t': where the place has a first stage, rounds and oracle messages (hs, hr, ho), `DoorYes`
holds (Y), and the stages' block, from the state after the batching, accepts the rounds and groups
of `stagesAll` and returns t' (h3). -/
theorem test_yes (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (ds : List Fmt.DeclaredRound)
    (os : List (List (ℕ × ℕ))) (hs : J.p.nums.stages = first :: rest)
    (hr : H2U.roundsOfNums J.p.nums = some ds) (ho : H2U.testOracles J.p.nums = some os)
    (Y : DoorYes J w fr (D 0) first) (t' : T12)
    (h3 : (stagesFrom guardedProximityTestParts J.p 0 first rest (J.laid.drop 1) : Block T12 Unit).decide
      (J.recB w fr (D 0))
      ((stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 first (J.laid.drop 1) 1
        (J.recB w fr (D 0)) (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).rs.map
        noDigest)
      (stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 first (J.laid.drop 1) 1
        (J.recB w fr (D 0)) (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).gs =
        .ok t') :
    (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' := by
  obtain ⟨t₀, h0⟩ := Y.front
  obtain ⟨t₁, h1⟩ := Y.bat
  have hl : J.laid = ds.zip J.p.oracles := by
    unfold TestJob.laid
    rw [hr]
    rfl
  have e0 : ((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD (J.rec₀ w fr) = t₀ :=
    getD_of_ok h0
  have eB : J.recB w fr (D 0) = t₁ := getD_of_ok h1
  have nB := Y.nB
  have oB := Y.oB
  have hg := Y.group
  rw [e0] at h1
  rw [eB] at h3 hg
  rw [hl] at nB oB h1 h3
  have eT : testAll J w fr C D = ⟨⟨[], D 0⟩ :: (stagesAll J.p
      (coinsOf J.p.nums.stages C.hide C.rest) rest 0 first (J.laid.drop 1) 1 (J.recB w fr (D 0))
      (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).rs,
      (fun _ => []) :: (if J.fresh.isNone then (stagesAll J.p
        (coinsOf J.p.nums.stages C.hide C.rest) rest 0 first (J.laid.drop 1) 1 (J.recB w fr (D 0))
        (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).tr.set 0
        (freshCol (sgOf first) (J.first w fr C)) else (stagesAll J.p
        (coinsOf J.p.nums.stages C.hide C.rest) rest 0 first (J.laid.drop 1) 1 (J.recB w fr (D 0))
        (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).tr),
      (stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 first (J.laid.drop 1) 1
        (J.recB w fr (D 0)) (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C)) D).gs⟩ := by
    unfold testAll
    rw [hs]
  rw [eT, eB, hl]
  refine k12_yes guardedProximityTestParts J.p first rest ds os _ t₀ t₁ t' _ _ hs hr ho h0 ?_ hg ?_
  · rw [nB, oB]
    exact h1
  · rw [nB, oB]
    exact h3

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.stages_yes
#print axioms ProofFile.Honest.K12.test_yes
#print axioms ProofFile.Honest.K12.DoorYes
