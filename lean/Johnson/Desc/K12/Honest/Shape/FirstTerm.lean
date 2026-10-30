-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/FirstTerm.lean: at the stages' term the door and the first stage of a
proximity test accept, from tests on the shape, at a group of any layout, in any number of trees, in
both cases of the first fold's fresh table. Not every hypothesis is a test on the shape: see
"Hypotheses" and "Limits". Two results are joined. `first_stage_of_shape` and
`first_stage_of_shape_own` (TestSwitch.lean in this folder) prove the first stage from the shape,
with the hypothesis that the switch's reading accepts (`ReadsAny`). `read_first_any` (ReadFirst.lean
in this folder) proves that the reading accepts the term's own columns. The conclusion is `FirstYes`
(Johnson/Desc/K12/Honest/FirstYes.lean), and next to it: the front and the batching accept, and the
question that the test's own frame asks after the batching is true. All parameters are universally
quantified: the place, the stages, the state before the test, the sampled challenges, and what the
term reads. Definitions and theorems. The file does not depend on the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: the parts of a proximity test are fields of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean;
their type is `Parts`, Johnson/Desc/K12/Frame.lean): the front, which has no round; the batching
(`bat`), with the round "BAT"; for each stage but the last a fold, a switch and the batching after
the switch (`batBehind`). A state is a value of `T12` (Johnson/Desc/K12/Join.lean), the type of the
verifier's state inside a test. A part accepts where its `decide` returns `.ok` with the next state.
In the field `pass` of the state a part passes something on to the next: a batching a claim with its
layout (`GroupLayout`), a fold single rows. The shape of a state is `testSh` of it
(Johnson/Desc/K12/Honest/Shape/Test.lean). Below, the frame is the test's own (`proximityTestKind`, `stagesFrom`,
Johnson/Desc/K12/Frame.lean), not the frame for an honest side: it puts the parts in order, cuts the
declared rounds among them, and asks two questions of the state: after the batching, whether the
group under test is the first stage's (`firstFits`); after a stage, where `p.early` is true, whether
the message that holds the next stage's mask has come (`maskCame`). The door is the front, the
batching, the first question and the first fold (TestDoor.lean in this folder). Of the parts, the
first stage has the first fold, the first switch and the batching after it. `FirstYes` says: these
three accept the term's rounds and groups of columns; the second question is true after them; four
numbers of the frame's cuts are as stated (`nF`, `oF`, `nS`, `oS` below). p: the place (`P12`,
Frame.lean: the numbers of a place at which a test is). `laidOf p`: its declared rounds with their
oracle messages; `laidS p`: those after "BAT" (Johnson/Desc/K12/Law/ReadsK.lean). The plan is the
place with these rounds. a, next, rest: the first stage, the second, the list of the others
(`Fmt.M1.Stage`). `⟨i.1, i.2, a.k, a.h⟩` (cu in `TermAsks`) and n: the first two stages as the
program names them (`IoppStage`: the two codes by their numbers, k and h). dS, dC: the first
switch's two declared rounds. t₀: the state before the test. dB: what "BAT" sampled. The stages'
term is `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean): the rounds, the trees and the groups of
opened columns of the stages, as one Lean term. Of it this file names the first fold's rounds
(`rfAt`), the first switch's two rounds (`rsAt`), the states after the fold, after the switch and
after the batching that follows (`t1At`, `aRec2`, `t3At`; these five: FirstYes.lean), and the groups
of columns for the switch's openings (`aGroups`, Stages.lean). The term's parameters: D, the sampled
challenges by the round's number; o, the number of the first fold's first round; P, the prover's
state (`PS`, Johnson/Prover/Link/BodyState.lean); K, further values that it reads (`BCoins`,
Johnson/Prover/Link/BodyAll.lean); a list of trees (`Tree`: a depth and a column function). Dp: the
library's plain data on the group (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean); `Dp.ts` lists the
trees of the group's members and of the fresh table. `c u x`: the column of tree u at position x, as
words. The main theorems' list of trees is `groupTrees Dp.ts (logAt Dp.book) c`
(Johnson/Desc/K12/Honest/GroupState.lean). The fresh table is the oracle message that holds the
first stage's mask: the field `mask` of t₀ is `some id` where it has come earlier, and `none` where
the first fold sends its own.

  `first_of_shape`: in the case `t₀.mask = some id`, under the hypotheses below: the front accepts
    at t₀ and returns t₀; the batching accepts at t₀ and at the round `⟨[], dB⟩` without its digest
    (`noDigest`), and returns `tBat p t₀ dB`; the first question is true at that state; that state
    passes a claim; and `FirstYes` holds at stage number 0, the rounds `laidS p`, that state and the
    list of trees above
  `first_of_shape_own`: the same in the case `t₀.mask = none`, with `foldCutOwn` for `foldCut`
  `TermAsks`: a structure of propositions: the hypotheses of these two theorems next to the door's
    tests and `SwitchPub`, at a state tB after the batching; field by field under "Hypotheses"
  `firstYes_of_done`: `FirstYes` at stage number 0, at any declared rounds l, state tB and list of
    trees, from: the first fold accepts the term's rounds; `SwitchDone` (TestSwitch.lean: what
    `switch_any` concludes) holds at the term's own two rounds and groups of columns; four numbers
    of the frame's cuts
  `readsAny_term`: under `TermAsks`, where tB passes a claim, and the first fold accepts the term's
    rounds and returns a state t₁ that passes single rows: `ReadsAny` (TestSwitch.lean) holds at t₁,
    these rows and the term's groups of columns, at every n and last, and at every round rC that
    sampled the term's positions. Its function on the book is `bump · Dp.ts`
    (Johnson/Desc/K12/Honest/ReadTrees.lean): one list more is counted at each tree of `Dp.ts`
  `tBat p t₀ dB`: a definition: the state after the batching, as a term in t₀ and dB: what the
    batching's `decide` returns at t₀ and at one round with no item that sampled dB; t₀ itself where
    the batching rejects

By what. `first_of_shape` calls `door_of_shape` (TestDoor.lean) for the front, the batching, the
first question and the first fold, and `first_stage_of_shape` (TestSwitch.lean) for `SwitchDone`.
The hypothesis `ReadsAny` of the latter comes from `readsAny_term`, which calls `read_first_any`
(ReadFirst.lean). `firstYes_of_done` then gives `FirstYes`. `first_of_shape_own` does the same with
`door_of_shape_own` and `first_stage_of_shape_own`. `getD_of_ok` (Johnson/Prover/Link/BodyYes.lean)
turns each acceptance into the value of the term's state: `tBat`, `t1At`, `aRec2`, `t3At`.

Hypotheses of `first_of_shape` and `first_of_shape_own`.
- h: the door's Bool on the shape: `doorB` (TestDoor.lean) is true at the shape of t₀. hm: the case.
- ht: the mark "tidy": `stTidyB t₀.st` (Johnson/Desc/Ground/Shape/Marks.lean). hv: the front's test
  on the open rows: `claimsB t₀` (TestDoor.lean). These two read the state itself, not its shape.
- hpl: the rows that the test takes in (`runRows`, OnBytes/Slice/BlkBegin.lean) are plain
  (`PlainRow`, OnBytes/Slice/BlkPlain.lean): none has a written-out factor.
- Pl: `SwitchPub` (TestSwitch.lean) at the first switch and at the codes of t₀.
- hB, hF: the tests on the plan's cuts: `batCut` (Johnson/Prover/Link/FormBat.lean) at the first
  declared round of `laidOf p`; `foldCut a.k` (Johnson/Prover/Link/FormFold.lean) or
  `foldCutOwn a.k` (Johnson/Desc/K12/Honest/OwnFold.lean) at the first 1 + a.k rounds of `laidS p`.
- fB: what "BAT" sampled has the declared form (`roundsFit`, Johnson/Desc/Block.lean).
- A: `TermAsks` at tB := `tBat p t₀ dB`. Its fields: `plain`: at whatever claim tB passes, the
  library's plain data (`gpOf`) is Dp, and Dp passes the library's test (`gpL`; both: FirstOk.lean).
  `hk`: a.h ≤ a.k. `stage`: cu is the first stage as the program names it (`stageAt p 0 a`,
  Join.lean). `width`: at each tree u of `Dp.ts` and each position x below 2 ^ `logAt Dp.book u`,
  `c u x` has `widthAt Dp.book u` words. `range`: the positions that the switch's second round
  sampled are below 2 ^ a.C.a. `cut`: the two declared rounds after the fold's are dS and dC.
  `fitF`, `fitS`: the term's rounds of the fold and of the switch have the declared form. `pub`:
  `readPubB` (ReadShape.lean in this folder) is true at the shapes of the state after the fold
  (`t1At`) and of whatever single rows that state passes. `nF`, `oF`, `nS`, `oS`: the four numbers
  of the frame's cuts: the fold's block (`foldAt`, Johnson/Desc/K12/FrameLaws.lean) has 1 + (h + g)
  rounds, h and g being those of `sgOf a`, and no opening; the switch's block (`switchAt`, same
  file) has 2 rounds and as many openings as `Dp.ts` has trees.

Limits.
- Every clause named under "Hypotheses" is a hypothesis: none is proved here, of any place.
- These are theorems on form: a fold and a switch lay claims and test none.
- The prover's state P and the columns c are universally quantified, but by type P is not free: the
  fields `fitF` and `fitS` of `TermAsks` read the term's rounds, and so P (and K), though
  `roundsFit` tests only the sort of a sent item; `pub` reads the state after the first fold, which
  is computed from these rounds, and nothing here says that its shape is a function of the shape
  before the fold. So it is not stated here that the door and the first stage accept whatever the
  prover's state holds. On c the only hypothesis is `width`.
- t₀ is a parameter of type `T12` under the hypotheses above: it is not shown to be the verifier's
  state in a run.
- dB and o are free parameters: no hypothesis ties dB to D, or o to the number of a round of the
  place.
- `SwitchPub` is a proposition; a test with code that gives it: `switchPubB` (TestSwitchPub.lean in
  this folder). `TermAsks` is a structure of propositions; a test with code that gives it where tB
  passes a claim at which `gpOf` returns Dp: `termB` (Johnson/Desc/ProofFile/Honest/K12/AllB.lean).
- Two clauses could be derived and are hypotheses: the positions' range, `range` (from the form of
  the switch's rounds, `fitS`, with `SwitchPub`), and h ≤ k, `hk` (from `SwitchPub`). Neither
  derivation is stated in Lean here.
- Rows with a written-out factor are not covered: where the test takes in such a row, hpl fails.
- Where the hypotheses hold together: see ToyAll.lean and ToyCame.lean in
  Johnson/Desc/ProofFile/Honest/K12/, each at a small made-up place, through the test `allB`
  (AllB.lean there). Their theorems are of the case where the fresh table has come earlier; of the
  other case ToyAll.lean has an evaluation by #guard, which leaves no theorem.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestSwitch
import Johnson.Desc.K12.Honest.Shape.ReadFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.K12

/-- The state after the batching: what the batching's `decide` returns at the state t₀ and at one
round with no item that sampled dB; t₀ itself where the batching rejects. -/
def tBat (p : P12) (t₀ : T12) (dB : Fmt.Drawn) : T12 :=
  ((guardedProximityTestParts.bat p (((laidOf p).take 1).map (·.1))).decide t₀ [noDigest ⟨[], dB⟩] []).toOption.getD
    t₀

/-- `FirstYes` from the first fold's acceptance (hf1), from what `switch_any` concludes at the
term's own two rounds and groups of columns (`SwitchDone`: hS, with hcut and hrs), and from the four
numbers of the frame's cuts (nF, oF, nS, oS). -/
theorem firstYes_of_done (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (tB : T12) (P : PS) (trees : List ProofFile.Honest.K12.Tree) (D : ℕ → Fmt.Drawn)
    (t₁ : T12)
    (hf1 : (guardedProximityTestParts.fold p 0 a ((l.take (1 + a.k)).map (·.1))).decide tB
      ((rfAt K 0 a o tB P D).map noDigest) [] = .ok t₁)
    (n : IoppStage) (dS dC : Fmt.DeclaredRound)
    (hcut : ((l.drop (1 + a.k)).take 2).map (·.1) = [dS, dC])
    (rows : SingleRows) (gp : ℕ) (rS rC : Fmt.RoundView) (ans : Fmt.Ext) (bk : TreeBook → TreeBook)
    (hrs : (rsAt p K rest 0 a next l o tB P D).map noDigest = [rS, rC])
    (hS : SwitchDone p 0 a next rest.isEmpty n dS dC t₁ rows gp rS rC ans (aGroups a o trees D) bk)
    (nF : (foldAt guardedProximityTestParts p 0 a l : Block T12 Unit).rounds.length =
      1 + ((sgOf a).h + (sgOf a).g))
    (oF : (foldAt guardedProximityTestParts p 0 a l : Block T12 Unit).openings = 0)
    (nS : (switchAt guardedProximityTestParts p 0 a next rest.isEmpty l : Block T12 Unit).rounds.length = 2)
    (oS : (switchAt guardedProximityTestParts p 0 a next rest.isEmpty l : Block T12 Unit).openings = trees.length) :
    FirstYes p K rest 0 a next l o tB P trees D := by
  have e1 : t1At p K 0 a l o tB P D = t₁ := getD_of_ok hf1
  obtain ⟨Dk, x, row', B, lay, -, -, h2, h3, -, hcame, -⟩ := hS
  have h2' : (guardedProximityTestParts.switch p 0 a next rest.isEmpty
      (((l.drop (1 + a.k)).take 2).map (·.1))).decide (t1At p K 0 a l o tB P D)
      ((rsAt p K rest 0 a next l o tB P D).map noDigest) (aGroups a o trees D) =
      .ok (switchT p n rest.isEmpty t₁ rC gp Dk B (E.ofTriple x)) := by
    rw [hrs, hcut, e1]
    exact h2
  have e2 : aRec2 p K rest 0 a next l o tB P trees D =
      switchT p n rest.isEmpty t₁ rC gp Dk B (E.ofTriple x) := getD_of_ok h2'
  have h3' : (guardedProximityTestParts.batBehind p (0 + 1) next (((l.drop (1 + a.k)).take 2).map (·.1))).decide
      (aRec2 p K rest 0 a next l o tB P trees D) [] [] =
      .ok (behindT p n rest.isEmpty t₁ rC gp Dk B row' lay) := by
    rw [e2, hcut]
    exact h3
  have e3 : t3At p K rest 0 a next l o tB P trees D =
      behindT p n rest.isEmpty t₁ rC gp Dk B row' lay := getD_of_ok h3'
  refine ⟨⟨t₁, hf1⟩, ⟨_, h2'⟩, ⟨_, h3'⟩, ?_, nF, oF, nS, oS⟩
  rw [e3]
  exact hcame

/-- The hypotheses of `first_of_shape` and `first_of_shape_own` next to the door's tests and
`SwitchPub`. tB: the state after the batching. -/
structure TermAsks (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage) (o : ℕ)
    (tB : T12) (P : PS) (D : ℕ → Fmt.Drawn) (Dp : Plain) (c : ℕ → ℕ → List UInt64)
    (cu : IoppStage) (dS dC : Fmt.DeclaredRound) : Prop where
  plain : ∀ row L, tB.pass = .claim row L →
    gpOf p tB a L = some Dp ∧ ok (gpL p a row Dp) = true
  hk : a.h ≤ a.k
  stage : stageAt p 0 a = some cu
  width : ∀ u ∈ Dp.ts, ∀ x, x < 2 ^ logAt Dp.book u → (c u x).length = widthAt Dp.book u
  range : ∀ x ∈ (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a
  cut : (((laidS p).drop (1 + a.k)).take 2).map (·.1) = [dS, dC]
  fitF : roundsFit (((laidS p).take (1 + a.k)).map (·.1)) (rfAt K 0 a o tB P D) = true
  fitS : roundsFit [dS, dC] ((rsAt p K rest 0 a next (laidS p) o tB P D).map noDigest) = true
  pub : ∀ rows gp, (t1At p K 0 a (laidS p) o tB P D).pass = .single rows gp →
    readPubB (coreSh ⟨(t1At p K 0 a (laidS p) o tB P D).st, (t1At p K 0 a (laidS p) o tB P D).book,
      (t1At p K 0 a (laidS p) o tB P D).roots⟩) (singleSh rows) a.C.a = true
  nF : (foldAt guardedProximityTestParts p 0 a (laidS p) : Block T12 Unit).rounds.length =
    1 + ((sgOf a).h + (sgOf a).g)
  oF : (foldAt guardedProximityTestParts p 0 a (laidS p) : Block T12 Unit).openings = 0
  nS : (switchAt guardedProximityTestParts p 0 a next rest.isEmpty (laidS p) : Block T12 Unit).rounds.length = 2
  oS : (switchAt guardedProximityTestParts p 0 a next rest.isEmpty (laidS p) : Block T12 Unit).openings =
    Dp.ts.length

/-- Under `TermAsks` the reading accepts at every value of `Taken`
(Johnson/Desc/K12/Law/SwDid.lean): `ReadsAny`, the form in which `first_stage_of_shape` and
`first_stage_of_shape_own` have it as a hypothesis. -/
theorem readsAny_term (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (tB : T12) (P : PS) (D : ℕ → Fmt.Drawn) (Dp : Plain) (c : ℕ → ℕ → List UInt64)
    (cu : IoppStage) (dS dC : Fmt.DeclaredRound) (A : TermAsks p K rest a next o tB P D Dp c cu dS dC)
    (row : GroupRow) (L : GroupLayout) (hp : tB.pass = .claim row L) (t₁ : T12)
    (hf1 : (guardedProximityTestParts.fold p 0 a (((laidS p).take (1 + a.k)).map (·.1))).decide tB
      ((rfAt K 0 a o tB P D).map noDigest) [] = .ok t₁)
    (rows : SingleRows) (gp : ℕ) (hp1 : t₁.pass = .single rows gp) (n : IoppStage) (last : Bool)
    (rC : Fmt.RoundView) (hposs : rC.drawn.poss = (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss) :
    ReadsAny p a last n dS dC t₁ rows gp rC (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D)
      (bump · Dp.ts) := by
  have e1 : t1At p K 0 a (laidS p) o tB P D = t₁ := getD_of_ok hf1
  obtain ⟨hD, hok⟩ := A.plain row L hp
  obtain ⟨rows', gp', hp', hall⟩ := read_first_any p K a o tB P D row L hp Dp hD hok A.hk cu A.stage
    c A.width t₁ hf1 A.range dS dC A.cut (by
      have k := A.pub
      rw [e1] at k
      exact k)
  rw [hp1] at hp'
  injection hp' with r1 _
  subst r1
  intro Dk
  exact hall n last rC gp Dk hposs

/-- **The door and the first stage at the term, where the fresh table has come earlier.** -/
theorem first_of_shape (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (t₀ : T12) (P : PS) (D : ℕ → Fmt.Drawn) (dB : Fmt.Drawn) (Dp : Plain)
    (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (id : ℕ) (dS dC : Fmt.DeclaredRound)
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i (n.code, n.maskCode) (testSh t₀) = true)
    (hm : t₀.mask = some id) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, PlainRow r)
    (hv : claimsB t₀ = true)
    (Pl : SwitchPub p t₀.st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (hF : foldCut a.k (((laidS p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true)
    (A : TermAsks p K rest a next o (tBat p t₀ dB) P D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC) :
    (guardedProximityTestParts.front p).decide t₀ [] [] = .ok t₀ ∧
      (guardedProximityTestParts.bat p (((laidOf p).take 1).map (·.1))).decide t₀ [noDigest ⟨[], dB⟩] [] =
        .ok (tBat p t₀ dB) ∧
      (guardedProximityTestParts.group (tBat p t₀ dB)).any (firstFits a) = true ∧
      (∃ row L, (tBat p t₀ dB).pass = .claim row L) ∧
      FirstYes p K rest 0 a next (laidS p) o (tBat p t₀ dB) P
        (groupTrees Dp.ts (logAt Dp.book) c) D := by
  obtain ⟨G, row, hG, hr, d1, d2, d3, d4⟩ := door_of_shape h hm ht hpl hv hB hF [⟨[], dB⟩]
    (rfAt K 0 a o (tBat p t₀ dB) P D) fB A.fitF
  have eB : tBat p t₀ dB = batT t₀ G row := getD_of_ok d2
  obtain ⟨G', row', hG', hr', -, -, -, -, hS⟩ := first_stage_of_shape (last := rest.isEmpty) h hm ht
    hpl hv Pl hB hF [⟨[], dB⟩] (rfAt K 0 a o (tBat p t₀ dB) P D) fB A.fitF
    (noDigest ⟨[], D (o + 1 + ((sgOf a).h + (sgOf a).g))⟩)
    (noDigest ⟨[.answer (ofE (aAns p 0 a next o D (t1At p K 0 a (laidS p) o (tBat p t₀ dB) P D)
      (qAt K rest 0 a next o P D)))], D (o + 2 + ((sgOf a).h + (sgOf a).g))⟩)
    A.fitS _ rfl (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D) (bump · Dp.ts)
    fun G₂ row₂ hG₂ hr₂ => by
      obtain rfl : G = G₂ := Option.some.inj (hG.symm.trans hG₂)
      obtain rfl : row = row₂ := Option.some.inj (hr.symm.trans hr₂)
      exact readsAny_term p K rest a next o (tBat p t₀ dB) P D Dp c _ dS dC A row _
        (by rw [eB]; rfl) _ (by rw [eB] at d4 ⊢; exact d4) _ _ rfl n rest.isEmpty _ rfl
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  obtain rfl : row = row' := Option.some.inj (hr.symm.trans hr')
  refine ⟨d1, by rw [eB]; exact d2, by rw [eB]; exact d3, ⟨row, _, by rw [eB]; rfl⟩, ?_⟩
  exact firstYes_of_done p K rest a next (laidS p) o (tBat p t₀ dB) P _ D _
    (by rw [eB] at d4 ⊢; exact d4) n dS dC A.cut _ _ _ _ _ _ rfl hS A.nF A.oF A.nS
    (by rw [A.oS]; simp [groupTrees])

/-- **The door and the first stage at the term, where the first fold sends its own fresh table.** -/
theorem first_of_shape_own (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage)
    (a next : Fmt.M1.Stage) (o : ℕ) (t₀ : T12) (P : PS) (D : ℕ → Fmt.Drawn) (dB : Fmt.Drawn)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (dS dC : Fmt.DeclaredRound)
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i (n.code, n.maskCode) (testSh t₀) = true)
    (hm : t₀.mask = none) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, PlainRow r)
    (hv : claimsB t₀ = true)
    (Pl : SwitchPub p t₀.st.codes 0 a next rest.isEmpty ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (hF : foldCutOwn a.k (((laidS p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true)
    (A : TermAsks p K rest a next o (tBat p t₀ dB) P D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC) :
    (guardedProximityTestParts.front p).decide t₀ [] [] = .ok t₀ ∧
      (guardedProximityTestParts.bat p (((laidOf p).take 1).map (·.1))).decide t₀ [noDigest ⟨[], dB⟩] [] =
        .ok (tBat p t₀ dB) ∧
      (guardedProximityTestParts.group (tBat p t₀ dB)).any (firstFits a) = true ∧
      (∃ row L, (tBat p t₀ dB).pass = .claim row L) ∧
      FirstYes p K rest 0 a next (laidS p) o (tBat p t₀ dB) P
        (groupTrees Dp.ts (logAt Dp.book) c) D := by
  obtain ⟨G, row, hG, hr, d1, d2, d3, d4⟩ := door_of_shape_own h hm ht hpl hv hB hF [⟨[], dB⟩]
    (rfAt K 0 a o (tBat p t₀ dB) P D) fB A.fitF
  have eB : tBat p t₀ dB = batT t₀ G row := getD_of_ok d2
  obtain ⟨G', row', hG', hr', -, -, -, -, hS⟩ := first_stage_of_shape_own (last := rest.isEmpty) h
    hm ht hpl hv Pl hB hF [⟨[], dB⟩] (rfAt K 0 a o (tBat p t₀ dB) P D) fB A.fitF
    (noDigest ⟨[], D (o + 1 + ((sgOf a).h + (sgOf a).g))⟩)
    (noDigest ⟨[.answer (ofE (aAns p 0 a next o D (t1At p K 0 a (laidS p) o (tBat p t₀ dB) P D)
      (qAt K rest 0 a next o P D)))], D (o + 2 + ((sgOf a).h + (sgOf a).g))⟩)
    A.fitS _ rfl (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D) (bump · Dp.ts)
    fun G₂ row₂ hG₂ hr₂ => by
      obtain rfl : G = G₂ := Option.some.inj (hG.symm.trans hG₂)
      obtain rfl : row = row₂ := Option.some.inj (hr.symm.trans hr₂)
      exact readsAny_term p K rest a next o (tBat p t₀ dB) P D Dp c _ dS dC A row _
        (by rw [eB]; rfl) _ (by rw [eB] at d4 ⊢; exact d4) _ _ rfl n rest.isEmpty _ rfl
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  obtain rfl : row = row' := Option.some.inj (hr.symm.trans hr')
  refine ⟨d1, by rw [eB]; exact d2, by rw [eB]; exact d3, ⟨row, _, by rw [eB]; rfl⟩, ?_⟩
  exact firstYes_of_done p K rest a next (laidS p) o (tBat p t₀ dB) P _ D _
    (by rw [eB] at d4 ⊢; exact d4) n dS dC A.cut _ _ _ _ _ _ rfl hS A.nF A.oF A.nS
    (by rw [A.oS]; simp [groupTrees])

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.firstYes_of_done
#print axioms ProofFile.Honest.Sh.readsAny_term
#print axioms ProofFile.Honest.Sh.first_of_shape
#print axioms ProofFile.Honest.Sh.first_of_shape_own
#print axioms ProofFile.Honest.Sh.tBat
#print axioms ProofFile.Honest.Sh.TermAsks
