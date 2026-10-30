-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestSwitchPub.lean: what is public at a switch, as a test with code:
`switchPubB`, a Bool on the plan, the codes and the switch's two declared rounds, and the theorem
that it gives `SwitchPub` (Johnson/Desc/K12/Honest/Shape/TestSwitch.lean). With it, what the theorem
on the first stage of a proximity test (`first_stage_of_shape`, same file) asks of the shape, the
plan and the declared rounds is one Bool: `firstB`. (Its other premises stay as they are: the first
mark; that the rows taken in are plain, a sentence on all of them; the named test on the open rows;
the view's form; the reading's accept.) The same for `first_stage_of_shape_own`, the other case of
the first fold's mask. Definitions and theorems, general in the plan, the codes, the stages, the
declared rounds, the rounds of the view and the structure before the test.

Terms, as in the head of TestSwitch.lean. The plan is p (`P12`, Johnson/Desc/K12/Frame.lean: the
numbers of the place of the test). K (`Codes`, OnBytes/Iop/Ground.lean) holds the main codes
(`base`) and the mask codes (`mask`). A stage is given twice: as cur, nxt or next (`Fmt.M1.Stage`:
its numbers; `sgOf`, Johnson/Desc/K12/Law/ChainOf.lean, is the same in the library's form, with
`g := k - h`) and as c or n (`IoppStage`: its two codes by their numbers in K, with k and h). The
parts of a test are the front, the batching, in each stage but the last the fold, the switch and the
batching after it, and the base case. The frame is the test's own (`proximityTestKind`, `stagesFrom`, Frame.lean),
not the frame for an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean): it puts the parts in
order, cuts the declared rounds (`Fmt.DeclaredRound`) among them, and asks after the first batching
whether the group is the first stage's (`firstFits`). A part's cut is the list of declared rounds
that the frame cuts for it: cutB is for the batching's, cutF for the fold's, dS and dC for the
switch's two, the round of the seed and the round of the positions. t is the structure inside a test
(`T12`, Johnson/Desc/K12/Join.lean); its shape is `testSh t` (`TestSh`,
Johnson/Desc/K12/Honest/Shape/Test.lean). The door is the word of
Johnson/Desc/K12/Honest/Shape/TestDoor.lean for the front, the batching, that question and the first
fold. "In front of" means before, in the order of the parts; "premises" are hypotheses; a test
"is asked" where it is a clause of the Bool.

  `first_of_B`: `first_stage_of_shape` with four of its hypotheses, h (`doorB`), Pl (`SwitchPub`),
    hB (`batCut`) and hF (`foldCut`), replaced by one: `firstB` is true at the shape of t. It is the
    case `t.mask = some id`. The other hypotheses and the conclusion are the same, word for word.
    The conclusion: there are the group G under test and the row that the batching makes such that
    the front, the batching and the fold of stage number 0 return `.ok`, each with the next
    structure written out; the frame's question is true after the batching; and `SwitchDone`
    (TestSwitch.lean) holds of the first switch and the batching after it
  `first_of_B_own`: the same for `first_stage_of_shape_own`: the case `t.mask = none`, with
    `foldCutOwn` for `foldCut`
  `firstB p cur nxt cutB cutF i n last dS dC a`: a definition: a Bool on the plan, the two stages,
    the declared rounds and a shape a. It is the conjunction of `doorB` (TestDoor.lean) at a, at i
    and at `(n.code, n.maskCode)`, the numbers of the first two stages' codes; `switchPubB` at the
    codes in a (`a.core.st.codes`), at `j := 0` and at `c := ⟨i.1, i.2, cur.k, cur.h⟩`;
    `batCut cutB` (Johnson/Prover/Link/FormBat.lean); and `foldCut cur.k cutF`
    (Johnson/Prover/Link/FormFold.lean) where `a.mask` is `some`, else `foldCutOwn cur.k cutF`
    (Johnson/Desc/K12/Honest/OwnFold.lean)
  `switchPub_of`: where `switchPubB` is true, `SwitchPub` holds at the same arguments
  `switchPubB p K j cur next last c n dS dC`: a definition: the conjunction of these clauses.
    `p.early`, and `p.answers = 1`. n has the code numbers that the plan names for stage number
    `j + 1` (`p.idx`), and k and h of next (`stageAt`, Join.lean). The two stages fit (`csFitB`).
    `(sgOf cur).C.a ≤ 32`. The codes of K at the numbers in c are the main code and the mask code of
    cur (`codeB`), and `c.k`, `c.h` are h + g and h of `sgOf cur`; the same for n and next.
    `K.lengthsOk`. Two bounds by `2 ^ 63` (see Limits). `switchCut`
    (Johnson/Prover/Link/FormSwitch.lean), a test on dS and dC. `dS.entry.drawE` is one more than
    the bits of the cube (`Send.cube`, OnBytes/Iop/Send.lean) of the switch's target (`swTarget`,
    FormSwitch.lean). `dC.entry.rows = 2 + 3 * dC.entry.poss`. `Own.treesCan`
    (Johnson/Desc/Own/Trees.lean) at `swNotices p n last` (FormSwitch.lean)

By what. `switchPub_of` splits the conjunction. `csFit_of_B` gives `CsFit` from `csFitB`, and
`code_of_B` gives the four equations on the codes from `codeB` (the two theorems: ChainOf.lean; the
two Bools: Johnson/Desc/K12/Law/PubOk.lean). Every other clause is a Bool that `SwitchPub` asks to
be true, or `decide` of a proposition that it asks. `first_of_B` and `first_of_B_own` split
`firstB`, rewrite the test on the fold's cut by hm, and call `first_stage_of_shape` or
`first_stage_of_shape_own` with `switchPub_of`.

Hypotheses of `first_of_B` and `first_of_B_own`. h: `firstB` is true at `testSh t`. hm: the case.
ht: the first mark, `stTidyB t.st` (Johnson/Desc/Ground/Shape/Marks.lean). hp: every row that the
test takes in (`runRows`) is plain (`PlainRow`). hv: the named test on the open rows, `claimsB t`
(TestDoor.lean). fB, fF, hfit, hans: the view's form: the rounds rsB, rsF and [rS, rC] are of the
declared form (`roundsFit`, Johnson/Desc/Block.lean), and `rC.vals = [.answer a]`. hread: the
reading's accept: `ReadsAny` (TestSwitch.lean) at the structure and the single rows after the first
fold, for the group under test and the row that the batching makes. It says that the switch's
reading of these rows returns `.ok` at every D (`Taken`, Johnson/Desc/K12/Law/SwDid.lean).

Limits.
- Sufficient, not necessary. Only one direction is proved: from `switchPubB` to `SwitchPub`, and
  from `firstB` with the other hypotheses to the conclusion.
- Many of the clauses of `switchPubB` are also in the block's own public test (`pubOk`, PubOk.lean),
  which `doorB` asks at the same codes (in `frontOwesB`, TestDoor.lean); no theorem here derives
  them from it.
- One clause is `Codes.lengthsOk` at the shape's own codes. `k12_tidy_mark`, in
  Johnson/Desc/K12/Honest/Shape/TestMarks.lean (not in the library yet), by which the first mark
  holds after a test that accepts if it holds before, has the same hypothesis.
- Two clauses compare with `2 ^ 63`: at `sgOf next`, `2 ^ (h + g) * C.l ≤ 2 ^ 63` and
  `2 ^ h * Z.l ≤ 2 ^ 63`.
- `switchPubB`, and so `firstB`, is false where `p.early` is false or `p.answers` is not 1.
- The parameters cur, nxt, cutB, cutF, i, n, last, dS and dC are free in the definitions and the
  theorems: the caller supplies the plan's own. That cutB, cutF, dS and dC are the declared rounds
  as the frame cuts them is not stated here.
- "Public" is a word of these comments, for the plan, the codes, the declared rounds and the shape.
  No statement in Lean here says that any of them is public.
- Nothing is evaluated here: that `firstB` is true at a place of a file is not shown here.
  Evaluations of `firstB` at small made-up examples, by #guard:
  Johnson/Desc/K12/Honest/Shape/TestSwitchToy.lean (not in the library yet).
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestSwitch
import Johnson.Desc.K12.Law.ChainOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw
open Johnson.Prover.Link
open H2K.Pub (sgOf csFitB codeB csFit_of_B code_of_B)

/-- What is public at a switch, as a test. Where it is true, `SwitchPub` holds at the same arguments
(`switchPub_of`). c, n: the two stages as the program names them. -/
def switchPubB (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool)
    (c n : IoppStage) (dS dC : Fmt.DeclaredRound) : Bool :=
  p.early && decide (p.answers = 1) && decide (stageAt p (j + 1) next = some n) &&
  csFitB cur next && decide ((sgOf cur).C.a ≤ 32) &&
  codeB K.base[c.code]? cur.C && codeB K.mask[c.maskCode]? cur.Z &&
  decide (c.k = (sgOf cur).h + (sgOf cur).g) && decide (c.h = (sgOf cur).h) &&
  codeB K.base[n.code]? next.C && codeB K.mask[n.maskCode]? next.Z &&
  decide (n.k = (sgOf next).h + (sgOf next).g) && decide (n.h = (sgOf next).h) &&
  K.lengthsOk &&
  decide (2 ^ ((sgOf next).h + (sgOf next).g) * (sgOf next).C.l ≤ 2 ^ 63) &&
  decide (2 ^ (sgOf next).h * (sgOf next).Z.l ≤ 2 ^ 63) &&
  switchCut (sgOf cur).C.a dS dC &&
  decide (dS.entry.drawE = (Send.cube K (swTarget p n).shape).bits + 1) &&
  decide (dC.entry.rows = 2 + 3 * dC.entry.poss) && Own.treesCan K (swNotices p n last)

theorem switchPub_of {p : P12} {K : Codes} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound}
    (h : switchPubB p K j cur next last c n dS dC = true) :
    SwitchPub p K j cur next last c n dS dC := by
  unfold switchPubB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩,
    a14⟩, a15⟩, a16⟩, a17⟩, a18⟩, a19⟩, a20⟩ := h
  have b6 := code_of_B a6
  have b7 := code_of_B a7
  have b10 := code_of_B a10
  have b11 := code_of_B a11
  exact
    { early := a1, one := a2, stageN := a3, fits := csFit_of_B a4, small := a5
      codes :=
        { base := ⟨_, b6, rfl⟩
          mask := by
            show codeOf (K.mask.getD c.maskCode default) = cur.Z
            rw [Array.getD_eq_getD_getElem?, b7]
            rfl
          k := a8, h := a9 }
      zk := by rw [b7]; rfl
      codeN := by rw [b10]; rfl
      zkN := by rw [b11]; rfl
      nk := a12, nh := a13, lengths := a14, bounds := ⟨a15, a16⟩, cutSw := a17, drawE := a18
      count := a19, trees := a20 }

/-- All that is public in front of a test's first stage, as one Bool: on the shape, the plan and the
declared rounds as the frame cuts them. Which test on the fold's cut is asked goes by the shape's
own field for the mask. In Lean: `foldCut` where `a.mask` is `some`, else `foldCutOwn`. The declared
rounds cutB, cutF, dS and dC, and last, are free parameters: no clause compares them with what the
frame cuts at p. -/
def firstB (p : P12) (cur nxt : Fmt.M1.Stage) (cutB cutF : List Fmt.DeclaredRound) (i : ℕ × ℕ)
    (n : IoppStage) (last : Bool) (dS dC : Fmt.DeclaredRound) (a : TestSh) : Bool :=
  doorB p cur nxt cutB i (n.code, n.maskCode) a &&
    switchPubB p a.core.st.codes 0 cur nxt last ⟨i.1, i.2, cur.k, cur.h⟩ n dS dC && batCut cutB &&
    (if a.mask.isSome then foldCut cur.k cutF else ProofFile.Honest.K12.foldCutOwn cur.k cutF)

open ProofFile.Honest.K12 (foldTOwn enteredT foldCutOwn)

/-- **The first stage, where the mask has come, with all that is public as one Bool.** It is
`first_stage_of_shape` with `firstB` in place of `doorB`, `SwitchPub`, `batCut` and `foldCut`. -/
theorem first_of_B {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i : ℕ × ℕ}
    {n : IoppStage} {id : ℕ} {cutB cutF : List Fmt.DeclaredRound} {last : Bool}
    {dS dC : Fmt.DeclaredRound} (h : firstB p cur nxt cutB cutF i n last dS dC (testSh t) = true)
    (hm : t.mask = some id) (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true)
    (rsB rsF : List Fmt.RoundView)
    (fB : roundsFit cutB rsB = true) (fF : roundsFit cutF rsF = true) (rS rC : Fmt.RoundView)
    (hfit : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook)
    (hread : ∀ G row, t.st.groups[t.g]? = some G →
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row →
      ReadsAny p cur last n dS dC
      (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) id (rsF.map noDigest))
      (foldOut (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ id
        (rsF.map noDigest))
      (batT t G row).st.groups.size rC gs bk) :
    ∃ G row,
      t.st.groups[t.g]? = some G ∧
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) id (rsF.map noDigest)) ∧
      SwitchDone p 0 cur nxt last n dS dC
        (foldT (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) id (rsF.map noDigest))
        (foldOut (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ id
          (rsF.map noDigest))
        (batT t G row).st.groups.size rS rC a gs bk := by
  unfold firstB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (if t.mask.isSome then foldCut cur.k cutF
    else ProofFile.Honest.K12.foldCutOwn cur.k cutF) = true := h4
  rw [hm] at h4'
  exact first_stage_of_shape h1 hm ht hp hv (switchPub_of h2) h3 h4' rsB rsF fB fF rS rC hfit a
    hans gs bk hread

/-- **The first stage, where the first fold receives its own mask, likewise.** It is
`first_stage_of_shape_own` with `firstB` in place of `doorB`, `SwitchPub`, `batCut` and
`foldCutOwn`. -/
theorem first_of_B_own {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {i : ℕ × ℕ}
    {n : IoppStage} {cutB cutF : List Fmt.DeclaredRound} {last : Bool} {dS dC : Fmt.DeclaredRound}
    (h : firstB p cur nxt cutB cutF i n last dS dC (testSh t) = true) (hm : t.mask = none)
    (ht : stTidyB t.st = true)
    (hp : ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, PlainRow r)
    (hv : claimsB t = true)
    (rsB rsF : List Fmt.RoundView)
    (fB : roundsFit cutB rsB = true) (fF : roundsFit cutF rsF = true) (rS rC : Fmt.RoundView)
    (hfit : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64))) (bk : TreeBook → TreeBook)
    (hread : ∀ G row, t.st.groups[t.g]? = some G →
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row →
      ReadsAny p cur last n dS dC
      (foldTOwn p (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
        (n.code, n.maskCode) (rsF.map noDigest))
      (foldOut (enteredT p (batT t G row)
          (ioppFoldShape ⟨i.1, i.2, cur.k, cur.h⟩ (Means.layoutOf t.st G))) row
        (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ (batT t G row).st.oracles.size
        (rsF.map noDigest))
      (batT t G row).st.groups.size rC gs bk) :
    ∃ G row,
      t.st.groups[t.g]? = some G ∧
      Bat.combine (begun t.st t.g G) t.g ⟨Means.layoutOf t.st G, runRows t.st G⟩
        (drawnOf ((rsB.map noDigest).headD ⟨[], ⟨[], [], [], none⟩⟩)) = some row ∧
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldTOwn p (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) (rsF.map noDigest)) ∧
      SwitchDone p 0 cur nxt last n dS dC
        (foldTOwn p (batT t G row) row (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩
          (n.code, n.maskCode) (rsF.map noDigest))
        (foldOut (enteredT p (batT t G row)
            (ioppFoldShape ⟨i.1, i.2, cur.k, cur.h⟩ (Means.layoutOf t.st G))) row
          (Means.layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ (batT t G row).st.oracles.size
          (rsF.map noDigest))
        (batT t G row).st.groups.size rS rC a gs bk := by
  unfold firstB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have h4' : (if t.mask.isSome then foldCut cur.k cutF
    else ProofFile.Honest.K12.foldCutOwn cur.k cutF) = true := h4
  rw [hm] at h4'
  exact first_stage_of_shape_own h1 hm ht hp hv (switchPub_of h2) h3 h4' rsB rsF fB fF rS rC hfit a
    hans gs bk hread

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.switchPub_of
#print axioms ProofFile.Honest.Sh.first_of_B
#print axioms ProofFile.Honest.Sh.first_of_B_own
#print axioms ProofFile.Honest.Sh.switchPubB
#print axioms ProofFile.Honest.Sh.firstB
