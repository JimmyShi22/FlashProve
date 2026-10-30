-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunBy.lean: `runBy` computes all that a prover shows in a
proximity test (`KindName.K12`): the rounds, the trees, and the opened columns tree by tree. Field
elements are triples of 64-bit words. Definitions only. It imports Run.lean alone, so no Mathlib.

It computes again what the reference definition `testAll` (Test.lean, with `stagesAll`,
Johnson/Desc/K12/Honest/Stages.lean) defines over the field. `runBy_eq` (RunByEq.lean) proves that
both give the same rounds, trees and columns wherever the stages pass `StagesOk`. `stagesAll` in
turn equals `bodyAll` (Johnson/Prover/Link/BodyAll.lean) where each stage fits the next (`FitAll`)
and one tree holds the rows (`stages_eq`, Stages.lean). To that extent this file re-implements a
definition of Johnson/Prover/Link/ of what a prover shows, over imports without Mathlib, so that it
can run as code. No statement of this library derives `FitAll` from `StagesOk`, and none joins the
two equations. Near the join, from the second stage on: `restText_body` (Sim/TreesText.lean).

  `pow2B`, `switchFitB`, `okFrom`, `StagesOk`   the hypothesis of `runBy_eq` on the list of stages
  `RunOut`        the result: rounds, trees, opened columns, and warnings
  `keep`, `rowAt`, `noClaim`, `orOneW`, `headE`   helpers (`Tree` and `denseAt`: Run.lean)
  `stagesBy`     the result for one stage and all later stages
  `sized`, `firstSized`   the first stage's lists have the sizes that the stage states
  `runBy`        the result for the whole test

By what. As in `testAll`, the verifier's state is advanced by the `decide` functions of `guardedProximityTestParts`
(Johnson/Desc/K12/JoinGuarded.lean); where one rejects, the old state is kept. A sampled factor that is 0
modulo the prime counts as 1. The arithmetic is done by the five functions of `Seams` (Run.lean)
and, outside them, by functions of Fmt/ on words. One call outside `Seams` is of another kind: the
last stage's claim is written out by `claimAt` (JoinGuarded.lean), a function of the verifier's side. At
every earlier stage the claim's row is written out by the field `dense` of `Seams`, whose two values
(`denseAt`, Run.lean; `denseAtFast`, FastDense.lean) also call or repeat the verifier's side.
`rowAt`, `orOneW` and `headE` repeat `rowOf`, `orOne` and `drawnE`, whose files import Mathlib; each
is proved to agree with its original (`rowAt_eq`, RunBySpec.lean; `toE_orOneW`, RunByAns.lean;
`toE_headE`, RunByFold.lean). `stagesBy` also follows `Fmt.M1.Own.go` (Fmt/M1Own.lean) closely; no
theorem relates the two.

Limits.
- `runBy` never fails: from unusable input it still computes rounds, trees and columns. Missing
  challenges, rows and codes count as 0, empty or default, mostly without a warning.
- The warnings (`RunOut.no`) are a debugging aid. No theorem says what a warning, or none, means.
  Equations between whole results hold them too: `runBy_fast` (FastWLaw.lean), `runJob_in`
  (RunJobLaw.lean). An empty list does not mean that the verifier accepts: `guardedProximityTestParts.base` and the
  `planOk` checks are never called. Under `StagesOk`, at the inputs `RunIn.ofTest` and
  `RunIn.ofRun`, the rounds, trees and columns are `testAll`'s whether or not there are warnings; at
  another `RunIn` no theorem ties them to `testAll`.
- Where `StagesOk` fails, the last stage's masking word can be shorter than what it masks, and the
  rest is sent unmasked, with a warning (see `stagesBy`). `testAll` has no such case. So `runBy` is
  not for a prover's side as it stands: use `lightHalf` or `lightHalfOf` (PartsBy.lean,
  PartsByJob.lean), which call it under `StagesOk` alone.
- A `RunIn` is all on words, but its two makers are not: `RunIn.ofTest` and `RunIn.ofRun` take the
  random values as field elements, and the verifier's state on entry is the caller's function
  (RunOf.lean, RunJob.lean).
- `stagesBy` shows one answer at each switch, whatever the parameters' field `answers` says, as
  `stagesAll` does (see the limits of Johnson/Desc/K12/Honest/Stages.lean). `StagesOk` does not read
  that field.
- Cost is not measured. For faster `Seams` see FastW.lean.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Stage dot cp)
open Fmt.M1.Own (PSt lhs axL syms words)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.K12 (P12 T12 Laid guardedProximityTestParts stageAt claimAt)

/-! ## 1 The test on the list of stages -/

/-- A power of two. -/
def pow2B (n : Nat) : Bool := n == 2 ^ Fmt.M1.lg n

/-- The five clauses of `CsFit` (OnBytes/Slice/CsData.lean) for a stage s and the next stage n, as a
Bool. The first has k here and h + (k - h) there, which is the same number where h ≤ k. No theorem
relates this definition to `H2K.Pub.csFitB` (Johnson/Desc/K12/Law/PubOk.lean), a Bool with the same
clauses. -/
def switchFitB (s n : Stage) : Bool :=
  2 ^ n.k * n.C.l == s.C.l && decide (2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ 2 ^ n.h * n.Z.l) &&
    pow2B n.C.l && pow2B n.Z.l && decide (s.Z.a ≤ s.C.a)

/-- The clauses of `StagesOk` for a stage and the stages after it. A stage that is not the last: h ≤
k, room in the fresh table for the hiding polynomial's coefficients (2 k + 1 ≤ h + Z.l), and
`switchFitB` with the next stage. The last stage: k = 0 and h = 0. -/
def okFrom : Stage → List Stage → Bool
  | s, [] => s.k == 0 && s.h == 0
  | s, n :: rest =>
    decide (s.h ≤ s.k) && decide (2 * s.k + 1 ≤ s.h + s.Z.l) && switchFitB s n && okFrom n rest

/-- **The hypothesis of `runBy_eq`** (RunByEq.lean): at least two stages, and `okFrom`. -/
def StagesOk : List Stage → Bool
  | s :: n :: rest => okFrom s (n :: rest)
  | _ => false

/-! ## 2 Helpers -/

/-- **The result.** rs: the rounds. tr: for each round the column function of the tree that it sends
(the function that returns the empty list where it sends none). gs: the opened columns, tree by
tree. no: warnings (see the head's limits). -/
structure RunOut where
  rs : List Fmt.RoundView
  tr : List (Nat → List UInt64)
  gs : List (List (Nat × List UInt64))
  no : List String

/-- The state that a `decide` function returns; where it rejects: the old state and its message. -/
def keep (t : T12) : Except String T12 → T12 × List String
  | .ok t' => (t', [])
  | .error e => (t, [e])

/-- The row of the claim that a state holds; the empty row where it holds none. -/
def rowAt (t : T12) : OnBytes.GroupRow :=
  match t.pass with
  | .claim row _ => row
  | _ => {}

/-- A warning where a state holds no claim, so that `rowAt` gives the empty row. j: the stage. -/
def noClaim (j : Nat) (t : T12) : List String :=
  match t.pass with
  | .claim _ _ => []
  | _ => [s!"stage {j}: the verifier's state holds no claim; an empty row is used"]

/-- b, or 1 where b is 0 modulo the prime. -/
def orOneW (b : E) : E := if Fld.two.addE b Fld.zeroE = Fld.zeroE then Fld.oneE else b

/-- The first element that a round sampled; three words 0 where it sampled none. -/
def headE (d : Fmt.Drawn) : E := d.elems.headD (0, 0, 0)

/-! ## 3 The run -/

/-- **The result for one stage and all later stages.** S: the five replaceable functions (`Seams`,
Run.lean). p: the test's parameters. K: the random values. The list: the later stages. j: the
stage's number, from 0. cur: the stage. l: the declared rounds from the stage's first on. o: the
number of that round. t: the verifier's state. P: the stage's rows and tails. trees: the trees that
hold them. D: the sampled challenges, by the round's number in the test. At the last stage `axL`
fills the shorter list with 0. Under `StagesOk` the masking word's four lists are as long as what
they mask (`Tab` at last := true, `nextBy_tab`, RunByNext.lean). Where `StagesOk` fails they can be
shorter, and the rest of a row is then sent unmasked, with a warning: `testAll` has no such case. -/
def stagesBy (S : Seams) (p : P12) (K : Sorted) : List Stage → Nat → Stage → Laid → Nat → T12 →
    PSt → List Tree → (Nat → Fmt.Drawn) → RunOut
  | [], j, cur, _, o, t, P, trees, D =>
    let f : Fld := .two
    let cl? := (stageAt p j cur).bind fun c => claimAt t.st.codes c (rowAt t)
    let cl := cl?.getD ⟨#[], #[], (0, 0, 0)⟩
    let Ms0 := P.P.getD 0 []
    let Ms1 := P.P.getD 1 []
    let lam := headE (D o)
    ⟨[⟨[.e (f.addE (dot f cl.c Ms0.toArray) (dot f cl.d Ms1.toArray))], D o⟩,
        ⟨(axL f Ms0 lam (P.M.getD 0 []) ++ axL f Ms1 lam (P.W.getD 0 []) ++
          axL f (P.Pi.getD 0 []) lam (P.Rh.getD 0 []) ++
          axL f (P.Pi.getD 1 []) lam (P.Sg.getD 0 [])).map .e, D (o + 1)⟩],
      [fun _ => [], fun _ => []], trees.map fun x => groupOf x (D (o + 1)).poss,
      noClaim j t ++
        (if cl?.isSome then []
          else ["the last stage: the claim cannot be written out (claimAt returns none)"]) ++
        if Ms0.length < (P.M.getD 0 []).length || Ms1.length < (P.W.getD 0 []).length ||
            (P.Pi.getD 0 []).length < (P.Rh.getD 0 []).length ||
            (P.Pi.getD 1 []).length < (P.Sg.getD 0 []).length then
          ["the last stage: a list of the masking word is shorter than what it masks; " ++
            "the rest is sent unmasked"]
        else []⟩
  | next :: rest, j, cur, l, o, t, P, trees, D =>
    let f : Fld := .two
    let g := (List.range cur.k).map fun n => headE (D (o + 1 + n))
    let T : Fmt.M1.FoldOwn.Trial :=
      { k := cur.k, h := cur.h, G := S.dense (rowAt t) cur, m := S.tab P.M cur.C.l,
        mu := S.tab P.W cur.Z.l, U := hideBy K (j + 1), eps := headE (D o), g := g, lzk := cur.Z.l }
    let rf : List Fmt.RoundView := ⟨[.e (T.sigma f)], D o⟩ ::
      ((S.rounds f T g).map (·.1)).zipIdx.map fun q => ⟨[.e q.1.1, .e q.1.2], D (o + 1 + q.2)⟩
    let Q := nextBy S f K (j + 2) cur next rest.isEmpty g P
    let tree := S.tree next rest.isEmpty Q
    let col := tree.2
    let x₁ := keep t ((guardedProximityTestParts.fold p j cur ((l.take (1 + cur.k)).map (·.1))).decide t
      (rf.map noDigest) [])
    let t₁ := x₁.1
    let els := (D (o + 1 + cur.k)).elems
    let bits := (OnBytes.Send.cube t₁.st.codes
      (OnBytes.switchTargetStage ((stageAt p (j + 1) next).getD default).code
        ((stageAt p (j + 1) next).getD default).maskCode next.k next.h 1).shape).bits
    let z := (List.range next.na).map fun i => (els.take bits).getD i Fld.zeroE
    let beta := els.getD bits Fld.zeroE
    let a := lhs f (Fmt.M1.sampleRow f next.Am next.Az z (orOneW beta) Fld.zeroE)
      (S.tab Q.M next.C.l) (S.tab Q.W next.Z.l)
    let rs : List Fmt.RoundView := [⟨[], D (o + 1 + cur.k)⟩, ⟨[.answer a], D (o + 2 + cur.k)⟩]
    let gs := trees.map fun x => groupOf x (D (o + 2 + cur.k)).poss
    let cutS := ((l.drop (1 + cur.k)).take 2).map (·.1)
    let x₂ := keep t₁ ((guardedProximityTestParts.switch p j cur next rest.isEmpty cutS).decide t₁
      (rs.map noDigest) gs)
    let x₃ := keep x₂.1 ((guardedProximityTestParts.batBehind p (j + 1) next cutS).decide x₂.1 [] [])
    let R := stagesBy S p K rest (j + 1) next (l.drop (cur.k + 3)) (o + cur.k + 3) x₃.1 Q
      [tree] D
    ⟨rf ++ rs ++ R.rs, rf.map (fun _ _ => []) ++ [col, fun _ => []] ++ R.tr, gs ++ R.gs,
      noClaim j t ++ x₁.2 ++
        (if orOneW beta == beta then []
          else [s!"the switch after stage {j}: the sampled factor is 0 or missing"]) ++
        x₂.2 ++ x₃.2 ++ R.no⟩

/-- n lists of m entries each. -/
def sized (n m : Nat) (l : List (List E)) : Bool := l.length == n && l.all (·.length == m)

/-- The first stage's four lists have the sizes that the stage states: 2 ^ k main rows of C.l
entries with tails of C.r, 2 ^ h mask rows of Z.l entries with tails of Z.r. -/
def firstSized (s : Stage) (p : PSt) : Bool :=
  sized (2 ^ s.k) s.C.l p.M && sized (2 ^ s.k) s.C.r p.Rh && sized (2 ^ s.h) s.Z.l p.W &&
    sized (2 ^ s.h) s.Z.r p.Sg

/-- **The result for the whole test.** D: the sampled challenges, by the round's number in the test;
the batching round "BAT" is round 0. -/
def runBy (S : Seams) (I : RunIn) (D : Nat → Fmt.Drawn) : RunOut :=
  match I.p.nums.stages with
  | [] => ⟨[], [], [], ["the list of stages fails StagesOk"]⟩
  | s :: rest =>
    let laid := ((H2U.roundsOfNums I.p.nums).getD []).zip I.p.oracles
    let xF := keep I.door ((guardedProximityTestParts.front I.p).decide I.door [] [])
    let xB := keep xF.1 ((guardedProximityTestParts.bat I.p ((laid.take 1).map (·.1))).decide xF.1
      [noDigest ⟨[], D 0⟩] [])
    let rd := ridersBy .two I.coin 1 s rest.isEmpty
    let p₀ : PSt := { I.first with P := rd.1, Pi := rd.2 }
    let B := stagesBy S I.p I.coin rest 0 s (laid.drop 1) 1 xB.1 p₀ (I.trees p₀) D
    ⟨⟨[], D 0⟩ :: B.rs,
      (fun _ => []) ::
        (if I.own then B.tr.set 0 fun x => (syms s.Z (cp s.Z x) p₀.P p₀.Pi).flatMap words
        else B.tr),
      B.gs,
      (if StagesOk (s :: rest) then [] else ["the list of stages fails StagesOk"]) ++
        (if I.own == I.p.nums.ownMask then []
          else ["the input and the test's parameters disagree on whether the first fold sends " ++
            "its own fresh table"]) ++
        (if firstSized s I.first then []
          else ["the input's first-stage rows or tails do not have the sizes that the stage " ++
            "states"]) ++
        xF.2 ++ xB.2 ++ B.no⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.pow2B
#print axioms ProofFile.Honest.K12.Light.switchFitB
#print axioms ProofFile.Honest.K12.Light.okFrom
#print axioms ProofFile.Honest.K12.Light.StagesOk
#print axioms ProofFile.Honest.K12.Light.RunOut
#print axioms ProofFile.Honest.K12.Light.keep
#print axioms ProofFile.Honest.K12.Light.rowAt
#print axioms ProofFile.Honest.K12.Light.noClaim
#print axioms ProofFile.Honest.K12.Light.orOneW
#print axioms ProofFile.Honest.K12.Light.headE
#print axioms ProofFile.Honest.K12.Light.stagesBy
#print axioms ProofFile.Honest.K12.Light.sized
#print axioms ProofFile.Honest.K12.Light.firstSized
#print axioms ProofFile.Honest.K12.Light.runBy
