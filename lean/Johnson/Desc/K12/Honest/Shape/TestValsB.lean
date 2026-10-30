-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestValsB.lean: the hypothesis on the values of a proximity test's own
rounds and columns (`ValsFrom`, Johnson/Desc/K12/Honest/Shape/TestReturns.lean; `ValsAsk`,
TestReturnsOneIff.lean in that folder) as a test with code, that is, a function into `Bool`; and
that the test says yes just where the hypothesis holds, with no further hypothesis but, in
`valsK12_iff`, an equation that names the place's stages. So, under `OneAsks`
(TestReturnsOneIff.lean), the proximity test's block accepts if and only if the test with code says
yes. "The block" is `proximityTestKind` (Johnson/Desc/K12/Frame.lean) at the parts `guardedProximityTestParts`
(Johnson/Desc/K12/JoinGuarded.lean); "accepts" means that its decision returns `.ok`. General in the
place's parameters, the stages, the structure before the test, the rounds and the columns.

What the test with code is, said plainly. It runs the proximity test's own parts to make the claim:
the batching's combination, and stage by stage the decisions of the fold, the switch and the
batching after it. Its only test is the base case's own decision at the claim that these make. Where
an earlier part refuses it says yes, as the hypothesis is vacuous there: it asserts no accept of an
earlier part. Under `OneAsks` it is equivalent to the block's yes (`k12_accept_iff_B`): so it is no
closed form of the claim in the rounds' values, and it spares an honest side's algebra nothing:
whoever shows it on an honest run shows that the block accepts there. (An honest side is a `Side`,
Johnson/Desc/ProofFile/Honest/Side.lean; this file names none.)

In the list: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the parameters of the place of a test. A
stage is a `Fmt.M1.Stage`; cur is the present stage, number j. A part (`Part`, same file) is a piece
of the proximity test with a decision of its own: the front, the batching, at a stage that is not
the last the fold, the switch and the batching after the switch, at the last stage the base case. t
(`T12`, Johnson/Desc/K12/Join.lean) is the verifier's structure inside a test. l (`Laid`,
Frame.lean) lists the declared rounds from this stage on, each with its oracle messages. rB, R and
rs are rounds (`Fmt.RoundView`); gs are groups of columns, a column being a position with a list of words.
The claim is what `claimAt` (JoinGuarded.lean) writes out of the row that t passes on. `noDigest`
(Johnson/Desc/Block.lean) sets the field `drawn.digest` of a round to `none`.

  `k12_accept_iff_B`: under `OneAsks`: the block accepts ↔ `valsK12` says yes. `OneAsks` holds all
    hypotheses of `k12_returns_one` (TestReturnsOne.lean in this folder) but the one on the values
    of the test's own rounds and columns
  `valsFromB` (definition), `valsFromB_iff`: `ValsFrom`, from any stage on
  `valsAskB` (definition), `valsAskB_iff`: `ValsAsk`, at the rounds as a decision is shown them. In
    `valsAskB_iff` the function is taken at `noDigest rB` and `R.map noDigest`, and `ValsAsk` at rB
    and R
  `valsK12` (definition), `valsK12_iff`: the same with the stages read off the place and the rounds
    as one list. After p it takes the three arguments of a block's decision (`Block.decide`,
    Johnson/Desc/Block.lean): the structure, the rounds, the groups of columns

By what. `valsFromB_iff` goes by recursion on the list of stages and unfolds both definitions, arm
by arm; at the last stage `baseDecide_same` (TestReturns.lean) says that the claim which the base
case's decision returns is the claim that it was handed. `valsAskB_iff` unfolds both definitions and
calls `valsFromB_iff`; `valsK12_iff` unfolds `valsK12` and calls `valsAskB_iff`. `k12_accept_iff_B`
joins `k12_accept_iff_one` (TestReturnsOneIff.lean) and `valsK12_iff`.

Limits. All limits of TestReturnsOneIff.lean hold here. The three functions say yes by default.
`valsFromB`: where an earlier part refuses, where no claim is passed, where the stage has no name in
the program, and where the claim cannot be written out. `valsAskB`: where the group under test is
not there and where the batching's combination gives nothing. `valsK12` says yes at a place with
fewer than two stages and at no round: nothing is meant there. So a yes of one of them, taken by
itself, does not say that any part accepts. At the last stage `valsFromB` does not read its argument
l: a caller can pass anything there. No value that meets `OneAsks` is given in this file. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestReturnsOneIff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12
open VerifiableInference.Desc.Ground.Sh
open Johnson.Prover.Link
open H2K.JointK (laidOf laidS)

/-- `ValsFrom` (TestReturns.lean) with code, arm by arm. At the last stage: whether `baseDecide`
(Johnson/Desc/Prox/BaseCase.lean) returns `.ok` at the claim written out. Yes where an earlier part
refuses, where no claim is passed (`t.pass` is no `.claim`), where the stage has no name in the
program (`stageAt`, Johnson/Desc/K12/Join.lean, returns `none`), and where the claim cannot be
written out (`claimAt` returns `none`). At the last stage l is not read. -/
def valsFromB (p : P12) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → T12 → List Fmt.RoundView →
    List (List (ℕ × List UInt64)) → Bool
  | [], j, cur, _, t, rs, gs =>
    match t.pass with
    | .claim row _ =>
      match stageAt p j cur with
      | some c =>
        match claimAt t.st.codes c row with
        | some cl => (baseDecide (basePar p cur) cl rs gs).isOk
        | none => true
      | none => true
    | _ => true
  | next :: rest, j, cur, l, t, rs, gs =>
    match (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).decide t
        (rs.take (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length)
        (gs.take (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings) with
    | .ok t₁ =>
      match (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).decide t₁
          ((rs.drop (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length).take
            (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).rounds.length)
          ((gs.drop (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings).take
            (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).openings) with
      | .ok t₂ =>
        match (guardedProximityTestParts.batBehind p (j + 1) next
            (((l.drop (1 + cur.k)).take 2).map (·.1))).decide t₂ [] [] with
        | .ok t₃ =>
          valsFromB p rest (j + 1) next (l.drop (cur.k + 3)) t₃
            (rs.drop ((foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length +
              (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).rounds.length))
            (gs.drop ((foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings +
              (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).openings))
        | .error _ => true
      | .error _ => true
    | .error _ => true

/-- **The test says yes just where the hypothesis holds**: `valsFromB` and `ValsFrom` at the same
arguments, from any stage on. -/
theorem valsFromB_iff (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage)
    (l : Laid) (t : T12) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    valsFromB p rest j cur l t rs gs = true ↔ ValsFrom p rest j cur l t rs gs
  | [], j, cur, l, t, rs, gs => by
    unfold valsFromB ValsFrom
    constructor
    · intro h row L c cl hp hs hc
      rw [hp] at h
      dsimp only at h
      rw [hs] at h
      dsimp only at h
      rw [hc] at h
      dsimp only at h
      cases hb : baseDecide (basePar p cur) cl rs gs with
      | ok x => rw [baseDecide_same _ _ _ _ _ hb]
      | error e =>
        rw [hb] at h
        cases h
    · intro h
      split
      · rename_i row L hp
        split
        · rename_i c hs
          split
          · rename_i cl hc
            rw [h row L c cl hp hs hc]
            rfl
          · rfl
        · rfl
      · rfl
  | next :: rest, j, cur, l, t, rs, gs => by
    unfold valsFromB ValsFrom
    constructor
    · intro h t₁ t₂ t₃ e1 e2 e3
      rw [e1] at h
      dsimp only at h
      rw [e2] at h
      dsimp only at h
      rw [e3] at h
      dsimp only at h
      exact (valsFromB_iff p rest _ _ _ _ _ _).1 h
    · intro h
      split
      · rename_i t₁ e1
        split
        · rename_i t₂ e2
          split
          · rename_i t₃ e3
            exact (valsFromB_iff p rest _ _ _ _ _ _).2 (h t₁ t₂ t₃ e1 e2 e3)
          · rfl
        · rfl
      · rfl

/-- `ValsAsk` (TestReturnsOneIff.lean) with code. rB, R: the batching's round and the stages', as a
decision is shown them. Yes where the group is not there (`t.st.groups[t.g]?` is `none`) and where
the batching's combination gives nothing (`Bat.combine`, OnBytes/Iop/Bat.lean, returns `none`). -/
def valsAskB (p : P12) (cur nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (t : T12) (rB : Fmt.RoundView)
    (R : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) : Bool :=
  match t.st.groups[t.g]? with
  | some G =>
    match Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩ (drawnOf rB) with
    | some row => valsFromB p (nxt :: rest) 0 cur (laidS p) (batT t G row) R gs
    | none => true
  | none => true

theorem valsAskB_iff (p : P12) (cur nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (t : T12)
    (rB : Fmt.RoundView) (R : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    valsAskB p cur nxt rest t (noDigest rB) (R.map noDigest) gs = true ↔
      ValsAsk p cur nxt rest t rB R gs := by
  unfold valsAskB ValsAsk
  constructor
  · intro h G row hG hr
    rw [hG] at h
    dsimp only at h
    rw [hr] at h
    dsimp only at h
    exact (valsFromB_iff p _ _ _ _ _ _ _).1 h
  · intro h
    split
    · rename_i G hG
      split
      · rename_i row hr
        exact (valsFromB_iff p _ _ _ _ _ _ _).2 (h G row hG hr)
      · rfl
    · rfl

/-- `valsAskB`, with the stages read off the place (`p.nums.stages`) and the rounds as one list. rs:
the block's rounds as its decision is shown them. Yes at a place with fewer than two stages and at
no round. -/
def valsK12 (p : P12) (t : T12) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) : Bool :=
  match p.nums.stages with
  | cur :: nxt :: rest =>
    match rs with
    | rB :: R => valsAskB p cur nxt rest t rB R gs
    | [] => true
  | _ => true

/-- Where the place's stages are cur, nxt and then rest: `valsK12` at `(rB :: R).map noDigest` says
yes just where `ValsAsk` holds at rB and R. -/
theorem valsK12_iff {p : P12} {cur nxt : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    (hst : p.nums.stages = cur :: nxt :: rest) (t : T12) (rB : Fmt.RoundView) (R : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) :
    valsK12 p t ((rB :: R).map noDigest) gs = true ↔ ValsAsk p cur nxt rest t rB R gs := by
  unfold valsK12
  rw [hst]
  exact valsAskB_iff p cur nxt rest t rB R gs

/-- **Under `OneAsks` the block accepts just where the test with code says yes.** `OneAsks` is not
free of values: see the limits of TestReturnsOneIff.lean. -/
theorem k12_accept_iff_B {p : P12} {cur nxt : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {t : T12}
    {i n : ℕ × ℕ} {id tN : ℕ} {rB : Fmt.RoundView} {R : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (A : OneAsks p cur nxt rest t i n id tN rB R gs) :
    (∃ t', (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t ((rB :: R).map noDigest) gs = .ok t') ↔
      valsK12 p t ((rB :: R).map noDigest) gs = true :=
  (k12_accept_iff_one A).trans (valsK12_iff A.stages t rB R gs).symm

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.valsFromB_iff
#print axioms ProofFile.Honest.Sh.valsAskB_iff
#print axioms ProofFile.Honest.Sh.valsK12_iff
#print axioms ProofFile.Honest.Sh.k12_accept_iff_B
#print axioms ProofFile.Honest.Sh.valsFromB
#print axioms ProofFile.Honest.Sh.valsAskB
#print axioms ProofFile.Honest.Sh.valsK12
