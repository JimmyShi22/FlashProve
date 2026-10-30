-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/JoinGuarded.lean: the proximity test's parts, joined, in the form that the kind's block
rides: `guardedProximityTestParts : Parts T12`, over the parts of Join.lean. Definitions only, all computable;
nothing is proved here.

What it has beyond Join.lean's `proximityTestParts`.
  The last part, `baseJ5`, decides by the base case of Johnson/Desc/Prox/BaseCase.lean
    (`baseDecide`), at the claim that is left in front of it, written out (`claimAt`). It calls no
    test of the verifier program. What that program's last step asked of the record beside its
    decision is asked here by plain comparisons of the record's fields:
      the claim's form fits the code's message length (`Own.formFits`,
      Johnson/Desc/Own/Shapes.lean);
      the one group of columns stands at the list of the drawn positions (`Fmt.listOf`);
      `lastMember`: the last group has one row variable (which `claimAt` fixes at 0) and one member,
      not kept;
      `lastPairOk`: the record's two codes are the place's; the last message and the masking message
      have one main row and one mask row each; the masking message is fresh;
      `lastTree`: the two stand alone in one tree, in this order, with the declared label, depths
      and widths, and it has not been opened: so the order of the four symbols in a column is held
      against the record's book by this text.
    Then the record is turned in two lines: the masking message is marked as spent; the tree is
    counted as opened once.
  On the plan (the block's own test):
    no round of the cut opens a stored table; the base case's own three tests, and `baseRounds` at
    the place's numbers is the cut that the frame deals to the last part; the test sends a tree;
    `fixedOk` (FixedBefore.lean): every tree that a stage opens was sent in front of the first draw
    of the stage that spends it;
    `cutOk` (Law/FirstCut.lean): the first switch's cut of the declared rounds;
    `p.early` and `p.answers == 1`: the masks come early, and each sample has one answer: the two
    numbers of the place under which the kind's law speaks;
    no declared range of positions is longer than 2 ^ 32.
  On the record and the view, by the letters under which they refuse:
    (f) at the very front: the plan's count of the chain's roots in front of the test is the
        record's.
    (p) behind the front's own questions: `pubOk` (Law/PubOk.lean): the record's codes and the
        place's declared rounds meet every public clause that the library's chain asks.
    (c) in front of the batching: `combOk`: the group is in order, the layout is the statement's,
        and every row that the batching takes, the members' sample rows too, lies on its members'
        tables: `combineAt` (Johnson/Desc/Means/TestsB.lean) at the statement behind the test's
        beginning, the layout in front and the rows that the test takes in.
    (k) behind the batching: the claim that is left has no kept form, and no member of the group's
        layout is kept.
    (g) beside it: `gpOk` and `labelsOk` (Law/FirstOk.lean, Law/FirstCut.lean): each member's and
        the mask's shape, place, tree's shape and number against what the first switch's rounds
        declare.
    (z) in front of every part that is dealt rounds: every drawn position lies in its round's range.

Why the guards. Each of (f), (p), (k), (g)'s `gpOk`, `fixedOk` and `cutOk` was a premise of the
kind's law that stood beside the block. Asked by the block, its own yes pays them. (g)'s `labelsOk`
is spent by no theorem of that law: it guards the run. (c) is of another kind: no file is known that
brings the verifier to a record at which it refuses. The front asks of the group's open rows that
they lie on the members' tables; no test of this block but (c) asks it of the members' sample rows,
and the batching's own success does not give it. With (c) the block's yes gives `combineAt` at the
record in front
(`comb_of_step`, Law/Step8.lean), and no promise on the rows has to be carried along the chain.
`p.early` and `p.answers == 1` follow from a yes of the block's step too (Law/EarlyStep.lean,
Law/AnswersStep.lean);
asked on the plan, they serve the laws that stand in front of the rounds and have no yes to
spend.

Limits. `claimAt` calls three tools of the verifier program by name (`Form.fixLow`, `Form.writeOut`,
`ceilLog2`); it refuses at a stage with k ≠ 0: it is the last stage's. The batching, the fold and
the switch also call that program's pure functions by name, through the texts that Parts.lean
names. Not here: that every word of a field's element in a view is below the prime: that is the
description's own test on the whole view (Block.lean, `viewWordsBelowPrime`). `guardedProximityTestParts` names Join.lean's parts
one by one and not `proximityTestParts`, so that a walk over constants from the block does not reach Join.lean's
last part. `baseJ5` asks neither the numbers of draws of its two rounds nor the columns' key:
`Block.step` does (`roundsFit`; its test on the columns). By itself the part says yes to a view from
which drawn positions and their columns are dropped. `lastTree` asks that the tree has not been
opened, not that it is marked as one that is opened at one list only: that mark is the sending's.
State any law at `proximityTestKind guardedProximityTestParts p` under its test on the plan, not at `baseJ5` with free letters.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Join
import Johnson.Desc.Prox.BaseCase
import Johnson.Desc.K12.FixedBefore
import Johnson.Desc.K12.Law.FirstCut
import Johnson.Desc.K12.Law.PubOk
import Johnson.Desc.Own.Shapes
import OnBytes.Slice.BlkBegin
import Johnson.Desc.Means.TestsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Prox (BasePar BaseClaim baseCase baseRounds baseDecide elems four)

/-- The Form written out, by Form.writeOut. -/
def dense (f : Form) (vars : Nat) : Array Fmt.M1.E := (f.writeOut vars).map (·.triple)

/-- **The claim that is left in front of the base case, written out.** -/
def claimAt (K : Codes) (cur : IoppStage) (row : GroupRow) : Option BaseClaim := do
  let c ← K.base[cur.code]?
  if cur.k != 0 || !row.kept.isEmpty then none
  pure ⟨dense (row.c.fixLow [zeroE]) (ceilLog2 c.ell), row.d.map (·.triple), row.target.triple⟩

/-- The base case's numbers of the place. -/
def basePar (p : P12) (s : Fmt.M1.Stage) : BasePar :=
  let own := p.nums.free + p.nums.sent.length - 1
  { place := p.place, C := s.C, Z := s.Z, t := s.t, label := p.nums.firstTree + own, own := own,
    workLam := 0, workBase := p.nums.work }

/-- **The last group's one member**: the layout has one row variable (`claimAt` fixes it at 0), no
mask row variable and one member, not kept, whose one main row and one mask row are the tables'
first. -/
def lastMember (L : GroupLayout) : Option Nat :=
  if L.k == 1 && L.h == 0 && L.members.size == 1 && L.kept == #[false] &&
      L.mainFirst == #[some 0] && L.maskFirst == #[some 0] then
    L.members[0]?
  else none

/-- One main row over the extension field and one mask row, under the stage's two codes. -/
def oneRowEach (x : OnBytes.Oracle) (c : IoppStage) : Bool :=
  x.shape.mainRows == 1 && x.shape.mainDeg == 3 && x.shape.code == c.code &&
    x.shape.maskRows == 1 && x.shape.maskCode == c.maskCode

/-- **The last message m and the masking message star, as the record has them**: the record's two
codes at the stage's numbers are the place's; m and star are two messages, each of one main row and
one mask row under these codes; m belongs to one group at most; star is not sampled, counts no
answer and has not been spent. -/
def lastPairOk (P : BasePar) (S : Statement) (c : IoppStage) (m star : Nat) : Bool :=
  match S.codes.base[c.code]?, S.codes.mask[c.maskCode]?, S.oracles[m]?, S.oracles[star]? with
  | some k, some z, some x, some o =>
    (k.logN, k.ell, k.r) == (P.C.a, P.C.l, P.C.r) &&
    (z.logN, z.ell, z.r) == (P.Z.a, P.Z.l, P.Z.r) && star != m && oneRowEach x c &&
    decide (x.groups.length ≤ 1) && oneRowEach o c && !o.sampled && o.shape.answers == 0 &&
    !o.spentAsMask
  | _, _, _, _ => false

/-- **The one tree that holds them**: m is its part 0, star its part 1, and they are all that it
holds; it bears the declared label, the two codes' depths, and three main and three mask words a
part (so a column's twelve words are `four`'s four symbols, in `four`'s order); it has not been
opened. -/
def lastTree (P : BasePar) (B : TreeBook) (m star : Nat) : Option Nat :=
  match B.place[m]?, B.place[star]? with
  | some (a, 0), some (b, 1) =>
    match B.trees[a]? with
    | some T =>
      if a == b && T.parts == #[m, star] && T.number == P.label && T.shape.logN == P.C.a &&
          T.shape.logNzk == P.Z.a && T.shape.mainSymbols == #[3, 3] &&
          T.shape.maskSymbols == #[3, 3] && T.lists == 0 then some a
      else none
    | none => none
  | _, _ => none

/-- **The last part.** It writes the claim out, asks that its form fits, decides by `baseDecide`,
asks the four plain questions of the record and the columns that the head lists, and turns the
record: the masking message is spent, the tree is counted as opened. -/
def baseJ5 (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) : Part T12 where
  planOk := noStored cut && decide (1 ≤ p.nums.sent.length) &&
    (baseCase (Cl := Unit) (basePar p cur)).planOk && baseRounds (basePar p cur) == cut
  decide := fun t rs gs =>
    match t.pass, stageAt p j cur, cut with
    | .claim row L, some c, [_, _] => do
      let cl ← named "the base case: the claim cannot be written out" (claimAt t.st.codes c row)
      need "the base case: the claim's form does not fit the code's message length"
        ((t.st.codes.base[c.code]?).any fun k =>
          Own.formFits (row.c.fixLow [zeroE]) (ceilLog2 k.ell))
      let _ ← baseDecide (basePar p cur) cl rs gs
      need "the base case: the columns do not stand at the list of the drawn positions"
        (match rs, gs with
          | [_, rB], [g] => g.map (·.1) == Fmt.listOf rB.drawn.poss
          | _, _ => false)
      let m ← named "the base case: the last group is not of one row" (lastMember L)
      let star ← named "the base case: the masking message has not come" t.mask
      need
        "the base case: the codes, the last message or the masking message are not the place's, \
          or it is spent"
        (lastPairOk (basePar p cur) t.st c m star)
      let a ← named
        "the base case: the two messages do not stand alone in the declared tree, unopened"
        (lastTree (basePar p cur) t.book m star)
      pure { t with
        st :=
          { t.st with oracles := t.st.oracles.modify star fun x => { x with spentAsMask := true } }
        book :=
          { t.book with trees := t.book.trees.modify a fun x => { x with lists := x.lists + 1 } }
        pass := .nothing, mask := none }
    | _, _, _ => wrongForm "the base case"

/-- Every position that a round drew is below 2 ^ (its declared entry's logN). -/
def inRange (cut : List Fmt.DeclaredRound) (rs : List Fmt.RoundView) : Bool :=
  (cut.zip rs).all fun x => x.2.drawn.poss.all fun y => decide (y < 2 ^ x.1.entry.logN)

/-- **Guard (z)**, in front of a part that draws positions. On the plan: no range is longer than
2 ^ 32 (up to there the verifier program's point of a position is the format's). On the view: every
drawn position lies in its round's range. -/
def ranged (cut : List Fmt.DeclaredRound) (X : Part T12) : Part T12 where
  planOk := X.planOk && cut.all fun d => decide (d.entry.logN ≤ 32)
  decide := fun t rs gs => do
    need "(z): a drawn position is out of its round's range" (inRange cut rs)
    X.decide t rs gs

/-- **Guard (k)**, on the record that the batching leaves: the one claim has no kept form, and no
member of the group's layout is kept. -/
def noKept (t : T12) : Bool :=
  match t.pass with
  | .claim row L =>
    row.kept.isEmpty && (List.range L.members.size).all (fun i => !(L.kept.getD i false))
  | _ => false

/-- **Guard (c)**, on the record in front of the batching: the group is in order, the layout is the
statement's, and every row that the batching takes lies on its members' tables. No file is known
that brings the verifier to a record at which this guard refuses. It is here for the proof: so that
the block's own yes gives `combineAt` (`comb_of_step`, Law/Step8.lean), which the law of what the
batched rows mean asks of the record. At a statement in order, at one of its groups, the guard says
yes (`combOk_of_order`, Johnson/Prover/Link/FormBatLaws.lean). -/
def combOk (t : T12) : Bool :=
  match t.st.groups[t.g]?, t.st.layout t.g with
  | some G0, some Ly =>
    OnBytes.Means.combineAt (OnBytes.Slice.begun t.st t.g G0) t.g
      ⟨Ly, OnBytes.Slice.runRows t.st G0⟩
  | _, _ => false

/-- **The parts, joined**: the last one decides by its own text of the base case; every part that is
dealt rounds stands behind guard (z) (asked of every round that a part is dealt, not by name:
the batching's and the fold's rounds draw no position); the front and the batching ask (f), (p),
(c), (k) and (g). `group` and `maskCame` are Join.lean's `proximityTestParts`'s, written out. -/
def guardedProximityTestParts : Parts T12 where
  front := fun p =>
    { planOk := (frontJ p).planOk && H2K.FixedBefore.fixedOk p && H2K.First.cutOk p && p.early &&
        p.answers == 1
      decide := fun t rs gs => do
        need "(f): the plan's count of roots in front of the test is not the record's"
          (p.nums.free == t.roots)
        let t' ← (frontJ p).decide t rs gs
        need "(p): the record's codes or the place's rounds fail a public clause of the chain"
          (H2K.Pub.pubOk p t'.st.codes)
        pure t' }
  bat := fun p cut => ranged cut
    { batJ p cut with
      decide := fun t rs gs => do
        need "(c): the group is not in order, or a batched row lies outside its members' tables"
          (combOk t)
        let t' ← (batJ p cut).decide t rs gs
        need "(k): behind the batching the claim has a kept form, or the group a kept member"
          (noKept t')
        need "(g): the group's trees in the record are not those that the place's numbers declare"
          (H2K.First.gpOk p t' && H2K.First.labelsOk p t')
        pure t' }
  fold := fun p j cur cut => ranged cut (foldJ p j cur cut)
  switch := fun p j cur next last cut => ranged cut (switchJ p j cur next last cut)
  batBehind := behindJ
  base := fun p j cur cut => ranged cut (baseJ5 p j cur cut)
  group := fun t =>
    match t.pass, t.st.groups[t.g]? with
    | .claim _ L, some G =>
      match t.st.codes.base[G.code]?, t.st.codes.mask[G.maskCode]? with
      | some c, some z => some (⟨c.logN, c.ell, c.r⟩, ⟨z.logN, z.ell, z.r⟩, L.k, L.h)
      | _, _ => none
    | _, _ => none
  maskCame := fun t => t.mask.isSome

end VerifiableInference.Desc.K12
