-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSwitch.lean: the form's half at a code switch of the proximity test and at
the batching behind it: the letters for saying that the description's two parts
(`guardedProximityTestParts.switch`, `guardedProximityTestParts.batBehind`, Johnson/Desc/K12/JoinGuarded.lean) return ok, from facts on the
plan, on the view's format and on the carried record. Not all of them are free of values: `factor`
reads a drawn element; `add` holds the tests on the made rows, whose coefficients come from drawn
values (each variable's pair of a vector of product form; 0 on every pad); `read` and `can` read the
dealt columns; `batch` reads the rows.

What is proved of them: Johnson/Prover/Link/FormSwitchLaws.lean.

Main names (namespace `Johnson.Prover.Link`).
  `swTarget p n`, `swOthers`, `swNotices`   the switch's target at the next stage n, what comes with
      the new message, and the announcements of the sending, as `switchJ` lays them where the masks
      come early
  `switchCut logN dS dC`   a test on the two declared rounds that the frame deals to a switch
  `swD0`, `swD2`   the plain state in front of the sending and behind it
  `swIds`, `swIn`   the numbers that the sending returns; what the step behind the sending reads
  `swPos`, `swOut`   the list of positions; what the switch returns
  `SwitchFacts`   `SwitchFront` with the joining and the adding of the rows asked as bare yeses:
      every clause is a Boolean or "= some" of a letter, so that it can be evaluated
  `SwitchFront`, `BehindFront`   the carried record, the plan and the view in front of a switch, and
      what the batching behind it asks: each clause one test of the description's own text
  `switchT`, `behindT`   the record behind the switch, and behind the batching, as functions of the
      record in front, the rounds and the letters of `Taken` (Johnson/Desc/K12/Law/SwDid.lean)

The statements between are the soundness side's own terms: `Taken.stA`, `Taken.stJ`, `Taken.stR`,
`Taken.grown`, `bookSentP` (SwDid.lean).

Limits. Letters and tests: nothing says here that a record or a plan meets them. Served: masks that
come early, one answer to a sample, no kept member.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.K12.Law.SwDid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

/-- The switch's target at the next stage. -/
def swTarget (p : P12) (n : IoppStage) : SwitchTarget :=
  switchTargetStage n.code n.maskCode n.k n.h p.answers

/-- The announcements of the sending. -/
def swNotices (p : P12) (n : IoppStage) (last : Bool) : Array OracleNotice :=
  Tw.L9.switchNotices (swTarget p n) (othersOf last n)

/-- A test on the two declared rounds of a switch. logN: the old main code's. -/
def switchCut (logN : Nat) (dS dC : Fmt.DeclaredRound) : Bool :=
  dS.entry.name == "SEND seed" && dS.entry.drawNZ == 1 && dS.entry.rows == 0 &&
    dS.entry.poss == 0 && dS.entry.trits == 0 && dS.items.filter (· != .root) == [] &&
    dC.entry.name == "CS" && dC.entry.drawE == 1 && dC.entry.drawNZ == 0 &&
    dC.entry.logN == logN && decide (0 < dC.entry.poss) && dC.entry.trits == 0 &&
    dC.items.filter (· != .root) == [.answer] && dS.stored.isEmpty && dC.stored.isEmpty

variable (p : P12) (n : IoppStage) (last : Bool) (dS dC : Fmt.DeclaredRound) (t : T12)
  (rS rC : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (rows : SingleRows) (gp : Nat)
  (D : Taken)

/-- The plain state in front of the sending. -/
def swD0 : Desc.Plain.DState Unit :=
  { st := t.st, book := t.book, roots := t.roots, opened := keyed p [dS, dC] gs, loc := () }

/-- The plain state behind the sending. -/
def swD2 : Desc.Plain.DState Unit :=
  { st := D.stA (swTarget p n) (othersOf last n) t.st
    book := bookSentP p.nums.firstTree t.roots t.st t.book
      (sentOf (swTarget p n) (othersOf last n)) D.lay
    roots := t.roots + D.lay.shapes.size, opened := keyed p [dS, dC] gs, loc := () }

/-- The numbers that the sending returns. -/
def swIds : Array Nat :=
  (Array.range (swNotices p n last).size).map (· + t.st.oracles.size)

/-- What the step behind the sending reads, as `switchE` lays it. `itemsLeft` is
`rC.vals.length - 1`, in natural numbers: 0 where `rC.vals` is empty. -/
def swIn : Tw.L9.SwIn :=
  { st := (swD2 p n last dS dC t gs D).st, book := (swD2 p n last dS dC t gs D).book
    firstTree := p.nums.firstTree, opened := keyed p [dS, dC] gs, old := rows
    T := swTarget p n, grp := gp, ids := swIds p n last t
    entry := { dC.entry with name := "LOC", drawE := 0 }, settled := true
    drawn := { rC.drawn with elems := [] }, itemsLeft := rC.vals.length - 1 }

/-- The list of positions. -/
def swPos : Positions := Positions.ofDraws D.code.logN rC.drawn.poss

/-- What the switch returns. WHERE `swIds` IS EMPTY: `g` is `noId`. -/
def swOut : Switched :=
  { g := (swIds p n last t).getD 0 noId, kept := #[]
    others := (swIds p n last t).extract 1 (swIds p n last t).size, positions := swPos rC D }

/-- **The record behind the switch.** B: the book behind the reading. theta: the drawn element. -/
def switchT (B : TreeBook) (theta : E) : T12 :=
  { t with st := D.stR (swTarget p n) gp (othersOf last n) t.st, book := B
           roots := t.roots + D.lay.shapes.size
           pass := .switched (swOut p n last t rC D) theta gp }

/-- **The carried state behind the batching.** `mask` is the first of `swOut`'s `others`; where
there is none: `none`. -/
def behindT (B : TreeBook) (row : GroupRow) (lay : GroupLayout) : T12 :=
  { t with st := begun (D.stR (swTarget p n) gp (othersOf last n) t.st) gp (D.grown t.st), book := B
           roots := t.roots + D.lay.shapes.size
           pass := .claim row lay, mask := (swOut p n last t rC D).others[0]? }

/-- **The carried record, the plan and the view in front of a switch.** Each clause is one test of
the description's own text, at a written term. x: the element that the second round draws. -/
structure SwitchFront (j : Nat) (next : Fmt.M1.Stage) (B : TreeBook) (x : Fmt.Ext) : Prop where
  pass : t.pass = .single rows gp
  stage : stageAt p (j + 1) next = some n
  early : p.early = true
  one : p.answers = 1
  guard : Tw.L9.switchGuard t.st rows (swTarget p n) = true
  cut : switchCut D.code.logN dS dC = true
  fit : roundsFit [dS, dC] [rS, rC] = true
  recv : Ground.ok (Ground.recvL t.st t.book (swNotices p n last)) = true
  trees : Own.treesMade t.st.codes (swNotices p n last) = some D.lay
  seed : (rS.drawn.elems.map E.ofTriple).drop (Send.cube t.st.codes (swTarget p n).shape).bits =
    [D.beta]
  factor : Own.allZero D.beta = false
  form : Own.formMade t.st.codes (swTarget p n).shape t.st.oracles.size
    ⟨(rS.drawn.elems.map E.ofTriple).take (Send.cube t.st.codes (swTarget p n).shape).bits,
      D.beta⟩ 0 = some D.smp
  pad : Own.padMade t.st.codes (swTarget p n).shape = some D.places
  ans : rC.vals = [.answer D.alpha.triple]
  admit : Ground.ok (Ground.admitL (stSent t.st (swNotices p n last)) t.st.oracles.size
    #[D.sample]) = true
  elem : rC.drawn.elems = [x]
  code : t.st.codes.base[rows.code]? = some D.code
  read : Tw.L9.readOld (swIn p n last dS dC t rC gs rows gp D) (swPos rC D) = .ok (B, [], D.y)
  join : Tw.L9.joinS (ledgerShut (D.stA (swTarget p n) (othersOf last n) t.st) (swTarget p n)
    t.st.oracles.size) gp t.st.oracles.size false =
      .ok (D.stJ (swTarget p n) gp (othersOf last n) t.st)
  fresh : ∃ G, (D.stJ (swTarget p n) gp (othersOf last n) t.st).groups[gp]? = some G ∧
    G.inRun = false
  can : Tw.K2.rowsCan (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows (swTarget p n) #[]
    (swPos rC D) D.y = true
  made : D.rows = (Own.swRows (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows (swTarget p n)
    t.st.oracles.size #[] (swPos rC D) D.y).getD []
  add : D.rows.foldlM (fun S r => Tw.L9.addRowS S gp r)
    (D.stJ (swTarget p n) gp (othersOf last n) t.st) =
      .ok (D.stR (swTarget p n) gp (othersOf last n) t.st)

/-- `SwitchFront` with three fields swapped: for `join` and `add` (equations) `joinOk` and `addOk`
(`.toOption.isSome = true` of the same calls); for `fresh` the field `group`. -/
structure SwitchFacts (j : Nat) (next : Fmt.M1.Stage) (B : TreeBook) (x : Fmt.Ext) : Prop where
  pass : t.pass = .single rows gp
  stage : stageAt p (j + 1) next = some n
  early : p.early = true
  one : p.answers = 1
  guard : Tw.L9.switchGuard t.st rows (swTarget p n) = true
  cut : switchCut D.code.logN dS dC = true
  fit : roundsFit [dS, dC] [rS, rC] = true
  recv : Ground.ok (Ground.recvL t.st t.book (swNotices p n last)) = true
  trees : Own.treesMade t.st.codes (swNotices p n last) = some D.lay
  seed : (rS.drawn.elems.map E.ofTriple).drop (Send.cube t.st.codes (swTarget p n).shape).bits =
    [D.beta]
  factor : Own.allZero D.beta = false
  form : Own.formMade t.st.codes (swTarget p n).shape t.st.oracles.size
    ⟨(rS.drawn.elems.map E.ofTriple).take (Send.cube t.st.codes (swTarget p n).shape).bits,
      D.beta⟩ 0 = some D.smp
  pad : Own.padMade t.st.codes (swTarget p n).shape = some D.places
  ans : rC.vals = [.answer D.alpha.triple]
  admit : Ground.ok (Ground.admitL (stSent t.st (swNotices p n last)) t.st.oracles.size
    #[D.sample]) = true
  elem : rC.drawn.elems = [x]
  code : t.st.codes.base[rows.code]? = some D.code
  read : Tw.L9.readOld (swIn p n last dS dC t rC gs rows gp D) (swPos rC D) = .ok (B, [], D.y)
  group : (ledgerShut (D.stA (swTarget p n) (othersOf last n) t.st) (swTarget p n)
    t.st.oracles.size).groups[gp]? = some D.G
  joinOk : (Tw.L9.joinS (ledgerShut (D.stA (swTarget p n) (othersOf last n) t.st) (swTarget p n)
    t.st.oracles.size) gp t.st.oracles.size false).toOption.isSome = true
  can : Tw.K2.rowsCan (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows (swTarget p n) #[]
    (swPos rC D) D.y = true
  made : D.rows = (Own.swRows (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows (swTarget p n)
    t.st.oracles.size #[] (swPos rC D) D.y).getD []
  addOk : (D.rows.foldlM (fun S r => Tw.L9.addRowS S gp r)
    (D.stJ (swTarget p n) gp (othersOf last n) t.st)).toOption.isSome = true

/-- **What the batching behind the switch asks.** -/
structure BehindFront (theta : E) (row : GroupRow) (lay : GroupLayout) : Prop where
  early : p.early = true
  begin : Ground.ok (Ground.beginRunL (D.stR (swTarget p n) gp (othersOf last n) t.st) gp) = true
  group : (D.stR (swTarget p n) gp (othersOf last n) t.st).groups[gp]? = some (D.grown t.st)
  layout : Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st) = lay
  count : dC.entry.rows =
    (runRows (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st)).size
  counts : dC.entry.rows ≠ 0
  batch : Own.batch (begun (D.stR (swTarget p n) gp (othersOf last n) t.st) gp (D.grown t.st)) gp
    ⟨lay, runRows (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st)⟩ theta = some row

end Johnson.Prover.Link
