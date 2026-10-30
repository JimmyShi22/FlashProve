-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Driver/Cut.lean: the first chain's table of stretches: which rounds each step
takes, as a function of the plan's entries.

Definitions with code alone; no theorem. It runs: the proof file's public part is
made with it (`ProofFile.pubBy`, Johnson/Desc/ProofFile/Pub.lean). It imports the format's plan alone:
no Mathlib. The table holds these facts. A lookup may lack "LKP shift". Attention's scores are not
always two sumchecks. The seal's row takes no round (the view that the frame hands to the file's
decision has no sealing round; the plan's last entry, "SEAL", is asked for and handed to no row). A
sending with answers is a link's first call at link 0 alone. The closing is "BAT", "FOLD epsilon",
then "FOLD round"s.


The plan's entries of a proof file's first chain bear names. cutOf reads the names, in order, by a
small grammar (a link: its first call; the lookup on the calls; the own rounds; the sending of the
reads; the matrix's draw; the sending of the digits; the lookup on the digits; at the head a merge;
the batching draw; the closing. Behind the links: the finish; the members' places; the seal) and
gives one row a step: the step's two names as the skeleton of the chain (Johnson/Skeleton/) has them
(look, step), the number and kind of the place in which it lies, and how many rounds it takes. A
step that takes no round is a row too. It refuses a list of names that the grammar does not fit;
nothing is left over.

Main names:
  Cut: look · step · place · kind · take.
  lookLen: a lookup runs from "LKP shift" (which stands only where it serves more than one call), or
    else from "LKP", to the first "PSC values" behind its first "ZERO".
  scoresLen: attention's scores end in front of the last "PSC epsilon" before the own rounds' first
    "BAT-sigma" (however many sumchecks they are).
  linkCut: one link. finishCut, membersCut: behind the links. cutOf: the chain.

What is not claimed. That the names are the planner's (the entries are an argument). That a step at
a row does what the program does there. The grammar's rules follow two texts of this project, seven
rules on the plan's names and a table of places: held against both, and against the
places as a term of the plan's records (KObj.Seg.modelPlaces), by gates beside this file, at two
sizes. Its bluntness: it reads no name and counts no round inside a lookup, the own rounds, a stage
or the closing beyond what the rules name: an entry struck there gives another table, end to end.
Opened columns are no part of a row: how many a step takes hangs on the positions drawn. A plan that
the grammar does not fit is refused whole, and with it the public files: that the grammar fits the
plan of every set of public files in the goals' scope is shown by no theorem that we know of.
`linksCut` and `stagesCut` run on a fuel, the number of names, and refuse where it runs out: every
turn strikes a name, so by reading it is enough; no theorem says so. Where no round stands in front
of the members' sending (b = 0 in `membersCut`) the rows M.0.… and M.1.… get one place number, and
`ProofFile.byPlace` (Johnson/Desc/ProofFile/Places.lean) joins them into one place of the kind K13: how
the description fares then is not tried. At the stored full size b is 20.
Nothing on soundness, on an honest prover or on hiding.

-/
import Fmt.Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- One row of the table of stretches. -/
structure Cut where
  /-- the step's two names in the skeleton -/
  look : String
  step : String
  /-- the number of the place in which it lies, from 0, and the place's kind -/
  place : Nat
  kind : String
  /-- how many rounds it takes -/
  take : Nat
  deriving Repr, BEq

/-- How many names stand in front of the first that is s; none if s does not come. -/
def upTo (s : String) (ns : List String) : Option Nat :=
  let a := (ns.takeWhile (· != s)).length
  if a < ns.length then some a else none

/-- The list begins with these names. -/
def begins (l ns : List String) : Bool := ns.take l.length == l

/-- A lookup: from "LKP shift", or else from "LKP", to the first "PSC values" behind its first
"ZERO". -/
def lookLen (ns : List String) : Option Nat :=
  if !(begins ["LKP shift", "LKP"] ns || ns.head? == some "LKP") then none
  else (upTo "ZERO" ns).bind fun a => (upTo "PSC values" (ns.drop a)).map fun b => a + b + 1

/-- Attention's scores: up to the last "PSC epsilon" in front of the first "BAT-sigma". -/
def scoresLen (ns : List String) : Option Nat :=
  (upTo "BAT-sigma" ns).bind fun b =>
    ((ns.take b).zipIdx.filter fun x => x.1 == "PSC epsilon").getLast?.map (·.2)

/-- The closing's rounds: "BAT", "FOLD epsilon", then "FOLD round"s; 0 if it does not begin so. -/
def doorLen (ns : List String) : Nat :=
  if begins ["BAT", "FOLD epsilon", "FOLD round"] ns then
    2 + ((ns.drop 2).takeWhile (· == "FOLD round")).length
  else 0

/-- The rows of the places 4 to 7 of a link and what follows up to its end. c: the first letter of
the steps' names; L: the look's head; i: the number of the look at the reads; pl: the place's
number. -/
def tailCut (c L : String) (i pl : Nat) (head : Bool) (claims : List (String × String))
    (ns : List String) : Option (List Cut × Nat × List String) := do
  let at' := fun (j : Nat) (w : String) => L ++ "." ++ toString j ++ "." ++ w
  if !begins ["SEND seed", "SEND answer", "RNG", "SEND seed", "SEND answer"] ns then none
  let n₁ := ns.drop 5
  let k ← lookLen n₁
  let n₂ := n₁.drop k
  let m ← upTo "BAT" n₂
  if m == 0 || (n₂.drop (m - 1)).head? != some "BAT-sigma" || (!head && m != 1) then none
  let n₃ := n₂.drop m
  let d := doorLen n₃
  if d == 0 then none
  let j := if head then i + 5 else i + 4
  let q := if head then pl + 5 else pl + 4
  pure (
    [⟨at' i "call", c ++ "Reads", pl, "send", 2⟩, ⟨at' i "quiet", c ++ "ReadsQuiet", pl, "send", 0⟩,
     ⟨at' (i + 1) "call", c ++ "Draw", pl + 1, "rng", 1⟩,
     ⟨at' (i + 2) "call", c ++ "Digits", pl + 2, "send", 2⟩,
     ⟨at' (i + 3) "call", c ++ "DigitsLook", pl + 3, "lookupDigits", k⟩,
     ⟨at' (i + 3) "quiet", c ++ "DigitsQuiet", pl + 3, "lookupDigits", 0⟩] ++
    (if head then
      [⟨at' (i + 4) "call", c ++ "Merge", pl + 4, "merge", m - 1⟩,
       ⟨at' (i + 4) "quiet", c ++ "MergeQuiet", pl + 4, "merge", 0⟩] else []) ++
    [⟨at' j "call", c ++ "Batch", q, "batSigma", 1⟩] ++
    (claims.map fun x => ⟨at' j x.1, c ++ x.2, q, "batSigma", 0⟩) ++
    [⟨at' (j + 1) "call", c ++ "Door", q + 1, "batFold", d⟩,
     ⟨at' (j + 1) "quiet", c ++ "DoorQuiet", q + 1, "batFold", 0⟩], q + 2, n₃.drop d)

/-- One link. g, a: how many layers' and attention links stand in front; pl: the next place's
number. Returns the rows, the two counts, the next place's number, whether it was the head's link,
and the names left. -/
def linkCut (g a pl : Nat) (ns : List String) :
    Option (List Cut × Nat × Nat × Nat × Bool × List String) := do
  let isHead := ns.head? == some "REPLY"
  let n₀ := if isHead then ns.drop 1 else ns
  let first := pl == 0 && !isHead
  if !begins ["SEND seed", if first then "SEND answer" else "LOC"] n₀ then none
  let fk := if first then "send" else "sendLoc"
  let n₁ := n₀.drop 2
  let k ← lookLen n₁
  let n₂ := n₁.drop k
  let o ← upTo "SEND seed" n₂
  if o == 0 then none
  if isHead then
    let (t, pl', rest) ← tailCut "s" "H" 4 (pl + 4) true
      [("front", "WalkFront"), ("objects", "Objects"), ("back", "WalkBack"), ("quiet", "Tests")]
      (n₂.drop o)
    pure ([⟨"H.0.front", "sFront", pl, "reply", 0⟩, ⟨"H.0.call", "sReply", pl, "reply", 1⟩,
      ⟨"H.1.call", "sSwitch", pl + 1, fk, 2⟩, ⟨"H.1.quiet", "sSwitchQuiet", pl + 1, fk, 0⟩,
      ⟨"H.2.call", "sLook", pl + 2, "lookupCalls", k⟩,
      ⟨"H.3.call", "sOwn", pl + 3, "headRow", o⟩,
      ⟨"H.3.quiet", "sOwnQuiet", pl + 3, "headRow", 0⟩] ++ t, g, a, pl', true, rest)
  else if n₂.head? == some "PSC epsilon" then
    let L := "A" ++ toString a
    let sc ← scoresLen (n₂.take o)
    let zr ← upTo "ZERO" n₂
    if !(decide (sc < zr) && decide (zr < o)) then none
    let (t, pl', rest) ← tailCut "a" L 3 (pl + 3) false
      [("claims", "Claims"), ("objects", "Objects"), ("quiet", "Tests")] (n₂.drop o)
    pure ([⟨L ++ ".0.call", "aFirst", pl, fk, 2⟩, ⟨L ++ ".0.quiet", "aFirstQuiet", pl, fk, 0⟩,
      ⟨L ++ ".1.call", "aLook", pl + 1, "lookupCalls", k⟩,
      ⟨L ++ ".2.scores", "aScores", pl + 2, "chain", sc⟩,
      ⟨L ++ ".2.divide", "aDivide", pl + 2, "chain", zr - sc⟩,
      ⟨L ++ ".2.call", "aAttain", pl + 2, "chain", o - zr⟩] ++ t, g, a + 1, pl', false, rest)
  else
    let L := "G" ++ toString g
    let (t, pl', rest) ← tailCut "g" L 3 (pl + 3) false
      [("front", "ClaimsFront"), ("objects", "Objects"), ("back", "ClaimsBack"), ("quiet", "Tests")]
      (n₂.drop o)
    pure ([⟨L ++ ".0.call", "gFirst", pl, fk, 2⟩, ⟨L ++ ".0.quiet", "gFirstQuiet", pl, fk, 0⟩,
      ⟨L ++ ".1.call", "gLook", pl + 1, "lookupCalls", k⟩,
      ⟨L ++ ".1.quiet", "gLookQuiet", pl + 1, "lookupCalls", 0⟩,
      ⟨L ++ ".2.call", "gOwn", pl + 2, "chain", o⟩] ++ t, g + 1, a, pl', false, rest)

/-- The links in a row, up to the head's, that one too. -/
def linksCut : (fuel g a pl : Nat) → List String → Option (List Cut × Nat × List String)
  | 0, _, _, _, _ => none
  | fuel + 1, g, a, pl, ns => do
    let (rows, g', a', pl', wasHead, rest) ← linkCut g a pl ns
    if wasHead then pure (rows, pl', rest)
    else
      let (more, pl'', rest') ← linksCut fuel g' a' pl' rest
      pure (rows ++ more, pl'', rest')

/-- The stages of the finish's test: each from "FOLD epsilon" to its "CS". i: the look's number. -/
def stagesCut : (fuel i pl : Nat) → List String → Option (List Cut × Nat × List String)
  | 0, _, _, _ => none
  | fuel + 1, i, pl, ns =>
    if ns.head? == some "FOLD epsilon" then do
      let c ← upTo "CS" ns
      let (more, j, rest) ← stagesCut fuel (i + 1) pl (ns.drop (c + 1))
      pure ([⟨"F." ++ toString i ++ ".call", "fStage", pl, "test", c + 1⟩,
        ⟨"F." ++ toString i ++ ".quiet", "fStageQuiet", pl, "test", 0⟩] ++ more, j, rest)
    else some ([], i, ns)

/-- The finish: the last switch and the last test. -/
def finishCut (pl : Nat) (ns : List String) : Option (List Cut × Nat × List String) := do
  if !begins ["SEND seed", "LOC", "BAT"] ns then none
  let (st, i, rest) ← stagesCut ns.length 2 (pl + 1) (ns.drop 3)
  if !begins ["BASE lambda", "BASE"] rest then none
  pure ([⟨"F.0.front", "fFront", pl, "sendLoc", 0⟩, ⟨"F.0.call", "fSwitch", pl, "sendLoc", 2⟩,
    ⟨"F.0.quiet", "fSwitchQuiet", pl, "sendLoc", 0⟩,
    ⟨"F.1.front", "fBatFront", pl + 1, "test", 0⟩, ⟨"F.1.call", "fBat", pl + 1, "test", 1⟩,
    ⟨"F.1.quiet", "fBatQuiet", pl + 1, "test", 0⟩] ++ st ++
    [⟨"F." ++ toString i ++ ".call", "fBase", pl + 1, "test", 2⟩], pl + 2, rest.drop 2)

/-- The members' places and the seal. -/
def membersCut (pl : Nat) (ns : List String) : Option (List Cut) := do
  let b ← upTo "SEND seed" ns
  if b != 0 && ns.head? != some "BAT-sigma" then none
  if (ns.drop b) != ["SEND seed", "SEND answer", "SEAL"] then none
  let q := if b == 0 then pl else pl + 1
  pure [⟨"M.0.front", "mFront", pl, "batPsc", 0⟩, ⟨"M.0.call", "mBatt", pl, "batPsc", b⟩,
    ⟨"M.0.quiet", "mBattQuiet", pl, "batPsc", 0⟩, ⟨"M.1.call", "mSend", q, "send", 2⟩,
    ⟨"M.1.quiet", "mSendQuiet", q, "send", 0⟩, ⟨"seal.behind", "seal", q + 1, "SEAL", 0⟩]

/-- **The first chain's table of stretches**, out of the plan's entries. -/
def cutOf (es : List Fmt.Entry) : Option (List Cut) := do
  let ns := es.map (·.name)
  let (a, pl, r₁) ← linksCut ns.length 0 0 0 ns
  let (b, pl', r₂) ← finishCut pl r₁
  let c ← membersCut pl' r₂
  pure (a ++ b ++ c)

end VerifiableInference.Desc.First
