-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Plan/Test.lean: what the entries of a plan must say at the rounds of a prover's
message and of a proximity test, as a function of the codes, the stages and a few counts; and the
test that a stretch of a plan's entries says so. Definitions with code; Bool tests; public data
only.

Why. The parameter bytes of a chain hold a plan: for each round an entry with the round's name and
eleven numbers (`Fmt.Entry`, Fmt/Plan.lean). The format's own reading of a file goes by these
numbers: how many bytes the prover sends, how many roots and sample answers are among them, how
many elements and positions are drawn. A description of the protocol has numbers of its own, from
the shapes. Here the two are compared, number by number, but for the bits of work and the number of
positions (see Limits).

Main names.
  `Want`, `Want.meets`: what an entry must say, but for its bits of work and for how many positions
    it draws; an entry says so.
  `wantSeed`, `wantAnswer`: the two rounds of a prover's message: seeds, answers.
  `largestCube`, `treesSent`: two counts of a prover's message that `wantSeed` takes.
  `wantsStages`, `wantsTest`: the entries of a proximity test, from its batching round on. Written
    after the planner's own list (`ioppList`, OnBytes/Params/PlanListsProx.lean) and after what the
    verifier program's blocks ask of an entry when they close a round (`Blk.close`,
    `closePositions`, `requireRows`: OnBytes/Iop/Ground.lean).
  `okFrom`: the plan's entries from a round on meet a list of wants, one by one.

Limits. No theorem: that `wantsTest` is the planner's list, or what those blocks ask, is proved
nowhere here. An entry's bits of work are not read. Of the number of positions that a round draws
only "none" or "at least one" is asked; the rows of a batching round are held against that number.
A stage's code whose number is not in the list of codes is read as the blank code
(`getD … default`, in `wantsStages`), and `treesSent` is 0 where the messages cannot be laid into
trees: neither is refused here. At one stage `firstMaskRoots` is not read; at no stage the list is
the batching round alone; the planner's `ioppList` is no plan's list below two stages. `Want`,
`largestCube` and `treesSent` are short names elsewhere in this library too: whoever opens both
namespaces meets an ambiguity. Nothing on soundness.

-/
import OnBytes.Iop.Prox
import OnBytes.Params.Chains

set_option autoImplicit false

namespace VerifiableInference.Desc.Key.Plan

open OnBytes OnBytes.Params

/-- What a plan's entry must say. -/
structure Want where
  /-- the round's name -/
  name : String
  /-- the bytes of the prover's message -/
  msg : Nat := 0
  /-- the roots among them -/
  roots : Nat := 0
  /-- the sample answers among them -/
  answers : Nat := 0
  /-- the elements of the extension field that are drawn -/
  drawE : Nat := 0
  /-- how many of these must not be 0 -/
  drawNZ : Nat := 0
  /-- if the round draws positions: they are drawn below 2 ^ logN -/
  logN : Option Nat := none
  /-- the rows that the round batches, from the number of its positions -/
  rows : Nat → Nat := fun _ => 0

/-- The entry says what is wanted: it stands for one round, has the wanted name and numbers and
draws no matrix entry; it draws positions, in the wanted range, just if a range is wanted. Its bits
of work are not read. -/
def Want.meets (w : Want) (e : Fmt.Entry) : Bool :=
  e.name == w.name && e.count == 1 && e.msg == w.msg && e.roots == w.roots &&
  e.answers == w.answers &&
  e.drawE == w.drawE && e.drawNZ == w.drawNZ && e.trits == 0 &&
  (match w.logN with
    | some a => decide (0 < e.poss) && e.logN == a
    | none => e.poss == 0 && e.logN == 0) &&
  e.rows == w.rows e.poss

/-- The round of seeds of a prover's message: roots trees; the largest cube among its sampled
messages has bits coordinates. -/
def wantSeed (samples roots bits : Nat) : Want :=
  { name := "SEND seed", msg := 32 * roots, roots := roots, drawE := samples * (bits + 1),
    drawNZ := samples }

/-- The round of the answers of n sampled messages. -/
def wantAnswer (samples n : Nat) : Want :=
  { name := "SEND answer", msg := 24 * (samples * n), answers := samples * n }

/-- The number of coordinates of the largest cube among the oracle messages that are sampled. -/
def largestCube (codes : Codes) (l : List OracleShape) : Nat :=
  (l.filter fun s => s.answers != 0).foldl (fun b s => max b (Send.cube codes s).bits) 0

/-- The number of trees in which a prover's message is sent; 0 where the messages cannot be laid
into trees. -/
def treesSent (codes : Codes) (sent : Array OracleNotice) : Nat :=
  ((layTrees codes sent).map (·.shapes.size)).getD 0

/-- The stages' rounds: for each stage but the last FOLD epsilon, the stage's k rounds FOLD round,
the seeds of the next stage's message and CS; for the last BASE lambda and BASE. first: this is the
test's first stage. -/
def wantsStages (codes : Codes) (samples firstMaskRoots : Nat) (ride : Bool) :
    Bool → List IoppStage → List Want
  | first, x :: y :: rest =>
    let r := if first then firstMaskRoots else if ride then 0 else 1
    let cube := (Send.cube codes (switchTargetStage y.code y.maskCode y.k y.h samples).shape).bits
    [{ name := "FOLD epsilon", msg := 32 * r + 24, roots := r, drawE := 1 }] ++
    List.replicate x.k { name := "FOLD round", msg := 48, drawE := 1 } ++
    [wantSeed samples 1 cube,
     { name := "CS", msg := 24 * samples, answers := samples, drawE := 1,
       logN := some (codes.base.getD x.code default).logN,
       rows := fun t => 1 + samples + 3 * t }] ++
    wantsStages codes samples firstMaskRoots ride false (y :: rest)
  | _, [x] =>
    let r := if ride then 0 else 1
    [{ name := "BASE lambda", msg := 32 * r + 24, roots := r, drawE := 1 },
     { name := "BASE",
       msg := 24 * ((codes.base.getD x.code default).dim +
         (codes.mask.getD x.maskCode default).dim),
       logN := some (codes.base.getD x.code default).logN }]
  | _, [] => []

/-- **The entries of a proximity test, from its batching round on.** rowsAtBat: the rows that the
first round batches. firstMaskRoots: the roots that the first fold sends itself. ride: later masks
ride with the message before them and have no root of their own. -/
def wantsTest (codes : Codes) (samples : Nat) (st : List IoppStage)
    (rowsAtBat firstMaskRoots : Nat) (ride : Bool) : List Want :=
  { name := "BAT", drawE := 1, rows := fun _ => rowsAtBat } ::
    wantsStages codes samples firstMaskRoots ride true st

/-- The plan's entries from round i on meet the wants, one by one. -/
def okFrom (ws : List Want) (es : List Fmt.Entry) (i : Nat) : Bool :=
  ((es.drop i).take ws.length).length == ws.length &&
    (ws.zip (es.drop i)).all fun p => p.1.meets p.2

end VerifiableInference.Desc.Key.Plan
