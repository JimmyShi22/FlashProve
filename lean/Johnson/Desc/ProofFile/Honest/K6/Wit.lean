-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Wit.lean: the honest side of the sub-protocol "the output head's
own rounds": how the small input at which its parts are typed (`HeadAsk`, Honest/K6/Ask.lean) is
made of the prover's input. Definitions with code, tests, four small theorems and one example.

  `HeadWhere`      the public numbers that say where the head's cells lie and where the lookup's
                   challenges stand
  `headMatNames`, `headMats`   the matrices of the head's segment by their numbers in the plan's
                   own list, read through the witness's reader by that list's names
  `headCellsOf`    the cells as integers, by feature and position, and the head's weights
  `headWeightIdx`, `headWeightIn`, `headTensorOf`   the head's weights as a tensor, read off the
                   matrix of all committed weights' digits by the verifier's own layout of it
  `headLookupAt`, `headLookupOf`   the lookup's point and its calls' key points, of the challenges
                   heard before the sub-protocol began
  `headAskOf`      the small input, of these numbers, a request, a token, a reader of cells and
                   the weights
  `headLookStep`, `headOwnStep`, `headLookNumbers`, `headBaseOf`, `headWhereOf`   the numbers at the
                   proof file's description
  `headWit'`       the small input, made of the prover's input through the two readers that all
                   sub-protocols share (`Cells`, `Weights`: Honest/ForKinds.lean), in the form in
                   which the lot's honest side takes it (`headLot`, Honest/K6/Part.lean)
  `headFitsOn`, `headFits`, `headFitsB`   WHETHER THE PUBLIC NUMBERS FIT: named tests with code
  `headCalls_keys`, `headFitsB_look`   two small theorems on these tests
  `headLotAt`      THE LOT's HONEST SIDE WITH NOTHING LEFT OPEN BUT THE TWO SHARED READERS:
                   `headLot` at `headFitsB` and `headWit'`; `headLotAt_fit`, `headLotAt_unfit`: what
                   it lays
  `headInstFits`   whether the instance's public part fits
  `headWitLinesOn`, `headWitLines`   the public numbers and each test's answer, as lines of text

Where a cell lies. A row of a committed matrix is not a position and a column is not a feature. The
cell of feature f at position t lies, in a matrix whose columns hold fc features, in row
(f mod fc) T + t of column f / fc, counted across the matrix's parts. That rule is not written here
a second time: `OnBytes.Road.Hd.cellsH` (Johnson/Road/HeadPlace.lean) has it, with the numbers of
the four matrices in the plan's list and with the place of the stream's limbs in the borrowed
matrix. Here it is handed the matrices as the witness's reader yields them. A matrix's name is the
plan's own (`OnBytes.Model.Head.matsH`): "hf0", "hf1", ... for the parts of the wide matrix, "hd",
"hr", "bH", "xbL".

From the field to the integers. A committed cell is an element of the base field; the laws on the
verifier's text speak of integer cells. A cell is read as the integer of least absolute value that
the field reads as it (`ZMod.valMinAbs`).

Where a weight lies. The verifier never reads an entry of the committed matrix of the weights'
digits: it makes a claim on the matrix's last unit, with a factor on the group of indices "x" (the
vocabulary entry) and one on the group "kk" (the coordinate) (`weightsClaim`,
OnBytes/Model/Head.lean). In which cell digit q of the weight with given indices lies, by the
verifier's layout, is written in `OnBytes.Road.cellOf` (Johnson/Road/FormsKeysWm.lean), at every
size. Here each digit is read there as an integer, and the weight is the digits' sum to the base
256, as the library's layout reads it (`Inst.Model.Layout.entry`). That file's own `wgtOf` makes
the same sum in a field; a test below holds the two against each other.

What is read of what. Of the witness: cells of the head's segment alone, through the reader. Of the
index: the head's weights alone: the digits in the last unit's rows, through the reader of the
matrix. Of the instance: the request's words and the token that is asked about, by the functions by
which the verifier's text reads them off its state (`Head.requestOf` at `startS`; `Reply.tokOf`). Of
the index committer's coins: nothing.
NO ROUND OF THE SUB-PROTOCOL READS A CELL OF THE WIDE MATRIX: what the parts send
(Johnson/Desc/K6/Honest/Tables.lean) is made of `stream`, `cell .act`, `cell .row` and `Wh`: a
reading of that file; no test here holds it. The wide matrix is laid all the same, so that the whole
of the cells is the letter of which the library's laws on the head speak.

Limits.
  - `headTensorOf` is 0 where the layout's last unit is not of the head's kind, has a group of
    another name than "x" and "kk", or an index is beyond its group: nothing refuses there; the test
    "the weights' unit" of `headFitsOn` says no at such a layout. A digit that is no signed byte is
    read as some integer all the same. By the head of `cellOf`'s file, that it is the library's
    place of a weight's digit is shown in other files: none of them is called here; one test below
    holds it against the library's written band of rows at the full size's numbers.
  - No test here holds a matrix's name or the segment's number against a witness's reader. By a
    reading of that reader's definitions: it answers to the
    plan's names, part by part ("hf0", "hf1", ...; rows and columns counted inside the part), it
    yields 0 at "hf", and it answers for the borrowed matrix under the borrower's segment and name.
    `Cells` (Honest/ForKinds.lean) asks for the same: the name as the verifier's own plan lays it,
    and the part's name where the plan cuts a matrix in parts. A name that a reader does not know
    reads whatever it yields, in silence.
  - The segment's number is the last link's. By the same word that is the reader's count wherever
    each group of layers has both its segments (24 at the full size), and no count for a shape
    without attention segments, for which there is no trace.
  - A cell that is not small is read as some integer all the same: nothing refuses.
  - SIX SHAPES THAT DO NOT FIT, AT WHICH THE MAKERS YIELD SOME VALUE IN SILENCE. Each has a named
    test in `headFitsOn`, which says no there; THE MAKERS THEMSELVES DO NOT ASK THE TESTS: whoever
    seats them does. (1) A feature beyond a matrix's last is read in the list's next matrix ("the
    features have room"). (2) The library's terms on the stream sum five limbs (`str`, `wsqZ`:
    Kinds/HeadNormLaw.lean); at four limbs a value, limb 4 is read beyond the stream's tensor ("the
    laid numbers: limbs"). (3) A matrix with fewer rows than there are positions has columns that
    hold no feature: the rule then divides by 0, which yields 0 ("every matrix has a row for each
    position"). (4) Where the description has no shape for the head's lookup on its calls, or the
    table of steps has no step of the name, `look` is none and both points are empty ("a lookup is
    named"). (5) Key points of other lengths than the verifier's text asks of its own (`given`,
    Johnson/Desc/Kinds/HeadFrame.lean) ("the key points' lengths"). (6) A number of rounds in front
    of the lookup, or a count of the lookup's rounds, that parts from the plan's table of steps: the
    points are then made of other rounds' challenges, or of 0 where a round is not yet heard, at the
    right lengths ("the lookup's rounds end where the sub-protocol's begin").
  - At a request that fails the state's own test on the request's words, `startS` is the blank
    state (Johnson/Desc/ProofFile/Pub.lean): every token is then 0 and the two positions are 0, in
    silence; `headInstFits` says no there. Such a request has no trace.
  - No coin is laid or read anywhere in this file: what it yields in silence at a shape that does
    not fit are cells, weights and points.
  - That the lookup's rounds begin at the step with the name of the last link and ".2.call" is read
    off the written table of the full size (Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean). No test
    holds the number of rounds against the description's own blocks.
  - That the points are those of the verifier's hearing is no matter of this file
    (Honest/K3/Heard.lean says what is shown of it).
  - The tests below try `headCellsOf`, `headTensorOf`, `headLookupOf`, `headAskOf`, `headFitsOn` and
    `headWitLinesOn` at small made-up numbers. `headLookNumbers`, `headBaseOf`, `headWhereOf`,
    `headWit'`, `headFits`, `headFitsB`, `headInstFits` and `headWitLines` want a description's
    public part: NO TEST HERE TRIES THEM.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.K6.Ask
import Johnson.Desc.ProofFile.Honest.K6.Part
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.First.Look.LookKind
import Johnson.Stored.HeadSeatAt
import Johnson.Road.HeadPlace
import Johnson.Road.FormsKeysWm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E)
open VerifiableInference.Desc.Kinds (Point Head.Request Head.Law.NCells)

variable {W₀ Rc Tr : Type}

/-! ## 1 Where the cells lie and where the lookup's challenges stand -/

/-- **The public numbers that the small input's maker reads.** -/
structure HeadWhere where
  /-- the number of the head's segment, as the witness's reader counts -/
  seg : Nat
  /-- the head's public numbers: of them the number of positions, the width and the number of parts
  of the wide matrix are read -/
  shape : OnBytes.Model.Head.Shape
  /-- the layout of the head's matrices: rows and columns of each -/
  lay : OnBytes.Model.Head.HL
  /-- where the stream's limbs lie in the matrix that the head borrows -/
  border : OnBytes.Model.Head.Border
  /-- the shape of the head's lookup on its calls, and the number of the first chain's rounds in
  front of that lookup; none where the description has none -/
  look : Option (OnBytes.Model.Forest.Shape × Nat)
  /-- the number of the first chain's rounds in front of the sub-protocol's own rounds; no maker
  reads it: it is there for the test that the lookup's rounds end where these begin -/
  own : Option Nat := none

/-- The names of the matrices of the head's segment, in the order of the plan's own list. That
list's two last arguments are identifiers, which no name reads. -/
def headMatNames (N : HeadWhere) : Array String :=
  (OnBytes.Model.Head.matsH N.shape N.lay N.border 0 0).map (·.name)

/-- **The matrices of the head's segment**, by number in the plan's list, row and column: read
through the witness's reader. A number beyond the list reads under the empty name. -/
def headMats (N : HeadWhere) (c : Cells) : OnBytes.Road.Mats Cb.Gl.F :=
  let names := headMatNames N
  fun n r k => c.cell N.seg (names.getD n "") r k

/-- **The cells as integers**, by matrix, feature and position, and the head's weights. Wh: the
weights, by coordinate and vocabulary entry. In the stream limb l of coordinate k is feature
l d + k. -/
def headCellsOf (N : HeadWhere) (c : Cells) (Wh : Nat → Nat → Int) : Head.Law.NCells :=
  let C := (OnBytes.Road.Hd.cellsH N.shape N.lay N.border (headMats N c)).map
    (ZMod.valMinAbs : Cb.Gl.F → Int)
  { cell := fun
      | .wide => C.hf
      | .act => C.hd
      | .row => C.hr
    Wh := Wh
    stream := C.x }

/-! ## 2 The head's weights, off the matrix of all committed weights' digits -/

/-- The indices of the weight at coordinate k and vocabulary entry v, one for each group of a unit,
in the unit's order: the groups are picked by name, as the verifier's text picks a claim's factors.
-/
def headWeightIdx (u : OnBytes.Model.WsUnit) (k v : Nat) : List Nat :=
  u.g.map fun g => if g.name == "x" then v else if g.name == "kk" then k else 0

/-- Every group of the unit is one of the two, and each index is below its group's number. -/
def headWeightIn (u : OnBytes.Model.WsUnit) (k v : Nat) : Bool :=
  u.g.all fun g =>
    if g.name == "x" then decide (v < g.R) else if g.name == "kk" then decide (k < g.R) else false

/-- **The head's weights as a tensor**, by coordinate and vocabulary entry: read in the last unit
of the verifier's layout of the matrix, which must be of the head's kind (13): the weight's digits,
each as the integer of least absolute value, summed to the base 256. 0 elsewhere. -/
def headTensorOf (lay : OnBytes.Model.WsLay) (w : Weights) (k v : Nat) : Int :=
  match lay.U.back? with
  | some u =>
    if u.X == 13 && headWeightIn u k v then
      VerifiableInference.Desc.Kinds.Head.Law.sumZ u.nlw fun q =>
        let at_ := OnBytes.Road.cellOf u q (headWeightIdx u k v)
        256 ^ q * (ZMod.valMinAbs (w.entry at_.1 at_.2) : Int)
    else 0
  | none => 0

/-! ## 3 What comes in from the lookup -/

/-- The lookup's point and each call's key point, as the verifier's text takes them off its state
(Johnson/Stored/HeadSeatAt.lean: `seatAt`, the field lookup), here of the challenges heard. h: the
lookup's shape. base: the number of the chain's rounds in front of the lookup. front: the chain's
challenges from its first round on. A call beyond the shape's has the empty point. -/
def headLookupAt (h : OnBytes.Model.Forest.Shape) (base : Nat) (front : List Fmt.Drawn) :
    Point × (Nat → Point) :=
  let k := K3.keyPtsAt h base front
  (k.zx, fun c => k.zk.getD c #[])

/-- The same at the public numbers; empty points where they name no lookup. -/
def headLookupOf (N : HeadWhere) (front : List Fmt.Drawn) : Point × (Nat → Point) :=
  match N.look with
  | some x => headLookupAt x.1 x.2 front
  | none => (#[], fun _ => #[])

/-! ## 4 The small input -/

/-- **The small input**, of the public numbers, the request's public part, the next token, the
witness's reader and the head's weights. -/
def headAskOf (N : HeadWhere) (request : Head.Request) (y : Nat) (c : Cells)
    (Wh : Nat → Nat → Int) : HeadAsk :=
  { request, y, cells := headCellsOf N c Wh, lookup := headLookupOf N }

/-! ## 5 At the proof file's description -/

/-- The name, in the table of steps, of the step in which the verifier hears a head's lookup on its
calls. link: the link's name. The library names the step of the piece in front in the same way (the
link's name and ".1.call": `headBefore`, Johnson/Desc/ProofFile/Lot/K6K7.lean). -/
def headLookStep (link : String) : String := link ++ ".2.call"

/-- The like for the step in which the verifier hears the sub-protocol's own rounds. -/
def headOwnStep (link : String) : String := link ++ ".3.call"

/-- The shape of the head's lookup on its calls, as the description's own parameters fix it, and
the number of the first chain's rounds in front of the step in which the verifier hears that lookup.
None if there is no link, no such lookup, no shape, or no step of the name. -/
def headLookNumbers (Z : Pub) (G : Ground) : Option (OnBytes.Model.Forest.Shape × Nat) := do
  let X ← G.built.back?
  let p ← VerifiableInference.Desc.First.Look.placeAt G.W (G.built.size - 1) false
  let h ← p.shape
  let base ← Z.roundsBefore? (headLookStep X.name)
  pure (h, base)

/-- The second of these numbers by itself: how many rounds of the first chain stand in front of the
head's lookup on its calls, by the plan's table of steps. For whoever holds it against the
description's own list of blocks (`roundsInFront`, Honest/ForKinds.lean, at that lookup's place): a
lot's honest side is handed no such list. -/
def headBaseOf (Z : Pub) (G : Ground) : Option Nat := (headLookNumbers Z G).map (·.2)

/-- **The public numbers at the proof file's description**: the head's segment is the last link. -/
def headWhereOf (Z : Pub) (G : Ground) : HeadWhere :=
  { seg := G.built.size - 1, shape := G.W.hS, lay := G.W.HLy
    border := OnBytes.Model.Verify.borderOf G.W.y, look := headLookNumbers Z G
    own := G.built.back?.bind fun X => Z.roundsBefore? (headOwnStep X.name) }

/-- **The small input, made of the prover's input through the two shared readers.** cells: the
witness's reader. weights: the reader of the matrix of all committed weights' digits. The layout of
that matrix is the one that the verifier makes of the public files, on which its text makes its
claim. The request is read off the first chain's first state, as the verifier's text reads it; the
token is the one that the instance asks about, which the sub-protocol "the next token" sends. -/
def headWit' (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground)
    (w : Local W₀ Rc Inst Tr) : HeadAsk :=
  headAskOf (headWhereOf Z G)
    (VerifiableInference.Desc.Kinds.Head.requestOf (startS Z w.x.pub))
    (OnBytes.Desc.Reply.tokOf w.x.asked) (cells w.trace)
    (headTensorOf G.W.layers.wsLay (weights w.w₀))

/-! ## 6 Whether the public numbers fit

The makers above yield some value at every choice of public numbers. At which choices that value is
what the sub-protocol's text means is said here: named tests with code, on public numbers alone.
They are a premise for whoever seats the makers; no maker asks them. -/

/-- The library's own named tests on the numbers as they are laid
(Johnson/Desc/Kinds/HeadLaid.lean), at the numbers at which the seated block asks them (`laidOk`,
Johnson/Stored/HeadSeatAt.lean). -/
def headLaidTests (N : HeadWhere) : List (String × Bool) :=
  let _ := (VerifiableInference.Desc.Kinds.Head.parOf N.shape 0).sizes
  let _ := (VerifiableInference.Desc.Kinds.Head.parOf N.shape 0).policy
  (VerifiableInference.Desc.Kinds.Head.laidAt N.shape N.border).tests

/-- Each of the four matrices that are read has a row for each position, and a column. The wide
matrix is asked only where it has a part (an idle leniency: without a part it has no room, and the
next test says no). THIS TEST NEVER SAYS NO ALONE: a matrix with fewer rows than positions holds no
feature, so the test on room, or one of the library's tests on the laid numbers, says no too: it
names the silence and adds no refusal. That is a reckoning on paper: no theorem here says it. -/
def headRowsFit (N : HeadWhere) : Bool :=
  let ok := fun (m k : Nat) => decide (N.shape.T ≤ m) && k != 0
  (N.shape.NHf == 0 || ok N.lay.m N.lay.k) && ok N.lay.mD N.lay.kD && ok N.lay.mR N.lay.kR &&
    ok N.border.mxb N.border.kxb

/-- Each of the head's own three matrices holds as many features as the verifier's text reads of it
(`readsNeed`, Johnson/Stored/HeadSeatAt.lean; of the wide matrix it counts blocks). The stream's
room is among the library's tests on the laid numbers ("stream"): in blocks, rounded down: where a
block's size does not divide five times the width, the last features are not counted. A name that
`readsNeed` does not have counts as 0: among the tests at the file's end, the three at which one of
kR, kD and k is too small say no only if the name is found. -/
def headRoomFits (N : HeadWhere) : Bool :=
  let need := fun (n : String) =>
    ((VerifiableInference.Desc.Kinds.Head.readsNeed N.shape).lookup n).getD 0
  let T := N.shape.T
  decide (need "hf@Z" * N.shape.S2 ≤ N.shape.NHf * N.lay.k * (N.lay.m / T)) &&
    decide (need "hd@zt_FC" ≤ N.lay.kD * (N.lay.mD / T)) &&
    decide (need "hr@zt_ROW" ≤ N.lay.kR * (N.lay.mR / T))

/-- The layout's last unit is the head's: of kind 13, two digits a weight, the group "x" over the
vocabulary and the group "kk" over the coordinates, in this order. -/
def headUnitFits (lay : OnBytes.Model.WsLay) (h : OnBytes.Model.Head.Shape) : Bool :=
  match lay.U.back? with
  | some u =>
    u.X == 13 && u.nlw == 2 && u.g.map (fun g => (g.name, g.R)) == [("x", h.V), ("kk", h.d)]
  | none => false

/-- A list of challenges in which round number i draws the one element i + 1. -/
def headLabels (rounds : Nat) : List Fmt.Drawn :=
  (List.range rounds).map fun i => ⟨[((i + 1).toUInt64, 0, 0)], [], [], none⟩

/-- How many rounds a lookup of a shape has, by the lookup's honest side's own list of stages. -/
def headLookRounds (h : OnBytes.Model.Forest.Shape) : Nat :=
  let f := VerifiableInference.Desc.K3.faceOf h
  ((K3.stages f).map (K3.Stage.rounds f)).sum

/-- The keys of the calls in what the verifier's text makes of the lookup's points are the written
list's, whatever the points. -/
theorem headCalls_keys [VerifiableInference.Desc.Kinds.Head.Sizes] (floor : Nat) (zx : Point)
    (zk : Nat → Point) :
    (VerifiableInference.Desc.Kinds.Head.fromLookup floor zx zk).calls.map (·.2) =
      VerifiableInference.Desc.Kinds.Head.callList := rfl

/-- What the verifier's text asks of its own points (`given`, Johnson/Desc/Kinds/HeadFrame.lean:
its third test), WRITTEN HERE A SECOND TIME and asked of the points that `headLookupOf` makes of
labelled challenges: each of the six calls' key points has the call's column coordinates and one
for each bit of a position, and ends as the lookup's point ends. `given` takes each call's keys off
what it makes of the points; here they are taken off the written list, which spares the weights of
all columns: `headCalls_keys` says that the two lists of keys are one. The lengths hang on the
shapes alone. The second half is met by the make of the key points wherever a tree has at least as
many key bits as a block's row has bits. -/
def headPointsFit (N : HeadWhere) : Bool :=
  match N.look with
  | none => false
  | some x =>
    let p := VerifiableInference.Desc.Kinds.Head.parOf N.shape 0
    let _ := p.sizes
    let z := headLookupAt x.1 x.2 (headLabels (x.2 + headLookRounds x.1))
    let n := VerifiableInference.Desc.Kinds.Norm.ls + VerifiableInference.Desc.Kinds.Norm.lt
    VerifiableInference.Desc.Kinds.Head.callList.zipIdx.all fun c =>
      (z.2 c.2).size == VerifiableInference.Desc.Kinds.Head.lJ p.floor c.1 +
          VerifiableInference.Desc.Kinds.Norm.lt &&
        (z.2 c.2).last n == z.1.last n

/-- The lookup's rounds, counted by its honest side's own list of stages from the number of rounds
in front of it, end where the sub-protocol's own rounds begin by the plan's table of steps. -/
def headEndsFit (N : HeadWhere) : Bool :=
  match N.look, N.own with
  | some x, some n => n == x.2 + headLookRounds x.1
  | _, _ => false

/-- **WHETHER THE PUBLIC NUMBERS FIT**: the tests, each under its name. lay: the verifier's layout
of the matrix of all committed weights' digits. Of the library's seventeen, "block's logarithm" is
true by definition at these numbers, as that file says. -/
def headFitsOn (N : HeadWhere) (lay : OnBytes.Model.WsLay) : List (String × Bool) :=
  ("a lookup is named", N.look.isSome) ::
    ((headLaidTests N).map (fun t => ("the laid numbers: " ++ t.1, t.2)) ++
      [("every matrix has a row for each position", headRowsFit N),
       ("the features have room", headRoomFits N),
       ("the weights' unit", headUnitFits lay N.shape),
       ("the key points' lengths", headPointsFit N),
       ("the lookup's rounds end where the sub-protocol's begin", headEndsFit N)])

/-- The tests at the proof file's description. -/
def headFits (Z : Pub) (G : Ground) : List (String × Bool) :=
  headFitsOn (headWhereOf Z G) G.W.layers.wsLay

/-- **THE NAMED PUBLIC PREMISE**: all of them say yes. -/
def headFitsB (Z : Pub) (G : Ground) : Bool := (headFits Z G).all (·.2)

/-- Under the premise a lookup is named: the arm of `headLookupOf` that yields empty points is not
met. -/
theorem headFitsB_look (Z : Pub) (G : Ground) (h : headFitsB Z G = true) :
    (headWhereOf Z G).look.isSome = true := by
  unfold headFitsB headFits headFitsOn at h
  simp only [List.all_cons, Bool.and_eq_true] at h
  exact h.1

-- the tests on the laid numbers are, at the description, those that the seated block asks
example (Z : Pub) (G : Ground) :
    (headLaidTests (headWhereOf Z G)).all (·.2) =
      VerifiableInference.Desc.Kinds.Head.laidOk G.W := rfl

#print axioms headCalls_keys
#print axioms headFitsB_look

/-- **Whether the instance's public part fits**: the state's own test on the request's words, as the
seated block asks it in front of its decision (`startOk`, Johnson/Stored/HeadSeatAt.lean), at the
first chain's first state; and the token that is asked about is an entry of the vocabulary. It is a
premise on the instance, not on the public part: a lot's honest side cannot ask it. -/
def headInstFits (Z : Pub) (G : Ground) (x : Inst) : Bool :=
  VerifiableInference.Desc.Kinds.Head.startOk G.W (startS Z x.pub) &&
    decide (OnBytes.Desc.Reply.tokOf x.asked < G.W.hS.V)

/-- The public numbers that the makers read, and each test's answer, as lines of text. -/
def headWitLinesOn (N : HeadWhere) (lay : OnBytes.Model.WsLay) : List String :=
  [s!"the head's segment: {N.seg}", s!"its matrices: {headMatNames N}",
   match N.look with
   | some x =>
     s!"the lookup on the calls: dT {x.1.dT} · rK {x.1.rK} · calls {x.1.NC} · iota {x.1.iota} · " ++
       s!"rounds in front {x.2} · its rounds {headLookRounds x.1}"
   | none => "the lookup on the calls: none",
   s!"rounds in front of the sub-protocol's own: {N.own}",
   match lay.U.back? with
   | some u =>
     s!"the weights' last unit: kind {u.X} · digits {u.nlw} · first row {u.off} · " ++
       s!"rows {u.rows} · groups {u.g.map fun g => (g.name, g.R)}"
   | none => "the weights' last unit: none"] ++
    (headFitsOn N lay).map fun t => s!"fits: {t.1}: {if t.2 then "yes" else "NO"}"

/-- The same at the proof file's description. -/
def headWitLines (Z : Pub) (G : Ground) : List String :=
  headWitLinesOn (headWhereOf Z G) G.W.layers.wsLay

/-- **THE LOT's HONEST SIDE, WITH NOTHING LEFT OPEN BUT THE TWO SHARED READERS**: the one name to
seat. It lays a half only where the public numbers fit. -/
def headLotAt {X : Type} (cells : Tr → Cells) (weights : W₀ → Weights) :
    HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  headLot headFitsB (headWit' cells weights)

/-- Where the public numbers fit: one half for each block that the lot seats. -/
theorem headLotAt_fit {X : Type} (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub)
    (G : Ground) (h : headFitsB Z G = true) :
    (headLotAt (Rc := Rc) (X := X) cells weights).halves Z G =
      (P4.k6Hear Z G).map fun b =>
        ⟨b.place, headRow (headWit' cells weights Z G) (headParAt G) b.place⟩ :=
  if_pos h

/-- Where they do not: none. -/
theorem headLotAt_unfit {X : Type} (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub)
    (G : Ground) (h : headFitsB Z G = false) :
    (headLotAt (Rc := Rc) (X := X) cells weights).halves Z G = [] :=
  if_neg (by rw [h]; exact Bool.false_ne_true)

#print axioms headLotAt_fit
#print axioms headLotAt_unfit

/-! ## 7 Tests at small made-up numbers

Four positions; width 6; the wide matrix in two parts of 8 rows and 3 columns (2 features a column);
"hd" with 16 rows (4 features a column); "hr" with 8 rows (2 a column); the borrowed matrix with 8
rows (2 a column), in which limb l of coordinate j is feature 3 + 12 l + j. The places below are
reckoned by hand from the rule in this file's head. -/

/-- The made-up numbers. The segment's number is 7. -/
def headToyWhere : HeadWhere :=
  { seg := 7
    shape := { (default : OnBytes.Model.Head.Shape) with lt := 2, d := 6, NHf := 2 }
    lay := { k := 3, m := 8, kD := 4, mD := 16, kR := 5, mR := 8 }
    border := { mxb := 8, kxb := 20, off := 3, nl := 5, cnt := 2, J := 6 }
    look := none }

/-- An integer as an element of the base field. -/
def headToyF (z : Int) : Cb.Gl.F :=
  if 0 ≤ z then OnBytes.Slice.toF z.toNat.toUInt64
  else OnBytes.Slice.toF (Code.pGold - z.natAbs).toUInt64

/-- A witness's reader with one cell that is not 0. -/
def headToyProbe (seg : Nat) (name : String) (row column : Nat) (v : Int) : Cells :=
  ⟨fun s n r k =>
    if s == seg && n == name && r == row && k == column then headToyF v else headToyF 0⟩

/-- All (feature, position, value) with a value that is not 0, at the features below a bound and the
four positions. -/
def headToyHits (f : Nat → Nat → Int) (features : Nat) : List (Nat × Nat × Int) :=
  (List.range features).flatMap fun a => (List.range 4).filterMap fun t =>
    if f a t == 0 then none else some (a, t, f a t)

/-- The cells at the made-up numbers and a reader; every weight 0. -/
def headToyCells (c : Cells) : Head.Law.NCells := headCellsOf headToyWhere c fun _ _ => 0

-- the names, in the plan's order
#guard headMatNames headToyWhere == #["hf0", "hf1", "hd", "hr", "bH", "xbL"]
-- the balanced residue evaluates at the field's size: a negative cell comes back negative
#guard (ZMod.valMinAbs (headToyF (-1)) : Int) == -1
#guard (ZMod.valMinAbs (headToyF (-128)) : Int) == -128
#guard (ZMod.valMinAbs (headToyF 127) : Int) == 127
#guard (ZMod.valMinAbs (headToyF 0) : Int) == 0
-- "hd", row 6, column 2: feature 2 * 4 + 1 = 9 at position 2, and no other cell of any matrix
#guard headToyHits ((headToyCells (headToyProbe 7 "hd" 6 2 (-5))).cell .act) 16 == [(9, 2, -5)]
#guard headToyHits ((headToyCells (headToyProbe 7 "hd" 6 2 (-5))).cell .row) 10 == []
#guard headToyHits ((headToyCells (headToyProbe 7 "hd" 6 2 (-5))).cell .wide) 12 == []
#guard headToyHits (headToyCells (headToyProbe 7 "hd" 6 2 (-5))).stream 30 == []
-- "hr", row 5, column 3: feature 3 * 2 + 1 = 7 at position 1
#guard headToyHits ((headToyCells (headToyProbe 7 "hr" 5 3 100)).cell .row) 10 == [(7, 1, 100)]
-- the wide matrix's second part, row 4, column 2: column 3 + 2 = 5 of the whole: feature 11 at
-- position 0; the same place in the first part: feature 5
#guard headToyHits ((headToyCells (headToyProbe 7 "hf1" 4 2 9)).cell .wide) 12 == [(11, 0, 9)]
#guard headToyHits ((headToyCells (headToyProbe 7 "hf0" 4 2 9)).cell .wide) 12 == [(5, 0, 9)]
-- the borrowed matrix, row 7, column 15: its feature 31 = 3 + 12 * 2 + 4 at position 3: limb 2 of
-- coordinate 4: feature 2 * 6 + 4 = 16 of the stream
#guard headToyHits (headToyCells (headToyProbe 7 "xbL" 7 15 (-77))).stream 30 == [(16, 3, -77)]
-- its features 0 to 2 and 9 to 14 hold no limb of the stream's first layer
#guard headToyHits (headToyCells (headToyProbe 7 "xbL" 4 0 1)).stream 30 == []
#guard headToyHits (headToyCells (headToyProbe 7 "xbL" 4 5 1)).stream 30 == []
-- another segment, another name: nothing is read
#guard headToyHits ((headToyCells (headToyProbe 6 "hd" 6 2 (-5))).cell .act) 16 == []
#guard headToyHits ((headToyCells (headToyProbe 7 "bH" 6 2 (-5))).cell .act) 16 == []
-- the library's terms on these cells, at the sizes of the same numbers: feature 9 = 6 + 3 is the
-- second limb of the activation of coordinate 3: 256 * (-5); limb 2 of the stream's coordinate 4:
-- 256 ^ 2 * (-77); a digit is its cell and 128
#guard
  let _ := VerifiableInference.Desc.Kinds.Head.sizesOf headToyWhere.shape
  VerifiableInference.Desc.Kinds.Head.Law.act
    (headToyCells (headToyProbe 7 "hd" 6 2 (-5))).toCells 2 3 == -1280
#guard
  let _ := VerifiableInference.Desc.Kinds.Head.sizesOf headToyWhere.shape
  VerifiableInference.Desc.Kinds.Head.Law.str
    (headToyCells (headToyProbe 7 "xbL" 7 15 (-77))) 3 4 == -5046272
#guard VerifiableInference.Desc.Kinds.Head.Law.digZ
  (headToyCells (headToyProbe 7 "hr" 5 3 100)) 1 7 == 228

/-! ### The weights

A matrix with 2 ^ 4 columns; vocabulary 5, width 6. The verifier's own maker of a layout lays first
a unit of the embedding's kind (12 rows), then the head's: the vocabulary entry takes the column
bits 0 to 2, the coordinate's lowest bit takes bit 3, the rest of the coordinate (3 values) and the
digit's number go to the rows. So digit q of the weight at (k, v) lies in row 12 + 3 q + k / 2 and
column v + 8 (k mod 2): reckoned by hand from the layout's text. -/

/-- The made-up layout; empty if the maker refuses. -/
def headToyLay : OnBytes.Model.WsLay :=
  match (OnBytes.Model.WsLay.add { lk := 4 } 12 0 4
      [OnBytes.Model.WsLay.A_ "v" 5, OnBytes.Model.WsLay.E_ "x" 6 true]).bind fun a =>
    a.add 13 0 2 [OnBytes.Model.WsLay.A_ "x" 5, OnBytes.Model.WsLay.E_ "kk" 6 false] with
  | .ok a => a
  | .error _ => {}

/-- A matrix of digits with the listed entries (row, column, value), and 0 elsewhere. -/
def headToyDigits (l : List (Nat × Nat × Int)) : Weights :=
  ⟨fun r c => headToyF (((l.find? fun x => x.1 == r && x.2.1 == c).map (·.2.2)).getD 0)⟩

/-- All (coordinate, vocabulary entry, weight) with a weight that is not 0, below two bounds. -/
def headToyWeights (f : Nat → Nat → Int) (ks vs : Nat) : List (Nat × Nat × Int) :=
  (List.range ks).flatMap fun k => (List.range vs).filterMap fun v =>
    if f k v == 0 then none else some (k, v, f k v)

#guard headToyLay.U.size == 2 && headToyLay.m0 == 18
#guard (headToyLay.U.back?.map fun u => (u.X, u.off, u.rows)) == some (13, 12, 6)
-- the weight at coordinate 5 and entry 4: digit 0 in row 14, digit 1 in row 17, column 12
#guard headToyWeights (headTensorOf headToyLay (headToyDigits [(14, 12, -7)])) 8 8 == [(5, 4, -7)]
#guard headToyWeights (headTensorOf headToyLay (headToyDigits [(17, 12, -3)])) 8 8 ==
  [(5, 4, -768)]
#guard headToyWeights (headTensorOf headToyLay (headToyDigits [(14, 12, -7), (17, 12, -3)])) 8 8 ==
  [(5, 4, -775)]
-- coordinate 0, entry 0: the unit's first row; coordinate 2, entry 3: row 13, column 3
#guard headToyWeights (headTensorOf headToyLay (headToyDigits [(12, 0, 1), (13, 3, 2)])) 8 8 ==
  [(0, 0, 1), (2, 3, 2)]
-- a row of the unit in front; a column that stands for no vocabulary entry: no weight
#guard headToyWeights (headTensorOf headToyLay (headToyDigits [(5, 12, 9)])) 8 8 == []
#guard headToyWeights (headTensorOf headToyLay (headToyDigits [(14, 13, 9), (14, 7, 9)])) 8 8 == []
-- a layout whose last unit is not of the head's kind; an empty layout: no weight
#guard headToyWeights (headTensorOf { headToyLay with U := headToyLay.U.pop }
  (headToyDigits [(5, 12, 9), (14, 12, -7)])) 8 8 == []
#guard headToyWeights (headTensorOf {} (headToyDigits [(14, 12, -7)])) 8 8 == []
-- the sum in the field, by the function that stands beside the cells' rule, read back as an integer
#guard (headToyLay.U.back?.map fun u =>
  (ZMod.valMinAbs (OnBytes.Road.wgtOf u (headToyDigits [(14, 12, -7), (17, 12, -3)]).entry
    (headWeightIdx u 5 4)) : Int)) == some (-775)
-- at the full size's numbers (2 ^ 18 columns, vocabulary 202,048, width 5,120, 3,065,840 rows in
-- front): the library's written band: digit q of the weight at (k, v) in row
-- 3,065,840 + 5,120 q + k, column v (Johnson/Desc/Kinds/Law/WhBand.lean)
#guard
  match OnBytes.Model.WsLay.add { lk := 18, m0 := 3065840 } 13 48 2
    [OnBytes.Model.WsLay.A_ "x" 202048, OnBytes.Model.WsLay.E_ "kk" 5120 false] with
  | .ok a =>
    headTensorOf a (headToyDigits [(3070959, 202047, 5), (3076079, 202047, -2)]) 5119 202047 ==
        -507 &&
      headTensorOf a (headToyDigits [(3070959, 202047, 5)]) 5118 202047 == 0
  | .error _ => false

/-- A made-up shape of a lookup: trees of 2 ^ 10 keys, two bits for a tree's number, two calls, of
two trees and of one. -/
def headToyLook : OnBytes.Model.Forest.Shape :=
  { calls := #[{ n := 11, iota := 1, k := 5, kappa := 5 },
      { n := 10, iota := 0, k := 5, kappa := 5 }]
    dT := 10, kT := 5, NT := 3, rK := 2, NC := 2, cK := 1, iota := #[1, 0], first := #[0, 2]
    callOf := #[0, 0, 1], pub := #[0, 0, 0] }

/-- A number as an element. -/
def headToyE (n : Nat) : E := E.ofTriple (n.toUInt64, 0, 0)

/-- A list of challenges: round number i draws the one element i + shift. -/
def headToyHeard (rounds shift : Nat) : List Fmt.Drawn :=
  (List.range rounds).map fun i => ⟨[((i + shift).toUInt64, 0, 0)], [], [], none⟩

/-- The small input's lookup with three rounds in front of the lookup's. -/
def headToyPoints (front : List Fmt.Drawn) : Point × (Nat → Point) :=
  (headAskOf { headToyWhere with look := some (headToyLook, 3) } ⟨fun _ => 0, 0, 0⟩ 0
    (headToyProbe 0 "" 0 0 0) fun _ _ => 0).lookup front

-- Written, from the numbers of the lookup's rounds: inside the lookup the last key level (11
-- variables) begins at round 195, its variables' rounds are 196 to 206, its last round is 209. With
-- three rounds in front: 199 to 209, and 212. The rounds fix the bits 4 3 2 7 6 5 10 9 8 1 0; the
-- point has the last round's draw first, then bit 10 down to bit 0.
#guard (headToyPoints (headToyHeard 320 0)).1 ==
  #[212, 205, 206, 207, 202, 203, 204, 199, 200, 201].map headToyE
#guard (headToyPoints (headToyHeard 320 0)).2 0 ==
  #[209, 212, 205, 206, 207, 202, 203, 204, 199, 200, 201].map headToyE
#guard (headToyPoints (headToyHeard 320 0)).2 1 ==
  #[212, 205, 206, 207, 202, 203, 204, 199, 200, 201].map headToyE
#guard (headToyPoints (headToyHeard 320 0)).2 2 == #[]
-- it moves with the challenges
#guard (headToyPoints (headToyHeard 320 1000)).1 ==
  #[1212, 1205, 1206, 1207, 1202, 1203, 1204, 1199, 1200, 1201].map headToyE
-- no lookup is named: empty points
#guard (headLookupOf headToyWhere (headToyHeard 320 0)).1 == #[]
#guard (headLookupOf headToyWhere (headToyHeard 320 0)).2 0 == #[]
-- NEAR IDLE: the request, the token and the weights are handed on as they are. What the line can
-- see: the weights' two indices changed over (248 for -5), or the token laid for a position
#guard
  let a := headAskOf headToyWhere ⟨fun i => i + 40, 1, 4⟩ 3 (headToyProbe 0 "" 0 0 0)
    fun k v => 10 * k - v
  (a.request.tok 2, a.request.r, a.request.e, a.y, a.cells.Wh 2 25) == (42, 1, 4, 3, -5)

/-! ### Whether the numbers fit

Made-up numbers at which every test says yes: four positions, blocks of two features, width 6,
vocabulary 6, five limbs, the stream's tensor at the matrix's first feature. The lookup's shape has
trees of 2 ^ 3 keys; the logarithms of the six calls' numbers of trees are written numbers, reckoned
by hand: the calls have 18, 6, 126, 4, 2 and 6 keys a position; the least powers of two that hold
them have the logarithms 5, 3, 7, 2, 1, 3; with the two bits of a position, less the three of a
key's place in its tree: 4, 2, 6, 1, 0, 2. WHAT THIS TOY DOES NOT TRY. Its lookup is no shape that
the lookup's own test on the plan admits (trees of fewer than 2 ^ 10 keys: `orderForestRange`,
OnBytes/Model/Forest.lean): of the key points their lengths alone are tried. The least allowed
logarithm of the number of a call's keys is 0, so the arm of a call's logarithm that rests on it is
not met. The number of rounds in front of the sub-protocol is laid by the very count that the last
test asks: its yes is by make. -/

/-- The head's public numbers. -/
def headFitShape : OnBytes.Model.Head.Shape :=
  { (default : OnBytes.Model.Head.Shape) with
    lt := 2, la := 3, d := 6, lPd := 3, V := 6, XL := 5, digSh := 8, clipC := 128, theta := 128
    NHf := 2 }

/-- A lookup's shape with six calls. bend: added to the third call's logarithm of its number of
trees. -/
def headFitLook (bend : Nat) : OnBytes.Model.Forest.Shape :=
  { dT := 3, kT := 5, rK := 7, NC := 6, cK := 3, iota := #[4, 2, 6 + bend, 1, 0, 2] }

/-- The public numbers; three rounds stand in front of the lookup. -/
def headFitWhere : HeadWhere :=
  { seg := 7, shape := headFitShape
    lay := { k := 15, m := 8, kD := 4, mD := 16, kR := 60, mR := 8 }
    border := { mxb := 8, kxb := 20, off := 0, nl := 5, cnt := 1, J := 6 }
    look := some (headFitLook 0, 3), own := some (3 + headLookRounds (headFitLook 0)) }

/-- A layout with the head's unit alone, by the verifier's own maker; empty if it refuses. -/
def headFitLay : OnBytes.Model.WsLay :=
  match OnBytes.Model.WsLay.add { lk := 4 } 13 0 2
      [OnBytes.Model.WsLay.A_ "x" 6, OnBytes.Model.WsLay.E_ "kk" 6 false] with
  | .ok a => a
  | .error _ => {}

/-- The names of the tests that say no. -/
def headFitFails (N : HeadWhere) (lay : OnBytes.Model.WsLay) : List String :=
  ((headFitsOn N lay).filter (!·.2)).map (·.1)

-- every test says yes: one on the lookup, the library's seventeen, five more
#guard headFitFails headFitWhere headFitLay == []
#guard (headFitsOn headFitWhere headFitLay).length == 23
-- ONE NUMBER BENT AT A TIME: just the tests that are named say no
#guard headFitFails { headFitWhere with look := none } headFitLay ==
  ["a lookup is named", "the key points' lengths",
   "the lookup's rounds end where the sub-protocol's begin"]
#guard headFitFails { headFitWhere with shape := { headFitShape with XL := 4 } } headFitLay ==
  ["the laid numbers: limbs"]
#guard headFitFails { headFitWhere with border := { headFitWhere.border with nl := 4 } }
  headFitLay == ["the laid numbers: the tensor's limbs"]
#guard headFitFails { headFitWhere with border := { headFitWhere.border with off := 3 } }
  headFitLay == ["the laid numbers: origin"]
#guard headFitFails { headFitWhere with lay := { headFitWhere.lay with mD := 2 } } headFitLay ==
  ["every matrix has a row for each position", "the features have room"]
#guard headFitFails { headFitWhere with lay := { headFitWhere.lay with kR := 59 } } headFitLay ==
  ["the features have room"]
#guard headFitFails { headFitWhere with lay := { headFitWhere.lay with kD := 2 } } headFitLay ==
  ["the features have room"]
#guard headFitFails { headFitWhere with lay := { headFitWhere.lay with k := 14 } } headFitLay ==
  ["the features have room"]
#guard headFitFails headFitWhere headToyLay == ["the weights' unit"]
#guard headFitFails headFitWhere {} == ["the weights' unit"]
#guard headFitFails { headFitWhere with look := some (headFitLook 1, 3) } headFitLay ==
  ["the key points' lengths"]
-- one round more in front of the lookup; one more, or none, in front of the sub-protocol: the key
-- points keep their lengths: the last test alone says no
#guard headFitFails { headFitWhere with look := some (headFitLook 0, 4) } headFitLay ==
  ["the lookup's rounds end where the sub-protocol's begin"]
#guard headFitFails { headFitWhere with own := headFitWhere.own.map (· + 1) } headFitLay ==
  ["the lookup's rounds end where the sub-protocol's begin"]
#guard headFitFails { headFitWhere with own := none } headFitLay ==
  ["the lookup's rounds end where the sub-protocol's begin"]
-- the numbers of the tests further up were made to try the rule on a cell's place, not to fit
#guard (headFitFails headToyWhere headToyLay).length != 0
-- the lines of text: five on the numbers, one for each test
#guard (headWitLinesOn headFitWhere headFitLay).length == 28
#guard (headWitLinesOn headFitWhere headFitLay).take 2 ==
  ["the head's segment: 7", "its matrices: #[hf0, hf1, hd, hr, bH, xbL]"]
#guard (headWitLinesOn { headFitWhere with look := none } {}).filter (·.endsWith "none") ==
  ["the lookup on the calls: none", "the weights' last unit: none"]
#guard (headWitLinesOn { headFitWhere with look := none } headFitLay).filter (·.endsWith "NO") ==
  ["fits: a lookup is named: NO", "fits: the key points' lengths: NO",
   "fits: the lookup's rounds end where the sub-protocol's begin: NO"]
-- the small input over the weights' reader: the tensor is handed on
#guard (headAskOf headToyWhere ⟨fun _ => 0, 0, 0⟩ 0 (headToyProbe 0 "" 0 0 0)
  (headTensorOf headToyLay (headToyDigits [(14, 12, -7), (17, 12, -3)]))).cells.Wh 5 4 == -775

end ProofFile.Honest.K6
