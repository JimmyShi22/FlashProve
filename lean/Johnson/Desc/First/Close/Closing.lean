-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Closing.lean: the closing of a link (kind K10), with its two parts: the
batching of the rows on a group (P3) and the fold (P4). Plain functions on data. Definitions alone;
what is proved of them: Johnson/Desc/First/Close/Law/.

ROUNDS. "BAT": nothing is sent; one element x is drawn. "FOLD epsilon": the sum of the hiding
polynomial is sent (behind the fresh mask's root, where the mask comes with it); eps is drawn. k
times "FOLD round": a constant and a quadratic coefficient are sent; g_j is drawn.
READS. Nothing is opened.
DECIDES. All rows of the group become one row, by the powers of x. The first claim is the sum plus
eps times that row's target. In each round the linear coefficient is set so that the round's check
holds, and the claim becomes the round's polynomial at g_j. What goes out is one claim on three
single rows and the kept rows. NO EQUATION IS TESTED: no guard reads an element that was sent or
drawn. Every refusal is about the view's shape, the plan or the state, AND HAS A NAME OF ITS OWN.
SENDS. Written in Lean only where the link proof's proximity test calls both parts (lean/GAPS.md).

Typed after the program `verify-on-bytes` ("the program", OnBytes/Iop/), guard by guard. Of its pure
routines these are called by name, each of which always returns: ioppFoldShape, foldClaimRound,
foldOutput, foldMaskNotice, reqMoments. THE BATCHING AND THE FOLD's THREE TESTS ARE THE
DESCRIPTION's OWN TEXT: Own.batch (Johnson/Desc/Own/Batch.lean), Own.foldShapeFits,
Own.foldMaskFits, Own.foldRowFits (Johnson/Desc/Own/Fold.lean). That each returns what the program's
Bat.combine, foldShapeOk, foldMaskOk, foldRowOk returns, at all arguments: BatchAgree.lean and
FoldAgree.lean, beside them. The effects on the statement are the part "the statement's ground"
(Johnson/Desc/First/Base/Ground.lean): beginRunP, spendAsMaskP, recvP, with their lists of named
clauses.

  `bat`         batVerify (Bat.lean:63-69)
  `foldD`       foldVerify (Fold.lean:374-377), both arms; `fold`: the arm of a link's closing
  `closing`     ReqFrame.close's two calls and the test between them (Req.lean:363-366)
  `closeFrame`  ReqFrame.close whole (Req.lean:359-368), on the frame's record as plain data
  `step`, `row` closeFrame as a step of a chain's decision (Johnson/Desc/Step.lean)
  `stretches`   which entries of the plan each closing takes

THE GUARDS: name · what it asks · the program's line.
 K10.owed      the round closed in front owes no count of rows · Ground.lean:825 (:602), Bat.lean:65
 K10.link      the link's shape is there · Req.lean:360
 K10.group     the link's group's record is there · Req.lean:361
 K10.due       a link is under way and all its moments have come · Req.lean:362
 K10.stretch   the stretch has 2 + k entries and rounds · Ground.lean:822, :839; Fold.lean:351-358
 K10.mask      the link's first message has left a mask · not the program's: at none it takes the
               fold's other arm; at a closing the frame always holds one (Req.lean:342)
 beginRun: …   four clauses of the ground's beginRunL · Ground.lean:1377, :1378, :1378, :1383
 K10.layout    the group has a layout · Ground.lean:1379 (dead behind "the group is there")
 K10.name      the entry has the round's name · Ground.lean:825
 K10.nonzero   it draws no element from the non-zero ones · Ground.lean:825
 K10.entry     it is the entry of a round of elements: one round; 24 bytes an item, 32 a root; roots
               as the caller says; no answer, position or matrix entry · not the program's, whose
               close reads neither bytes nor roots; the C++ channel asks the like
 K10.items     as many items as are taken, each an element · Ground.lean:770, :773, :779-781, :841
 K10.draws     as many draws as the entry says, of three kinds · Ground.lean:841-842
 K10.one       one element is drawn · Ground.lean:870-872
 K10.rows      "BAT" batches as many rows as its entry counts · Bat.lean:66 (Ground.lean:852-857)
 K10.combine   every row names what the layout has: Own.batch returns · Bat.lean:68 (:46)
 K10.kh        the layout's k and h are the plan's · Req.lean:364
 K10.norows    no entry of the fold counts rows, the last included · Ground.lean:825 (:602); at the
               last entry the program refuses one close later
 K10.shape     Own.foldShapeFits · Fold.lean:317 (foldShapeOk :250)
 recv: …       three clauses of the ground's recvL, at no mask · Fold.lean:321
               (Ground.lean:1477-1479)
 K10.entered   the entered mask has a number · Fold.lean:322
 K10.maskfits  Own.foldMaskFits · Fold.lean:323 (foldMaskOk :295)
 spendAsMask: … four clauses of the ground's spendAsMaskL · Fold.lean:324 (Ground.lean:1280-1281)
 K10.rowfits   Own.foldRowFits · Fold.lean:369 (foldRowOk :279)
THE ROWS' ORDER: plain rows as created, each member's sample rows, the members as sent, then the
rows from reads: Ground.lean:1381-1386: the ground's beginRunP.
THE FRAME BEHIND: rows, mask := none, link + 1, next := .first: Req.lean:368.
NOT ASKED HERE. Words below the prime: `heard` lays each element by E.ofTriple, unasked, as the
program's recvE does; that test is the whole view's, at the front of the folds. No message is open
when the stretch begins: a step is handed whole rounds. foldRoundsVerify's five equations between
two shapes (Fold.lean:366-367): here there is one shape. The order of the fold's three calls
(Fold.lean:330, :364): here the order of the text. Notes (Req.lean:365, :367): no test reads one.
`bat`, `foldD` and `closing` do not ask K10.owed: whoever calls one of them at a step's first
close asks it, as closeFrame does.

-/
import OnBytes.Iop.Req
import Johnson.Desc.Step
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Own.Batch
import Johnson.Desc.Own.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes

/-- Refuses under the name unless b. -/
def need (name : String) (b : Bool) : Except String Unit := if b then .ok () else .error name

/-- The value, or a refusal under the name. -/
def got {α : Type} (name : String) (x : Option α) : Except String α :=
  match x with
  | some a => .ok a
  | none => .error name

/-- Refuses under the name of the first clause that does not hold. -/
def named (l : Ground.Clauses) : Except String Unit :=
  match l.find? (!·.2) with
  | some c => .error c.1
  | none => .ok ()

/-- A statement as the ground's carried record: the effects called below read and write of it the
statement alone. -/
def onSt (S : Statement) : _root_.Desc.Plain.DState Unit := ⟨S, {}, 0, [], ()⟩

/-- A round in which the prover sends `items` elements, behind `roots` roots, and the verifier draws
one element: what was sent, and what was drawn. -/
def heard (name : String) (items : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (roots : Nat := 0) :
    Except String (List E × E) := do
  need "K10.name" (e.name == name)
  need "K10.nonzero" (e.drawNZ == 0)
  need "K10.entry" (e.count == 1 && e.msg == 24 * items + 32 * roots && e.roots == roots &&
    e.answers == 0 && e.poss == 0 && e.trits == 0)
  need "K10.items" (r.vals.length == items)
  need "K10.draws" (r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
    r.drawn.trits.length == e.trits)
  let xs ← got "K10.items" (r.vals.mapM fun v =>
    match v with
    | .e x => some (E.ofTriple x)
    | _ => none)
  match r.drawn.elems with
  | [x] => pure (xs, E.ofTriple x)
  | _ => .error "K10.one"

/-- **The batching** (P3). S: the statement. g: the group. e, r: the entry and the round "BAT".
Returns the one row, the group's layout, the statement behind. -/
def bat (S : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) :
    Except String (GroupRow × GroupLayout × Statement) := do
  named (Ground.beginRunL S g)
  let (input, d) ← got "K10.layout" (Ground.beginRunP (onSt S) g)
  let x ← (heard "BAT" 0 e r).map (·.2)
  need "K10.rows" (e.rows == input.rows.size)
  let row ← got "K10.combine" (Own.batch d.st g input x)
  pure (row, input.layout, d.st)

/-- The fold's rounds: the challenges and the running claim behind the last. -/
def rounds : List Fmt.Entry → List Fmt.RoundView → E → Except String (List E × E)
  | [], [], claim => .ok ([], claim)
  | e :: es, r :: rs, claim => do
    match ← heard "FOLD round" 2 e r with
    | ([c0, c2], g) =>
      let x ← rounds es rs (foldClaimRound claim c0 c2 g)
      pure (g :: x.1, x.2)
    | _ => .error "K10.items"
  | _, _, _ => .error "K10.stretch"

/-- **The fold** (P4), whole, on the ground's carried record. F: its shape. row: the row to fold.
mask: the fresh mask's message, if it came in an earlier message; at `none` its root comes in the
fold's own first message and the message is entered here (firstTree: the number of the first tree
that the chain sends). es, rs: the entries and rounds "FOLD epsilon" and k times "FOLD round". -/
def foldD {L : Type} (firstTree : Nat) (d : _root_.Desc.Plain.DState L) (F : FoldShape)
    (row : GroupRow) (mask : Option Nat) (es : List Fmt.Entry) (rs : List Fmt.RoundView) :
    Except String (SingleRows × _root_.Desc.Plain.DState L) :=
  match es, rs with
  | eE :: eR, rE :: rR => do
    need "K10.stretch" (eR.length == F.layout.k && rR.length == F.layout.k)
    need "K10.norows" (es.all (·.rows == 0))
    need "K10.shape" (Own.foldShapeFits d.st F)
    let (id, d1) ← match mask with
      | some id => pure (id, d)
      | none => do
        named (Ground.recvL d.st d.book #[foldMaskNotice F])
        let (ids, d') ← got "K10.entered" (Ground.recvP firstTree d #[foldMaskNotice F])
        pure (← got "K10.entered" ids[0]?, d')
    need "K10.maskfits" (Own.foldMaskFits d1.st F id)
    named (Ground.spendAsMaskL d1.st id)
    let d2 ← got "K10.maskfits" (Ground.spendAsMaskP d1 id)
    match ← heard "FOLD epsilon" 1 eE rE (d1.roots - d.roots) with
    | ([sum], eps) =>
      need "K10.rowfits" (Own.foldRowFits d2.st F row)
      let (gamma, claim) ← rounds eR rR (maddE sum eps row.target)
      pure (foldOutput d2.st F row id eps gamma claim, d2)
    | _ => .error "K10.items"
  | _, _ => .error "K10.stretch"

/-- The fold where the fresh mask came in an earlier message: of the carried record it reads and
writes the statement alone. -/
def fold (S : Statement) (F : FoldShape) (row : GroupRow) (mask : Nat) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) : Except String (SingleRows × Statement) :=
  (foldD 0 (onSt S) F row (some mask) es rs).map fun x => (x.1, x.2.st)

/-- What the plan says of a link's closing: the two codes' numbers, k, h, the 2 + k entries. -/
structure Plan where
  code : Nat
  maskCode : Nat
  k : Nat
  h : Nat
  entries : List Fmt.Entry

/-- **The closing of a link.** S: the statement. g: the link's group. mask: the fresh mask's
message, as the link's first message has left it. rs: the stretch's rounds. -/
def closing (P : Plan) (S : Statement) (g : Nat) (mask : Option Nat) (rs : List Fmt.RoundView) :
    Except String (SingleRows × Statement) :=
  match P.entries, rs with
  | eB :: es, rB :: rs => do
    let mask ← got "K10.mask" mask
    let (row, L, S1) ← bat S g eB rB
    need "K10.kh" (L.k == P.k && L.h == P.h)
    fold S1 (ioppFoldShape { code := P.code, maskCode := P.maskCode, k := P.k, h := P.h } L) row
      mask es rs
  | _, _ => .error "K10.stretch"

/-- **The frame's closing of a link, whole.** owed: the carried state's field "rows owed": the
number of rows that the entry of a round closed earlier counts, until it has been compared. f: the
frame's record, the program's own, as plain data. Behind the closing nothing is owed. -/
def closeFrame (owed : Option Nat) (f : ReqFrame) (S : Statement) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) : Except String (ReqFrame × Statement) := do
  need "K10.owed" owed.isNone
  let L ← got "K10.link" f.shape.link[f.link]?
  let G ← got "K10.group" f.groups[f.link]?
  need "K10.due" (f.next == .laterOrClose && f.moment == reqMoments L)
  let (rows, S') ← closing
    { code := f.shape.code, maskCode := f.shape.maskCode, k := G.k, h := G.h, entries := es } S
    f.group f.mask rs
  pure ({ f with rows := rows, mask := none, link := f.link + 1, next := .first }, S')

/-- The frame's closing as a step of a chain's decision. es: the stretch's entries, a parameter of
whoever makes the table. rd: what is owed, the frame and the statement, off the state. wr: frame
and statement, into the state. It takes no column. The refusal's name is dropped here. -/
def step {σ : Type} (es : List Fmt.Entry) (rd : σ → Option Nat × ReqFrame × Statement)
    (wr : σ → ReqFrame → Statement → σ) : Step σ :=
  fun s rs _ =>
    (closeFrame (rd s).1 (rd s).2.1 (rd s).2.2 es rs).toOption.map fun x => (wr s x.1 x.2, 0)

/-- The step's row in a table of stretches: as many rounds as the stretch has entries. -/
def row {σ : Type} (name : String) (es : List Fmt.Entry)
    (rd : σ → Option Nat × ReqFrame × Statement) (wr : σ → ReqFrame → Statement → σ) : Row σ :=
  ⟨name, es.length, step es rd wr⟩

/-- The stretches of the links' closings, off a first chain's entries: each "BAT" that a
"FOLD epsilon" follows, with the "FOLD round"s behind it, in order. The links' closings come first;
a test's first fold behind them has the same names. -/
def stretches (es : List Fmt.Entry) : List (List Fmt.Entry) :=
  let a := es.toArray
  (List.range a.size).filterMap fun i =>
    if (a[i]?.map (·.name)) == some "BAT" && (a[i + 1]?.map (·.name)) == some "FOLD epsilon" then
      some ((es.drop i).take
        (2 + ((es.drop (i + 2)).takeWhile fun e => e.name == "FOLD round").length))
    else none

end VerifiableInference.Desc.First.Close
