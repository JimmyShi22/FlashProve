-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FirstOk.lean: a test, by evaluation, that the public premises and the record's
premises of the law of the proximity test (the kind K12) at its first stage are not empty.

The premises are GpData.Pub, GpData.LayG, PartsP (Johnson/Desc/K12/Law/FirstRead.lean) and OpensAre
(Johnson/Desc/K12/Law/FirstSrc.lean). Definitions with code alone and no theorem, so that the test
can be compiled and run. Nothing is typed off a print: the plain data are made by code from the
record behind the batching and the place's numbers.
Main names:
  `Seat1`, `seatOf`: an oracle message as a part of a tree: its shape off st.oracles; its tree's
    place and its part off book.place; that tree's shape and number off book.trees.
  `entered`: the first fold's mask, with the statement and the book behind its entering: it has come
    (the record names it), or the fold's own first message brings it (Ground.recvP at foldMaskNotice
    of the place's own stage).
  `Plain`, `gpOf`: the members off L.members, in the layout's order; the mask; the first rows of the
    blocks off L.mainFirst and L.maskFirst; the trees' places, rising, each once (Fmt.listOf); what
    the first switch's two declared rounds open (the frame's own cut of H2U.roundsOfNums).
  `gpL`, `gpOk`, `gpNo`: the clauses, named, so that a run says which refuses.
The clauses (w: a member's number in the layout):
  w:short: the member's tree is not longer than the range (Site.ha). w:long: a member with a main
    row has a tree as long as the range (Site.hM). w:zshort: at a member with a mask row the mask
    code is not longer than its tree (Site.hz).
  w:codeM, w:codeZ: the record's code at the shape's number is the stage's (what Site.hC and Site.hZ
    mean; the typed group takes the stage's codes by definition).
  w:deg: main rows over the base field or over the extension field (Pub.deg). w:roomM, w:roomZ: the
    block has room in the table (Numbered). w:firstM, w:firstZ: a member with rows has a first row
    (LayG).
  apartM, apartZ: no two blocks overlap (Numbered). kept: no member is kept, at any number
    (LayG.kept). sizes: the layout's four arrays are as long as one another.
  f:main, f:mask: the mask has no main row and 2 ^ h mask rows (Pub.fMain, Pub.fMask). f:short,
    f:zshort, f:codeZ: as for a member. f:no member: the mask is no member.
  opens.n, opens.key, opens.a, opens.W: the first switch's declared openings are as many as the
    trees, and in turn have their keys (OpensAre), depths and widths. A key is a tree's number less
    firstTree, cut off at 0, on both sides of opens.key: where every opened tree's number is below
    firstTree (the full size's last chain: keys 0, 0, 0) that clause says nothing. The numbers
    uncut are `labelsOk`'s clause opens.tree (Johnson/Desc/K12/Law/FirstCut.lean), which the block
    asks beside `gpOk` (Johnson/Desc/K12/JoinGuarded.lean, guard (g)). No clause here reads the source
    of a declared opening.
  row.kept: the batched row has no kept form.
Limits: Evaluated is not proved. No soundness is claimed, and nothing is said on hiding.

-/
import Johnson.Desc.K12.Join

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12

abbrev Clauses : Type := List (String × Bool)
def ok (l : Clauses) : Bool := l.all (·.2)

/-- An oracle message as a part of a tree. -/
structure Seat1 where
  id : Nat
  sh : OracleShape
  t : Nat
  part : Nat
  tsh : TreeShape
  num : Nat
  deriving Repr

def seatOf (st : Statement) (book : TreeBook) (id : Nat) : Option Seat1 :=
  (st.oracles[id]?).bind fun x => (book.place[id]?).bind fun q => (book.trees[q.1]?).map fun T =>
    ⟨id, x.shape, q.1, q.2, T.shape, T.number⟩

/-- The word at which the main | mask symbols of part p begin in a column (the library's skipM |
skipZ). -/
def skM (tsh : TreeShape) (p : Nat) : Nat := (tsh.mainSymbols.extract 0 p).foldl (· + ·) 0
def skZ (tsh : TreeShape) (p : Nat) : Nat :=
  tsh.mainWidth + (tsh.maskSymbols.extract 0 p).foldl (· + ·) 0

/-- The first fold's mask, and the statement and the book behind its entering. cu: the place's first
stage in the program's form. -/
def entered (p : P12) (t : T12) (cu : IoppStage) (L : GroupLayout) :
    Option (Nat × Statement × TreeBook) :=
  match t.mask with
  | some id => some (id, t.st, t.book)
  | none =>
    (Ground.recvP p.nums.firstTree (⟨t.st, t.book, t.roots, [], ()⟩ : _root_.Desc.Plain.DState
        Unit)
      #[foldMaskNotice (ioppFoldShape cu L)]).bind fun x => (x.1[0]?).map fun id => (id, x.2.st,
          x.2.book)

/-- What the first switch's two declared rounds open: the frame's own cut. k: the first stage's row
variables. -/
def opensOf (p : P12) (k : Nat) : List (Fmt.Shape × Fmt.TreeSource) :=
  ((((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1).drop (1 + k)).take 2).flatMap
    (·.1.opens)

structure Plain where
  st : Statement
  book : TreeBook
  L : GroupLayout
  mems : List Seat1
  fresh : Seat1
  ts : List Nat
  opens : List (Fmt.Shape × Fmt.TreeSource)

def gpOf (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) : Option Plain :=
  (stageAt p 0 a).bind fun cu => (entered p t cu L).bind fun e =>
    (L.members.toList.mapM (seatOf e.2.1 e.2.2)).bind fun ms => (seatOf e.2.1 e.2.2 e.1).map fun f
        =>
      ⟨e.2.1, e.2.2, L, ms, f, Fmt.listOf ((ms.map (·.t)) ++ [f.t]), opensOf p a.k⟩

def oM (L : GroupLayout) (w : Nat) : Nat := (L.mainFirst.getD w none).getD 0
def oZ (L : GroupLayout) (w : Nat) : Nat := (L.maskFirst.getD w none).getD 0
def keyAt (F : Nat) (book : TreeBook) (t : Nat) : Nat := ((book.trees[t]?).map (·.number)).getD 0 -
    F
def logAt (book : TreeBook) (t : Nat) : Nat := ((book.trees[t]?).map (·.shape.logN)).getD 0
def widthAt (book : TreeBook) (t : Nat) : Nat :=
  ((book.trees[t]?).map fun T => T.shape.mainWidth + T.shape.maskWidth).getD 0

def codeB (x : Option OnBytes.Code) (c : Fmt.M1.Code) : Bool := decide (x = some ⟨c.a, c.l, c.r⟩)

/-- The row variables in the library's form: h + g with g := k - h. -/
def kk (a : Fmt.M1.Stage) : Nat := a.h + (a.k - a.h)

def memL (K : Codes) (a : Fmt.M1.Stage) (L : GroupLayout) (w : Nat) (m : Seat1) : Clauses :=
  [("short", decide (m.tsh.logN ≤ a.C.a)),
   ("long", decide (0 < m.sh.mainRows → m.tsh.logN = a.C.a)),
   ("zshort", decide (0 < m.sh.maskRows → a.Z.a ≤ m.tsh.logN)),
   ("codeM", m.sh.mainRows == 0 || codeB K.base[m.sh.code]? a.C),
   ("codeZ", m.sh.maskRows == 0 || codeB K.mask[m.sh.maskCode]? a.Z),
   ("deg", m.sh.mainDeg == 1 || m.sh.mainDeg == 3),
   ("roomM", decide (oM L w + m.sh.mainRows ≤ 2 ^ kk a)),
   ("roomZ", decide (oZ L w + m.sh.maskRows ≤ 2 ^ a.h)),
   ("firstM", m.sh.mainRows == 0 || (L.mainFirst.getD w none).isSome),
   ("firstZ", m.sh.maskRows == 0 || (L.maskFirst.getD w none).isSome)].map fun x =>
    (toString w ++ ":" ++ x.1, x.2)

def apartB (first : Nat → Nat) (rows : Seat1 → Nat) (ms : List Seat1) : Bool :=
  ms.zipIdx.all fun x => ms.zipIdx.all fun y =>
    x.2 == y.2 || decide (first x.2 + rows x.1 ≤ first y.2) || decide (first y.2 + rows y.1 ≤ first
        x.2)

def gpL (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain) : Clauses :=
  let K := D.st.codes
  let F := p.nums.firstTree
  (D.mems.zipIdx.flatMap fun x => memL K a D.L x.2 x.1) ++
  [("apartM", apartB (oM D.L) (·.sh.mainRows) D.mems), ("apartZ",
      apartB (oZ D.L) (·.sh.maskRows) D.mems),
   ("kept", D.L.kept.all (!·)),
   ("sizes", D.L.kept.size == D.L.members.size && D.L.mainFirst.size == D.L.members.size &&
      D.L.maskFirst.size == D.L.members.size),
   ("f:main", D.fresh.sh.mainRows == 0), ("f:mask", D.fresh.sh.maskRows == 2 ^ a.h),
   ("f:short", decide (D.fresh.tsh.logN ≤ a.C.a)), ("f:zshort", decide (a.Z.a ≤ D.fresh.tsh.logN)),
   ("f:codeZ", codeB K.mask[D.fresh.sh.maskCode]? a.Z),
   ("f:no member", !D.L.members.contains D.fresh.id),
   ("opens.n", D.opens.length == D.ts.length),
   ("opens.key", D.opens.map (·.1.tree - F) == D.ts.map (keyAt F D.book)),
   ("opens.a", D.opens.map (·.1.a) == D.ts.map (logAt D.book)),
   ("opens.W", D.opens.map (·.1.W) == D.ts.map (widthAt D.book)),
   ("row.kept", row.kept.isEmpty)]

/-- The named clauses at a place and the record behind the batching. -/
def gpAll (p : P12) (t : T12) : Clauses :=
  match p.nums.stages, t.pass with
  | a :: _, .claim row L =>
    match gpOf p t a L with
    | some D => gpL p a row D
    | none => [("the plain data cannot be made: a member, the mask, a place or a tree is lacking",
        false)]
  | _, _ => [("no stage, or no claim passes", false)]

/-- The test: every clause says yes. -/
def gpOk (p : P12) (t : T12) : Bool := ok (gpAll p t)

/-- The clauses that refuse. -/
def gpNo (p : P12) (t : T12) : List String := ((gpAll p t).filter (!·.2)).map (·.1)

end H2K.First
