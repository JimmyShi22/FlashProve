-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Req.lean: the frame of a request's own proof, a chain of links.
C++ counterpart: blocks/iop/req.h (req_groups, req_shape_fault, req_fault, ReqFrame, ReqVerifier,
req_verify).

A link is a part of the computation with a sub-proof of its own. (The link of OnBytes/Iop/Link.lean,
between two stored tables, is another thing.) Its oracle messages go out at a few moments, that is,
in a few prover's messages, and each is sampled at once. The sub-proof ends in rows: linear claims
with public targets on the messages of the link's group. The frame knows nothing else of a
sub-proof. It puts these rounds around it (docs/format/FORMAT.md, R12.16, R12.17, R14.4,
R14.8):
  first    the link's plain scalars, if it has any, in a round of their own; then one prover's
           message: from the second link on, the carrying message (the oracle message that
           re-encodes what the closing of the link before returns) and the kept oracle messages
           sent anew; the link's own messages of moment 0; the fresh mask of the link's own closing;
           in the first link, what rides at the start. Then their sample and, from the second link
           on, the positions of the link before;
  later    the oracle messages of the next moment and their sample;
  close    all rows of the link's group are batched into one and folded to single rows;
  finish   after the last link: a carrying message once more, with the fresh mask of the last test's
           first fold; the positions of the last link; the last proximity test.
So the positions of a group are drawn only after the oracle message that re-encodes its fold has
been sent, sampled and answered.
An oracle message whose main rows later links read has a life: the number of links from it to its
last reader, that reader counted (2 if only the link after the next reads it). In its own link and
in every link before the last of its life its rows are kept rows: a fold leaves them as they are,
and the code switch sends them anew. In the last link of its life they are ordinary rows.
A plain scalar is something public that the prover can name only late, such as a reply. The frame
receives it and passes it to the link's sub-proof. It tests neither its form nor its value: that,
and the comparison with what a client was given, is the duty of the sub-proof's verifier.

The frame's calls (`start`, `first`, `later`, `close`, `finish`) are blocks in `Blk`
(OnBytes/Iop/Ground.lean) and call the smaller blocks by their names: `sendVerify`, `csSigmaVerify`,
`batVerify`, `foldVerify`, `ioppVerify`.

Main definitions: `ReqGroup`, `reqGroups`, `reqShapeOk`, `reqOk`, `ReqFrame`, `ReqFrame.start`,
`ReqFrame.first`, `ReqFrame.later`, `ReqFrame.close`, `ReqFrame.finish`, `ReqFrame.whereIs`,
`reqVerify`.

What is not claimed. A yes of `reqVerify` says nothing of what rides at the start, which belongs to
no group of the frame, nor of a group that a sub-proof has made itself: testing those is the
caller's duty (`Blk.requireAllTested` is not called here). No theorem here speaks of a verdict.
-/
import OnBytes.Iop.Prox
import OnBytes.Chain.Lists

namespace OnBytes

open Params (ReqMessage ReqLink ReqShape IoppStage)

/-! ## What follows from the shape -/

/-- An oracle message whose main rows later links still read. -/
structure ReqAlive where
  shape : OracleShape
  /-- a message that is sent anew stays in the class of leaves in which it was born -/
  leafClass : Nat
  /-- how many links are still to come up to its last reader, that reader counted -/
  left : Nat
  /-- as which oracle message it was first sent: the link, and its number in the link -/
  born : Nat × Nat

/-- What follows from the shape for one group. The groups are those of the links, in their order,
and then the group of the last proximity test. -/
structure ReqGroup where
  /-- the row variables of the group's main rows -/
  k : Nat := 0
  /-- the row variables of the group's mask rows -/
  h : Nat := 0
  /-- where the code switch into this group leads; not used for the first group -/
  target : SwitchTarget := { shape := {}, main := {}, rest := {} }
  /-- for each kept target of that switch, in their order: as what it was first sent -/
  born : Array (Nat × Nat) := #[]
  deriving Inhabited

/-- The rows of the aligned block that takes so many rows: the least power of two that is at least
`rows`; 0 for none. -/
def rowBlock (rows : Nat) : Nat := if rows == 0 then 0 else 2 ^ ceilLog2 rows

/-- The group number l, and the messages that are alive after it. `alive`: those alive before. -/
def reqGroupAt (s : ReqShape) (l : Nat) (alive : List ReqAlive) : ReqGroup × List ReqAlive :=
  let goesOn := fun (a : ReqAlive) => decide (1 < a.left)
  let own := (s.link[l]?.map (·.messages)).getD []
  let born := own.zipIdx.filterMap fun x =>
    if x.1.life == 0 then none
    else some ({ shape := x.1.shape, leafClass := x.1.leafClass, left := x.1.life,
                 born := (l, x.2) } : ReqAlive)
  let main := (if l == 0 then 0 else 2) +
    ((alive.filter fun a => !goesOn a).map fun a => rowBlock a.shape.mainRows).foldl (· + ·) 0 +
    ((own.filter fun m => m.life == 0).map fun m => rowBlock m.shape.mainRows).foldl (· + ·) 0
  let mask := (own.map fun m => rowBlock m.shape.maskRows).foldl (· + ·) 0
  let h := ceilLog2 mask
  let carried : OracleShape :=
    if l == 0 then {} else { code := s.code, mainRows := 2, mainDeg := 3, answers := s.answers }
  let target : SwitchTarget :=
    { shape := carried
      main := { part := .main, bits := 0, firstRow := 0 }
      rest := { part := .main, bits := 0, firstRow := if l == 0 then 0 else 1 }
      kept := (alive.map fun a =>
        ({ shape := a.shape, leafClass := a.leafClass,
           keptAgain := goesOn a } : KeptTarget)).toArray }
  ({ k := max (max (ceilLog2 main) h) 1, h := h, target := target,
     born := (alive.map (·.born)).toArray },
   ((alive.filter goesOn).map fun a => { a with left := a.left - 1 }) ++ born)

/-- The groups from number l on; `count` is how many are still to come. -/
def reqGroupsFrom (s : ReqShape) : (count l : Nat) → List ReqAlive → List ReqGroup
  | 0, _, _ => []
  | count + 1, l, alive =>
    let x := reqGroupAt s l alive
    x.1 :: reqGroupsFrom s count (l + 1) x.2

/-- `reqGroupsFrom` as a loop: the groups are added to `acc`. The depth of the calls does not grow
with the number of links. `reqGroups` runs this form. -/
def reqGroupsLoop (s : ReqShape) : (count l : Nat) → List ReqAlive → Array ReqGroup → Array ReqGroup
  | 0, _, _, acc => acc
  | count + 1, l, alive, acc =>
    let x := reqGroupAt s l alive
    reqGroupsLoop s count (l + 1) x.2 (acc.push x.1)

/-- The loop gives the groups of `reqGroupsFrom`, behind what `acc` held. -/
theorem reqGroupsLoop_eq (s : ReqShape) : ∀ (count l : Nat) (alive : List ReqAlive)
    (acc : Array ReqGroup),
    reqGroupsLoop s count l alive acc = acc ++ (reqGroupsFrom s count l alive).toArray
  | 0, _, _, acc => by simp [reqGroupsLoop, reqGroupsFrom]
  | count + 1, l, alive, acc => by
    simp only [reqGroupsLoop, reqGroupsFrom]
    rw [reqGroupsLoop_eq s count]
    apply Array.toList_inj.1
    simp

/-- All groups of a request: one for each link, then the group of the last test. -/
def reqGroups (s : ReqShape) : Array ReqGroup :=
  reqGroupsLoop s (s.link.length + 1) 0 [] #[]

/-- The groups of a request are those of `reqGroupsFrom`. -/
theorem reqGroups_eq (s : ReqShape) :
    reqGroups s = (reqGroupsFrom s (s.link.length + 1) 0 []).toArray := by
  simp [reqGroups, reqGroupsLoop_eq]

/-- The number of a link's moments. -/
def reqMoments (l : ReqLink) : Nat :=
  match l.messages.getLast? with
  | none => 0
  | some m => m.moment + 1

/-! ## Which shapes are lawful -/

/-- The most rows of an oracle message of a link, or of one that rides at the start. The bound is
that of the C++ programs: far above any use, and sums of such numbers stay far below 2^63. -/
def reqMostRows : Nat := 2 ^ 20

/-- The conditions on one oracle message of a link. A kept message has main rows only and goes in
its link's first message. The last rule is the design's rule for what a later link reads: such rows
are fixed, sampled and answered before their owner's sub-proof draws its first challenge. Nothing in
what ties a kept message to its later sendings needs the rule, but the frame has been tried in that
form only. -/
def reqMessageOk (m : ReqMessage) : Bool :=
  decide (0 < m.shape.mainRows + m.shape.maskRows) &&
  decide (m.shape.mainRows ≤ reqMostRows) && decide (m.shape.maskRows ≤ reqMostRows) &&
  (m.shape.mainRows == 0 || m.shape.mainDeg == 1 || m.shape.mainDeg == 3) &&
  noticeOk { shape := m.shape, leafClass := m.leafClass } &&
  (m.life == 0 || (m.shape.mainRows != 0 && m.shape.maskRows == 0 && m.moment == 0))

/-- The messages come by moment and no moment is empty. t is the moment of the message before. -/
def reqMomentsOk : Nat → List ReqMessage → Bool
  | _, [] => true
  | t, m :: ms => (m.moment == t || m.moment == t + 1) && reqMomentsOk m.moment ms

/-- The conditions on one link by itself. -/
def reqLinkOk (l : ReqLink) : Bool :=
  (l.messages.head?.any fun m => m.moment == 0) && reqMomentsOk 0 l.messages &&
  l.messages.all reqMessageOk

/-- The greatest class of leaves of any link's oracle message. -/
def reqMostClass (s : ReqShape) : Nat :=
  (s.link.flatMap fun l => l.messages.map (·.leafClass)).foldl max 0

/-- What the shape shows by itself. There is a link, and every link passes reqLinkOk. Every message,
also one that rides at the start, is sampled with the request's number of answers, which is at least
1. The protocol's argument needs this: a round that tests what a link's messages hold counts no list
factor because each of them has its sample answered, and SEND samples only a message whose shape has
answers. Every message of a link is under the request's two codes. Nothing is kept beyond the last
link. The first link has a main row that is not kept: a closing folds such rows, and only from the
second link on does the carrying message supply them. What rides at the start has mask rows only and
a class of leaves above every link's: it is opened at other lists of positions than the links'
messages, so it shares no leaf with them. No link's group has more than 2^mostLogN rows. The last
test has at least two stages, and its first stage is the group of the last carrying message. -/
def reqShapeOk (s : ReqShape) : Bool :=
  let groups := reqGroups s
  let lastGroup := groups.getD s.link.length {}
  !s.link.isEmpty && decide (1 ≤ s.answers) &&
  (s.link.zipIdx.all fun x =>
    reqLinkOk x.1 && x.1.messages.all fun m =>
      m.shape.answers == s.answers &&
      (m.shape.mainRows == 0 || m.shape.code == s.code) &&
      (m.shape.maskRows == 0 || m.shape.maskCode == s.maskCode) &&
      decide (x.2 + m.life < s.link.length)) &&
  (s.link.head?.any fun l => l.messages.any fun m => m.shape.mainRows != 0 && m.life == 0) &&
  (s.atStart.all fun n =>
    n.shape.mainRows == 0 && n.shape.maskRows != 0 && decide (n.shape.maskRows ≤ reqMostRows) &&
    noticeOk n && n.shape.answers == s.answers && decide (reqMostClass s < n.leafClass)) &&
  ((groups.toList.take s.link.length).all fun G => decide (G.k ≤ mostLogN)) &&
  decide (2 ≤ s.last.length) && s.last.all stageOk &&
  (s.last.head?.any fun t =>
    t.code == s.code && t.maskCode == s.maskCode && t.k == lastGroup.k && t.h == lastGroup.h)

/-- What a link's closing carries on, in entries of one row: two mask rows' messages, the tails of
the main row and of both mask rows, the pad of the carrying message's sample, and for each kept
message its rows' tails and the pads of its sample. `next` is the group after the link's. -/
def reqCarried (s : ReqShape) (c zk : Code) (next : ReqGroup) : Nat :=
  2 * zk.ell + c.r + 2 * zk.r + s.answers +
    (next.target.kept.toList.map fun k =>
      k.shape.mainRows * c.r +
        k.shape.answers * (if k.shape.mainDeg == 1 then 3 else 1)).foldl (· + ·) 0

/-- What shape and codes show together: the codes exist, a row has room for the answers' pads, the
mask rows are long enough for each closing's hiding polynomial, what a closing carries on fits one
row, and the sizes of the last test close. -/
def reqOk (codes : Codes) (s : ReqShape) : Bool :=
  let groups := reqGroups s
  reqShapeOk s &&
  match codes.base[s.code]?, codes.mask[s.maskCode]? with
  | some c, some zk =>
    decide (s.answers < c.ell) && decide (s.answers < zk.ell) &&
    (s.atStart.all fun n =>
      match codes.mask[n.shape.maskCode]? with
      | some z => decide (n.shape.answers < z.ell)
      | none => false) &&
    ((List.range s.link.length).all fun l =>
      let G := groups.getD l {}
      decide (foldMaskColumns G.k G.h ≤ zk.ell) &&
      decide (reqCarried s c zk (groups.getD (l + 1) {}) ≤ c.ell)) &&
    ioppOk codes s.last s.answers
  | _, _ => false

/-! ## The frame -/

/-- Which call of the frame is due. -/
inductive ReqNext where
  /-- a link's first message, or the end after the last link -/
  | first
  /-- a later moment of the present link, or its closing -/
  | laterOrClose
  /-- nothing more -/
  | done
  deriving DecidableEq, Repr, Inhabited

/-- What the frame keeps between its calls. -/
structure ReqFrame where
  shape : ReqShape
  groups : Array ReqGroup
  next : ReqNext := .first
  /-- the present link, counted from 0 -/
  link : Nat := 0
  /-- the next moment of the present link -/
  moment : Nat := 0
  /-- the group of the present link -/
  group : Nat := noId
  /-- the kept oracle messages of earlier links as they are in the present link, in the order of
  sending -/
  keptBefore : Array Nat := #[]
  /-- the oracle messages that rode in the very first message -/
  atStart : Array Nat := #[]
  /-- the present link's own oracle messages that have been sent -/
  own : Array Nat := #[]
  /-- the present link's plain scalars -/
  plain : List E := []
  /-- the fresh mask of the present link's closing -/
  mask : Option Nat := none
  /-- what the last closing has returned -/
  rows : SingleRows := {}

namespace ReqFrame

/-- The frame before the first link. Fails unless the shape is lawful under the statement's codes
and has the plan's number of answers to a sample. -/
def start (shape : ReqShape) : Blk ReqFrame := do
  let S ← Blk.statement
  Blk.must (reqOk S.codes shape)
  Blk.must (shape.answers == (← Blk.samples))
  pure { shape := shape, groups := reqGroups shape }

/-- The shape of the fold that closes group l. -/
def foldShape (f : ReqFrame) (l : Nat) (layout : GroupLayout) : FoldShape :=
  let G := f.groups.getD l {}
  ioppFoldShape { code := f.shape.code, maskCode := f.shape.maskCode, k := G.k, h := G.h } layout

/-- The present link's oracle messages of one moment. -/
def atMoment (f : ReqFrame) (moment : Nat) : List ReqMessage :=
  ((f.shape.link[f.link]?.map (·.messages)).getD []).filter fun m => m.moment == moment

/-- Oracle messages of a link as they are announced. -/
def notices (own : List ReqMessage) : Array OracleNotice :=
  (own.map fun m => ({ shape := m.shape, leafClass := m.leafClass } : OracleNotice)).toArray

/-- The link's own oracle messages of one moment become members of its group. -/
def joinOwn (f : ReqFrame) (sent : List ReqMessage) (ids : Array Nat) : Blk ReqFrame := do
  Blk.must (sent.length == ids.size)
  for x in zipT sent ids.toList do
    Blk.join f.group x.2 (decide (0 < x.1.life))
  pure { f with own := f.own ++ ids }

/-- Opens the group of the next link, or of the last test. -/
def beginLink (f : ReqFrame) : Blk ReqFrame := do
  let g ← Blk.newGroup f.shape.code f.shape.maskCode
  pure { f with group := g, moment := 1, own := #[] }

/-- Which oracle message of the present link holds the rows of the message that was sent as number
`message` of link `born`: that message itself, or what took its rows at the last switch. Returns
nothing if no link is under way, if the message's moment is still to come, or if the present link
does not read it. -/
def whereIs (f : ReqFrame) (born message : Nat) : Option Nat :=
  if f.next != .laterOrClose then none
  else if born == f.link then f.own[message]?
  else ((f.groups.getD f.link {}).born.idxOf? (born, message)).bind fun i => f.keptBefore[i]?

/-- The first message of the next link. Returns the numbers of the link's own oracle messages of
moment 0. -/
def first (f : ReqFrame) : Blk (ReqFrame × Array Nat) := do
  Blk.must (f.next == .first)
  let L ← Blk.get f.shape.link[f.link]?
  let G ← Blk.get f.groups[f.link]?
  let own := f.atMoment 0
  let others := notices own ++ #[foldMaskNotice (f.foldShape f.link {})] ++
    (if f.link == 0 then f.shape.atStart.toArray else #[])
  let f ← f.beginLink
  let plain ← Blk.recvEs L.plain
  if L.plain != 0 then Blk.closeEmpty "REPLY"
  let (kept, ids) ←
    if f.link == 0 then do
      let ids ← sendVerify others
      pure (f.keptBefore, ids)
    else do
      let s ← csSigmaVerify f.rows G.target f.group others
      pure (s.kept, s.others)
  Blk.must (ids.size == others.size)
  let mask ← Blk.get ids[own.length]?
  let f := { f with
    plain := plain, keptBefore := kept, mask := some mask,
    atStart := f.atStart ++ ids.extract (own.length + 1) ids.size }
  let mine := ids.extract 0 own.length
  let f ← f.joinOwn own mine
  pure ({ f with next := .laterOrClose }, mine)

/-- The oracle messages of the present link's next moment. Returns their numbers. -/
def later (f : ReqFrame) : Blk (ReqFrame × Array Nat) := do
  let L ← Blk.get f.shape.link[f.link]?
  Blk.must (f.next == .laterOrClose && decide (f.moment < reqMoments L))
  let own := f.atMoment f.moment
  let ids ← sendVerify (notices own)
  let f ← { f with moment := f.moment + 1 }.joinOwn own ids
  pure (f, ids)

/-- Closes the present link: all rows of its group are batched into one row, and that row is folded
to a claim on single rows. -/
def close (f : ReqFrame) : Blk ReqFrame := do
  let L ← Blk.get f.shape.link[f.link]?
  let G ← Blk.get f.groups[f.link]?
  Blk.must (f.next == .laterOrClose && f.moment == reqMoments L)
  let (row, layout) ← batVerify f.group
  Blk.must (layout.k == G.k && layout.h == G.h)
  Blk.note "REQ: the group row's target" row.target
  let rows ← foldVerify (f.foldShape f.link layout) row f.mask
  Blk.note "REQ: FOLD's target" rows.target
  pure { f with rows := rows, mask := none, link := f.link + 1, next := .first }

/-- After the last link: the carrying message of the last closing, and the last proximity test, on
that message only. -/
def finish (f : ReqFrame) : Blk ReqFrame := do
  Blk.must (f.next == .first && f.link == f.shape.link.length)
  let G ← Blk.get f.groups[f.link]?
  let f ← f.beginLink
  let s ← csSigmaVerify f.rows G.target f.group #[foldMaskNotice (f.foldShape f.link {})]
  let mask ← Blk.get s.others[0]?
  ioppVerify f.group f.shape.last f.shape.choice (some mask)
  pure { f with next := .done, mask := none }

end ReqFrame

/-! ## A whole request -/

/-- A sub-proof as the frame sees it. After the sample of each moment of each link the frame calls
it: the sub-proof speaks through the same channel, takes masks from the statement's ledgers and
adds its rows to the frame's present group. Its arguments: the frame, the moment, the oracle
messages of that moment, and what the sub-proofs carry along. Not tested by the frame, and the
sub-proof's duty: everything public that enters a row, its target above all, comes from the chain's
first query, from what the prover has sent, or from draws. -/
abbrev ReqSub (σ : Type) : Type := ReqFrame → Nat → Array Nat → σ → Blk σ

/-- The later moments of the present link, from moment t on; `count` is how many are to come. -/
def reqLaterMoments {σ : Type} (sub : ReqSub σ) : (count t : Nat) → ReqFrame → σ →
    Blk (ReqFrame × σ)
  | 0, _, f, x => pure (f, x)
  | count + 1, t, f, x => do
    let (f, sent) ← f.later
    let x ← sub f t sent x
    reqLaterMoments sub count (t + 1) f x

/-- The links that are still to come, one after the other. -/
def reqLinks {σ : Type} (sub : ReqSub σ) : List ReqLink → ReqFrame → σ → Blk (ReqFrame × σ)
  | [], f, x => pure (f, x)
  | L :: rest, f, x => do
    let (f, sent) ← f.first
    let x ← sub f 0 sent x
    let (f, x) ← reqLaterMoments sub (reqMoments L - 1) 1 f x
    let f ← f.close
    reqLinks sub rest f x

/-- A whole chain of links with its last proximity test. Returns the frame at its end and what the
sub-proofs have carried along. A yes says nothing of what rides at the start, nor of a group that a
sub-proof has made itself: testing those is the caller's duty. -/
def reqVerify {σ : Type} (shape : ReqShape) (sub : ReqSub σ) (x : σ) : Blk (ReqFrame × σ) := do
  let f ← ReqFrame.start shape
  let (f, x) ← reqLinks sub shape.link f x
  let f ← f.finish
  pure (f, x)

end OnBytes
