-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SwDid.lean: what a code switch of the proximity test and the batching behind it
have done, as a record without a context.

Definitions alone. The library's `CsTaken` and `CsRan` (OnBytes/Slice/BlkCsRun.lean) say what a run
of the code switch of the program `verify-on-bytes` has done between two contexts. Here the same
clauses stand over plain data: the statement, the book and the count of roots in front, the
statement and the book behind; and the one clause that was a run, the reading of the old rows, is a
yes of the plain `readOld` (Johnson/Top/H0/Tw/L9/Switch.lean).
Main names:
  `Taken`: what was taken of the two rounds and made on the way, with the statements between.
  `bookSentP`: the book behind the sending.
  `Did`: what the switch and the batching behind it have done.
  `SeatP`: the named messages are the parts of one tree.
  `SwitchUnfolds`: a proposition: a yes of the switch's part on two rounds and of the batching's
    part behind it gives `Did`. Proved in Johnson/Desc/K12/Law/SwUnfold.lean.
  `SeatReads`: a proposition: a seat of the stage's message and its fold's mask in one tree, and
    columns that are the written tree's, give `ReadTie` at the standard readings. Proved in
    Johnson/Desc/K12/Law/SwRead.lean.
Limits: No theorem stands in this file. The two propositions are asserted nowhere in it. What
follows from `Did` is in Johnson/Desc/K12/Law/SwClaim.lean and SwTies.lean;
Johnson/Desc/K12/Law/SwitchKeeps.lean joins the four. Nothing here is about hiding.

-/
import Johnson.Desc.K12.Law.JointK

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

/-- What a switch has taken of its two rounds and has made on its way. -/
structure Taken where
  /-- how the oracle messages sent are placed in trees -/
  lay : TreeLay
  /-- the round of the seed; the round of the positions -/
  rS : Fmt.RoundView
  rC : Fmt.RoundView
  /-- the factor of the seed; the answer -/
  beta : E
  alpha : E
  /-- the left side of the sample row; the pad of the sample -/
  smp : Row
  places : List PadPlace
  /-- the old main code -/
  code : OnBytes.Code
  /-- the symbols read of the old rows -/
  y : Array E
  /-- the group before the switch -/
  G : Group
  /-- the claims on the new oracle message -/
  rows : List Row

namespace Taken
variable (D : Taken) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice) (S : Statement)

/-- The point of the seed. -/
def z : List E := (D.rS.drawn.elems.map E.ofTriple).take (Send.cube S.codes T.shape).bits

/-- The sample row. -/
def sample : Row := { D.smp with target := D.alpha }

/-- The statement after the sending. -/
def stA : Statement :=
  admitted (stSent S (sentOf T others)) S.oracles.size T.shape D.places #[D.sample]

/-- The statement in which the new oracle message is a member of its group. -/
def stJ : Statement :=
  withMessageInGroup (ledgerShut (D.stA T others S) T S.oracles.size) gp S.oracles.size false D.G

/-- The statement with the claims as open rows. -/
def stR : Statement := withRows (D.stJ T gp others S) gp D.rows

/-- The group with its new member and the claims. -/
def grown : Group :=
  { D.G with
    members := D.G.members.insertIdxIfInBounds
      (D.G.members.filter (· < S.oracles.size)).size S.oracles.size
    kept := D.G.kept.insertIdxIfInBounds (D.G.members.filter (· < S.oracles.size)).size false
    rows := D.G.rows ++ D.rows.toArray }

end Taken

/-- The book after a prover's message with oracle messages (Ground.recvP's term; the library's
bookSent without its context). -/
def bookSentP (firstTree roots : Nat) (S : Statement) (Bk : TreeBook) (sent : Array OracleNotice)
    (lay : TreeLay) : TreeBook :=
  { trees := partsLaid sent lay S.oracles.size Bk.trees.size
      (treesSent firstTree lay.shapes.toList roots Bk.trees)
    place := Bk.place ++ (Array.range sent.size).map fun i =>
      (Bk.trees.size + lay.tree.getD i 0, lay.part.getD i 0) }

/-- What a switch and the batching behind it have done. firstTree: the chain's first tree's number.
cols: the columns that the switch was dealt. S, Bk, roots: in front. S', Bk': behind. -/
structure Did (firstTree : Nat) (cols : List Tw.L9.Col) (old : SingleRows) (T : SwitchTarget)
    (gp : Nat) (others : Array OracleNotice) (S : Statement) (Bk : TreeBook) (roots : Nat)
    (S' : Statement) (Bk' : TreeBook) (out : Switched) (row : GroupRow) (lay : GroupLayout)
    (theta : E) (D : Taken) : Prop where
  check : switchTargetCheck S old T = true
  trees : layTrees S.codes (sentOf T others) = some D.lay
  /-- before the switch the book had a place for each oracle message, and for no other -/
  places : S.oracles.size = Bk.place.size
  /-- the first round sends roots alone and draws the point and one factor, which is not 0 -/
  valsS : D.rS.vals = []
  seed : (D.rS.drawn.elems.map E.ofTriple).drop (Send.cube S.codes T.shape).bits = [D.beta]
  factor : isZeroE D.beta = false
  form : Send.form S.codes T.shape S.oracles.size ⟨D.z T S, D.beta⟩ 0 = some D.smp
  pad : Send.pad S.codes T.shape = some D.places
  /-- the second round sends the answer and draws positions and one element -/
  valsC : D.rC.vals = [.answer D.alpha.triple]
  elem : D.rC.drawn.elems.map E.ofTriple = [theta]
  code : S.codes.base[old.code]? = some D.code
  g : out.g = S.oracles.size
  kept : out.kept = #[]
  /-- the other oracle messages of the prover's message have the numbers after it -/
  riders : out.others = (Array.range others.size).map (· + (S.oracles.size + 1))
  positions : out.positions = Positions.ofDraws D.code.logN D.rC.drawn.poss
  /-- the old rows are read: a yes of the plain reading `readOld`, at the statement and the book
  behind the sending -/
  read : ∃ (i : Tw.L9.SwIn) (left : List Tw.L9.Col), i.st = D.stA T others S ∧
    i.book = bookSentP firstTree roots S Bk (sentOf T others) D.lay ∧ i.firstTree = firstTree ∧
    i.opened = cols ∧ i.old = old ∧ Tw.L9.readOld i out.positions = .ok (Bk', left, D.y)
  /-- the claims -/
  group : (ledgerShut (D.stA T others S) T S.oracles.size).groups[gp]? = some D.G
  fresh : D.G.inRun = false
  rows : switchRows (D.stJ T gp others S) old T S.oracles.size #[] out.positions D.y = some D.rows
  kinds : ∀ r ∈ D.rows, r.kind ≠ .sample ∧ RowChecked (D.stJ T gp others S) r
  /-- the batching -/
  layout : (D.stR T gp others S).layout gp = some lay
  row : Bat.combine (begun (D.stR T gp others S) gp (D.grown S)) gp
    ⟨lay, runRows (D.stR T gp others S) (D.grown S)⟩ theta = some row
  /-- what is left -/
  st : S' = begun (D.stR T gp others S) gp (D.grown S)

/-- The oracle messages ids are the parts of one tree, in this order: the tree with the number n, of
2^logN leaves. shapes: their shapes. -/
structure SeatP (st : Statement) (book : TreeBook) (ids : List Nat) (n logN : Nat)
    (shapes : List OracleShape) : Prop where
  len : shapes.length = ids.length
  tree : ∃ (t : Nat) (tree : Tree), book.trees[t]? = some tree ∧ tree.number = n ∧
    tree.shape.logN = logN ∧
    tree.shape.mainSymbols = (shapes.map fun s => s.mainRows * s.mainDeg).toArray ∧
    tree.shape.maskSymbols = (shapes.map fun s => s.maskRows * 3).toArray ∧
    ∀ w, w < ids.length → book.place[ids.getD w 0]? = some (t, w)
  shape : ∀ w, w < ids.length →
    ∃ x, st.oracles[ids.getD w 0]? = some x ∧ x.shape = shapes.getD w default

/-- What comes with the switch's message beside the new tables, as switchJ lays it where the masks
come early. -/
def othersOf (last : Bool) (nx : IoppStage) : Array OracleNotice :=
  if last then #[baseMaskNotice nx.code nx.maskCode 1 0] else #[foldMaskNotice (ioppFoldShape nx
      {})]

/-- A proposition, asserted nowhere in this file and proved in Johnson/Desc/K12/Law/SwUnfold.lean: a
yes of the switch's part on two rounds and of the batching's part behind it gives `Did`. -/
def SwitchUnfolds (p : P12) : Prop :=
  ∀ (j : Nat) (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rS rC : Fmt.RoundView) (gs : Gs) (rows : SingleRows) (gp : Nat) (nx : IoppStage),
    p.early = true → p.answers = 1 → t1.pass = .single rows gp →
    stageAt p (j + 1) nxt = some nx →
    (switchJ p j cur nxt last cut).decide t1 [rS, rC] gs = .ok t2 →
    (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3 →
    ∃ (out : Switched) (row : GroupRow) (lay : GroupLayout) (theta : E) (D : Taken),
      D.rS = rS ∧ D.rC = rC ∧
      Did p.nums.firstTree (keyed p cut gs) rows
        (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) gp (othersOf last nx) t1.st t1.book
        t1.roots t3.st t3.book out row lay theta D ∧
      t3.pass = .claim row lay ∧ t3.mask = out.others[0]?

/-- A proposition, asserted nowhere in this file and proved in Johnson/Desc/K12/Law/SwRead.lean. o:
the stage's oracle message; id: its fold's mask; d, orc: the written round that sent their tree, and
its written oracle. -/
def SeatReads : Prop :=
  ∀ (firstTree : Nat) (s : Sg) (cu : IoppStage) (L : GroupLayout) (st : Statement)
    (book : TreeBook) (o id n : Nat) (d : PQ.RD) (orc : (wRound d).Orc) (cols : List Tw.L9.Col)
    (poss : List Nat),
    cu.k = s.h + s.g → cu.h = s.h → 1 ≤ s.h + s.g → LayAt [o] #[some 0] #[some 0] L →
    SeatP st book [o, id] n s.C.a (stageShapes s cu) →
    PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h) →
    (∀ c ∈ cols, c.2.2 = colW d orc c.2.1) →
    ReadTie firstTree s (wordIn s (colSt s d orc)) (wordFr s (colSt s d orc)) (ioppFoldShape cu L)
      st book id cols poss

end H2K.Sw
