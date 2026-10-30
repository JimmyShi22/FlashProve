-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Own.lean: an honest prover of this library's own for the first toy (a product test), without
a hash, and the decision on what it makes, at tiny sizes. The prover is a function from a witness,
coins and the verifier's messages to the prover's messages, round by round, and the columns of all
trees.

Definitions that compute, and tests (#guard). No theorem. No Mathlib. Generic in the sizes and in
the number of stages.
The decision (`decM`, Fmt/M1All.lean) is the algebraic part of the verifier's check: a function of
the sizes (`Par`) and a view (`View`, both in Fmt/M1Types.lean: what it reads of each round, and the
opened columns) to yes or no. It does not test a file's form, the proof of work, or that an opened
column belongs to its tree's root. A stage (`Stage`) is a stage of the proximity test: its two
codes, the exponents k, h of its numbers of main and mask rows, and its number of drawn positions. A
column is what one leaf of a stage's tree holds: symbols of the stage's rows at one position.

Why: this file's sources include no file of the programs (the C++ implementation that comes with
this Lean code). It tests the decision as a whole on a run of this library's own: an honest run
must be accepted, altered ones refused. The whole (Fmt/M1All.lean) is the pass through all blocks
(`decWith`, Fmt/M1Dec.lean) with the blocks of Fmt/M1Send.lean, Fmt/M1Psc.lean, Fmt/M1Fold.lean,
Fmt/M1Cs.lean. (The decision's outcomes on the programs' own files are tested in
Fmt/M1FullProgPTa.lean, Fmt/M1FullProgPRa.lean, Fmt/M1FullProgPFa.lean and the files beside them.)

Below, "the text" is the programs' description of the toy.
What the prover is given.
  a, b, c: three vectors of 2^K elements of the base field (the toy's claim: a_i b_i = c_i for every
    i).
  coin tag i: all that an honest prover would draw (tails, mask rows, hiding polynomials, free room,
    pads, the masking word), as a function, so that a run can be repeated.
  vs: the verifier's messages as a list (elements, positions), round by round. A message that the
    list lacks counts as empty.
What it gives (`Out`).
  sent: the elements of each round's message.
  roots: the rounds whose message is a root.
  cols: for each tree the column at a position, as words, in the order of the text's section 3.
  lists: the positions at which each tree is opened, as drawn.
Message number i reads the verifier's messages before it alone: so whoever runs the prover along a
chain calls it with the messages so far and takes message number i. (Not proved; tested: other later
messages leave the earlier prover's messages and trees as they were.) The test tries one other
choice only, no later messages at all, and compares each tree at eight positions.

How, block by block (the text's parts 1 to 4).
  SEND: the answer is the sample row's left side at the tables (`lhs`).
  PSC, FOLD: the honest sides of Fmt/M1Psc.lean (`PscHon`) and Fmt/M1Fold.lean (`FoldOwn`). They
    make the round polynomials by sums over the cube.
  CS: what the new oracle message holds is made by Fmt/M1Cs.lean's `csOwnG`.
  BASE: the masking word; tau*; the sums M* + lambda M, R* + lambda R in the clear.
The claim that the prover carries is made by the verifier's own functions (the record `Blocks`), as
in the programs, where one routine serves both sides.

Main names (namespace `Fmt.M1.Own`):
  `PSt`: what the prover holds of a stage: rows and tails of the main rows (`M`, `Rh`), the mask
    rows (`W`, `Sg`), the fresh mask (`P`, `Pi`; at the last stage: the masking word's two rows).
  `go`, `own`: the proximity test from a group's row on; the whole run.
  `viewOf`: the view of a run: what the decision reads.
  `ownStep`: the next message as one function of what was drawn so far.

The tests run at `tiny`: the format's second field (`Fld.two`), K = 2, and three stages with the
toy's shapes (k, h) = (2, 0), (1, 1), (0, 0).
The honest run is accepted, at three sets of made-up messages, and at one with a position drawn
twice. Refused:
  the honest view with one element of one message made one larger: every element of every message,
    one after the other;
  the honest view with one word of an opened column made one larger: every word of a column of each
    tree;
  the honest view with a round too few, a round too many, a column lacking;
  a false witness (one entry of c changed) with all else by the honest rules.

Notation:
  sizes ⟨fld, K, stages, work, salt⟩: the fields of `Par` (Fmt/M1Types.lean);
  `work`: bits of work on each draw of positions;
  a stage ⟨C, Z, k, h, t⟩: the fields of `Stage` (Fmt/M1Types.lean);
  a code (a, l, r): codewords of length 2^a, messages of l entries, a tail of r entries (`Code`,
    Fmt/M1Codes.lean).

Limits: this file does not say that the programs' prover does the same: what is tested is that a
reading of the four parts fits together.
An error that both sides share is not seen by these tests:
  the prover makes its answers with the verifier's sample row and carries the claim with the
    verifier's own functions;
  and rows that are true give a true batched row in any order, so an honest run does not hold the
    order of batching.
The blocks' own tests go other ways for some of this.
Nothing on hiding: the coins are made up.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1All

namespace Fmt.M1
namespace Own

/-- what the prover holds of a stage -/
structure PSt where
  M  : List (List E)
  Rh : List (List E)
  W  : List (List E)
  Sg : List (List E)
  P  : List (List E)
  Pi : List (List E)
  deriving Inhabited

/-- rows of n entries as one table -/
def tabOf (rows : List (List E)) (n : Nat) : Array E :=
  Array.ofFn (n := rows.length * n) fun i =>
    (rows.getD (i.val % rows.length) []).getD (i.val / rows.length) Fld.zeroE

/-- a table of nr rows, row by row -/
def rowsOf (nr : Nat) (T : Array E) : List (List E) :=
  (List.range nr).map fun b => (List.range (T.size / nr)).map fun c => ent T (b + nr * c)

def coins (coin : Nat → Nat → E) (tag n : Nat) : List E := (List.range n).map (coin tag)
def words (e : E) : List UInt64 := [e.1, e.2.1, e.2.2]

/-- the symbols of rows at a position -/
def syms (C : Code) (x : Nat) (rows tails : List (List E)) : List E :=
  (List.range rows.length).map fun b => symE C x (rows.getD b []) (tails.getD b [])

/-- A leaf's column. first: the first tree (three main symbols over the base field); last: the last
tree (the message's and the masking word's main symbols, then their mask symbols) -/
def colOf (s : Stage) (first last : Bool) (p : PSt) (x : Nat) : List UInt64 :=
  if last then
    ((syms s.C x p.M p.Rh ++ syms s.C x (p.P.take 1) (p.Pi.take 1)) ++
      (syms s.Z (cp s.Z x) p.W p.Sg ++
        syms s.Z (cp s.Z x) (p.P.drop 1) (p.Pi.drop 1))).flatMap words
  else
    (if first then ((syms s.C x p.M p.Rh).take 3).map (·.1)
        else (syms s.C x p.M p.Rh).flatMap words) ++
      (syms s.Z (cp s.Z x) p.W p.Sg ++ syms s.Z (cp s.Z x) p.P p.Pi).flatMap words

/-- the hiding polynomial of stage number i -/
def hideOf (coin : Nat → Nat → E) (i : Nat) : FoldOwn.Hide :=
  ⟨fun l t => coin (100 * i + 30) (2 * l + t), coin (100 * i + 30) 0⟩

/-- The fields `P`, `Pi` of stage number i: the fresh mask's rows and tails; at the last stage the
masking word's main row and mask row, and their tails. -/
def riders (f : Fld) (coin : Nat → Nat → E) (i : Nat) (s : Stage) (last : Bool) :
    List (List E) × List (List E) :=
  if last then
    ([coins coin (100 * i + 60) s.C.l, coins coin (100 * i + 61) s.Z.l],
      [coins coin (100 * i + 62) s.C.r, coins coin (100 * i + 63) s.Z.r])
  else
    (rowsOf (2 ^ s.h) (FoldOwn.freshRows f s.k s.h s.Z.l (hideOf coin i)),
      (List.range (2 ^ s.h)).map fun b => coins coin (100 * i + 40 + b) s.Z.r)

/-- The first stage. Its main rows are a, b, c and a row that nobody sends (zeros). The tails of
a, b, c are over the base field. It has one mask row. -/
def stage0 (f : Fld) (coin : Nat → Nat → E) (s : Stage) (last : Bool) (a b c : List UInt64) : PSt :=
  let rd := riders f coin 0 s last
  { M := [a.map Fld.ofF, b.map Fld.ofF, c.map Fld.ofF, List.replicate s.C.l Fld.zeroE]
    Rh := ((List.range 3).map fun r => (coins coin r s.C.r).map fun e => Fld.ofF e.1) ++
      [List.replicate s.C.r Fld.zeroE]
    W := [coins coin 10 s.Z.l], Sg := [coins coin 20 s.Z.r], P := rd.1, Pi := rd.2 }

/-- The next stage, number i, from the fold's challenges -/
def nextSt (f : Fld) (coin : Nat → Nat → E) (i : Nat) (old new : Stage) (last : Bool)
    (g : List E) (p : PSt) : PSt :=
  let gg := csOwnG f old new g p.M p.Rh p.W p.Sg p.P p.Pi
    (coins coin (100 * i + 50) (2 ^ new.h * new.Z.l)) (coin (100 * i + 51) 0)
  let rd := riders f coin i new last
  { M := rowsOf (2 ^ new.k) gg.1,
    Rh := (List.range (2 ^ new.k)).map fun b => coins coin (100 * i + b) new.C.r
    W := rowsOf (2 ^ new.h) gg.2,
      Sg := (List.range (2 ^ new.h)).map fun b =>
          coins coin (100 * i + 20 + b) new.Z.r, P := rd.1, Pi := rd.2 }

/-- what a run gives -/
structure Out where
  sent  : List (List E) := []
  roots : List Nat := []
  cols  : List (Nat → List UInt64) := []
  lists : List (List Nat) := []

def Out.pre (ms : List (List E)) (o : Out) : Out := { o with sent := ms ++ o.sent }

/-- the verifier's message of round r -/
def vAt (vs : List RV) (r : Nat) : RV := vs.getD r default
def el0 (v : RV) : E := v.els.getD 0 Fld.zeroE

/-- a row's left side at tables -/
def lhs (f : Fld) (R : GRow) (m s : Array E) : E := f.addE (dot f R.c m) (dot f R.d s)

def axL (f : Fld) (u : List E) (s : E) (v : List E) : List E :=
  (List.range (max u.length v.length)).map fun i =>
    f.addE (u.getD i Fld.zeroE) (f.mulE s (v.getD i Fld.zeroE))

/-- The proximity test from a group's row on: i: the stage's number; r: the number of the next
round -/
def go (B : Blocks) (f : Fld) (coin : Nat → Nat → E) (vs : List RV) :
    List Stage → (i r : Nat) → PSt → GRow → Out
  | [], _, _, _, _ => {}
  | [s], i, r, p, G =>
    let Ms0 := p.P.getD 0 []
    let Ms1 := p.P.getD 1 []
    let lam := el0 (vAt vs r)
    { sent := [[f.addE (dot f G.c Ms0.toArray) (dot f G.d Ms1.toArray)],
        axL f Ms0 lam (p.M.getD 0 []) ++ axL f Ms1 lam (p.W.getD 0 []) ++
          axL f (p.Pi.getD 0 []) lam (p.Rh.getD 0 []) ++
          axL f (p.Pi.getD 1 []) lam (p.Sg.getD 0 [])]
      cols := [colOf s (i == 0) true p], lists := [(vAt vs (r + 1)).poss] }
  | s :: s' :: more, i, r, p, G =>
    let eps := el0 (vAt vs r)
    let g := (List.range s.k).map fun j => el0 (vAt vs (r + 1 + j))
    let T : FoldOwn.Trial :=
      { k := s.k, h := s.h, G := G, m := tabOf p.M s.C.l, mu := tabOf p.W s.Z.l, U := hideOf coin i,
        eps := eps, g := g, lzk := s.Z.l }
    let sigma := T.sigma f
    let qs := (FoldOwn.honest f T [] g).map (·.1)
    let p' := nextSt f coin (i + 1) s s' more.isEmpty g p
    let vz := vAt vs (r + s.k + 1)
    let z := vz.els.take s'.na
    let beta := vz.els.getD s'.na Fld.zeroE
    let alpha :=
      lhs f (B.sample f s'.Am s'.Az z beta Fld.zeroE) (tabOf p'.M s'.C.l) (tabOf p'.W s'.Z.l)
    let vc := vAt vs (r + s.k + 2)
    let col := colOf s (i == 0) false p
    let G' := (B.cs f s s' (B.fold f s.k s.h G sigma eps qs g)
      (B.sample f s'.Am s'.Az z beta alpha) vc.poss (el0 vc) (fun x =>
        stageCol s (if i == 0 then 3 else 0) (if i == 0 then 0 else 2 ^ s.k) (col x))).getD default
    let o := go B f coin vs (s' :: more) (i + 1) (r + s.k + 3) p' G'
    { sent := [[sigma]] ++ qs.map (fun q => [q.1, q.2]) ++ [[], [alpha]] ++ o.sent,
      roots := (r + s.k + 1) :: o.roots, cols := col :: o.cols, lists := vc.poss :: o.lists }

/-- The whole run. -/
def own (B : Blocks) (P : Par) (coin : Nat → Nat → E) (a b c : List UInt64) (vs : List RV) : Out :=
  match P.stages with
  | [] => {}
  | s :: more =>
    let f := P.fld
    let K := P.K
    let p := stage0 f coin s more.isEmpty a b c
    let m := tabOf p.M s.C.l
    let mu := tabOf p.W s.Z.l
    let z := (vAt vs 0).els.take s.na
    let beta := (vAt vs 0).els.getD s.na Fld.zeroE
    let y := lhs f (B.sample f s.Am s.Az z beta Fld.zeroE) m mu
    let zeta := (vAt vs 2).els
    let d : PscDraw :=
      ⟨el0 (vAt vs 3), (List.range K).map fun j => el0 (vAt vs (4 + j)), el0 (vAt vs (4 + K))⟩
    let w : PscHon.Wit :=
      ⟨(a.map Fld.ofF).toArray, (b.map Fld.ofF).toArray, (c.map Fld.ofF).toArray, mu⟩
    let pm := PscHon.msg f w K zeta d
    let G := sumRows f (el0 (vAt vs (6 + K)))
      (B.psc f K s.Z.l zeta pm.mu pm.q pm.p pm.v d.eps d.gamma d.beta ++
        [B.sample f s.Am s.Az z beta y])
    let o := go B f coin vs P.stages 0 (7 + K) p G
    { o with
      sent := [[], [y], [], [pm.mu]] ++ pm.q.map (fun q => [q.1, q.2]) ++
          [[pm.p.1, pm.p.2], [pm.v.1, pm.v.2], []] ++ o.sent,
      roots := 0 :: o.roots }

/-- The view of a run. -/
def viewOf (o : Out) (vs : List RV) : View :=
  ⟨(List.range o.sent.length).map fun r => ⟨o.sent.getD r [], (vAt vs r).els, (vAt vs r).poss⟩,
    (List.range o.cols.length).flatMap fun t =>
      (o.lists.getD t []).map fun x => (t, x, (o.cols.getD t fun _ => []) x)⟩

/-- the numbers of each round's verifier message: elements, positions, the positions' range -/
def shapeI : List Stage → List (Nat × Nat × Nat)
  | [] => []
  | [s] => [(1, 0, 0), (0, s.t, s.C.n)]
  | s :: s' :: more =>
    [(1, 0, 0)] ++ List.replicate s.k (1, 0, 0) ++
      [(s'.na + 1, 0, 0), (1, s.t, s.C.n)] ++ shapeI (s' :: more)

def shape (P : Par) : List (Nat × Nat × Nat) :=
  [((P.stages.headD default).na + 1, 0, 0), (0, 0, 0), (P.K, 0, 0), (1, 0, 0)] ++
    List.replicate P.K (1, 0, 0) ++ [(1, 0, 0), (0, 0, 0), (1, 0, 0)] ++ shapeI P.stages

/-- made-up elements -/
def mk (f : Fld) (n : Nat) : E :=
  (f.red (1000003 * n + 17), f.red (n * n + 5 * n + 3), f.red (7919 * n + 1))

/-- made-up verifier's messages -/
def chal (P : Par) (seed : Nat) : List RV :=
  (List.range (shape P).length).map fun r =>
    let sh := (shape P).getD r (0, 0, 0)
    ⟨[], (List.range sh.1).map fun j => mk P.fld (seed + 1000 * r + j),
      (List.range sh.2.1).map fun j => (seed * 31 + 17 * r + 29 * j * j + 5 * j) % sh.2.2⟩


/-- One function of the prefix: from what was drawn in the rounds done (elements, positions as
drawn) to the next message's elements and, for each root of that message, the tree's column at a
position -/
def ownStep (B : Blocks) (P : Par) (coin : Nat → Nat → E)
    (a b c : List UInt64) (pre : List (List E × List Nat)) :
    List E × List (Nat → List UInt64) :=
  let o := own B P coin a b c (pre.map fun x => ⟨[], x.1, x.2⟩)
  (o.sent.getD pre.length [], match o.roots.idxOf? pre.length with
    | some t => [o.cols.getD t fun _ => []]
    | none => [])

/-! ## Tests -/

/-- tiny sizes with the toy's three shapes -/
def tiny : Par :=
  ⟨.two, 2,
    [⟨⟨6, 4, 2⟩, ⟨6, 16, 2⟩, 2, 0, 2⟩, ⟨⟨7, 2, 2⟩, ⟨7, 32, 2⟩, 1, 1, 2⟩,
      ⟨⟨9, 2, 2⟩, ⟨9, 128, 2⟩, 0, 0, 2⟩],
    20, 40⟩

def cn (tag i : Nat) : E := mk .two (100000 + 977 * tag + i)
def wa : List UInt64 := [3, 5, 7, 11]
def wb : List UInt64 := [13, 17, 19, 23]
def wc : List UInt64 := [39, 85, 133, 253]

def run (c : List UInt64) (vs : List RV) : Out := own blocks tiny cn wa wb c vs
def decT (V : View) : Bool := decM tiny V

/-- element j of round r's message made one larger -/
def spoilSent (V : View) (r j : Nat) : View :=
  { V with rounds := (List.range V.rounds.length).map fun i =>
      let v := V.rounds.getD i default
      if i = r then
        { v with
          sent := (List.range v.sent.length).map fun t =>
              if t = j then Fld.two.addE (v.sent.getD t Fld.zeroE) Fld.oneE
              else v.sent.getD t Fld.zeroE }
      else v }

/-- word j of the first opened column of a tree made one larger -/
def spoilCol (V : View) (tree j : Nat) : View :=
  let x0 := ((V.opened.find? fun o => o.1 == tree).map (·.2.1)).getD 0
  { V with
    opened := V.opened.map fun o =>
        if o.1 == tree && o.2.1 == x0 then
          (o.1, o.2.1,
            (List.range o.2.2.length).map fun t =>
              if t = j then Fld.two.add (o.2.2.getD t 0) 1 else o.2.2.getD t 0)
        else o }

def honestV (seed : Nat) : View := viewOf (run wc (chal tiny seed)) (chal tiny seed)

end Own

open Own in
#guard stagesOK blocks tiny && (shape tiny).length == nRounds tiny && nRounds tiny == 20
-- the honest run is accepted
open Own in
#guard decT (honestV 1) && decT (honestV 2) && decT (honestV 77)
-- with a position drawn twice, at each of the three lists
open Own in
#guard (let vs := (chal tiny 5).map fun v => { v with poss := v.poss.map fun _ => 9 }; decT (viewOf (run wc vs) vs))
-- the numbers: twenty messages; roots in rounds 0, 12, 16; three trees with columns of 9, 18, 12
-- words
open Own in
#guard ((run wc (chal tiny 1)).sent.length, (run wc (chal tiny 1)).roots, (run wc (chal tiny 1)).cols.map fun c => (c 5).length) == (20, [0, 12, 16], [9, 18, 12])
-- every element of every message bears on the decision: one element made one larger, all else as it
-- was: refused. All 155 elements of the twenty messages, the 134 in the clear among them
open Own in
#guard ((List.range 20).map fun r => ((honestV 1).rounds.getD r default).sent.length).sum == 155
open Own in
#guard (List.range 20).all fun r => (List.range ((honestV 1).rounds.getD r default).sent.length).all fun j => !decT (spoilSent (honestV 1) r j)
-- one word of an opened column, of every row of every tree: refused
open Own in
#guard (List.range 9).all (fun j => !decT (spoilCol (honestV 1) 0 j)) && (List.range 18).all (fun j => !decT (spoilCol (honestV 1) 1 j)) && (List.range 12).all (fun j => !decT (spoilCol (honestV 1) 2 j))
-- a false witness, all else by the honest rules: refused
open Own in
#guard !decT (viewOf (run [39, 85, 134, 253] (chal tiny 1)) (chal tiny 1)) && !decT (viewOf (run [40, 85, 133, 253] (chal tiny 2)) (chal tiny 2))
-- a round too few, a round too many, a column that lacks: refused
open Own in
#guard !decT { honestV 1 with rounds := (honestV 1).rounds.dropLast } && !decT { honestV 1 with rounds := (honestV 1).rounds ++ [default] } && !decT { honestV 1 with opened := (honestV 1).opened.drop 1 }
-- message number i reads the verifier's messages before it alone: with the first i messages of one
-- run and none behind them, message i and the trees sent so far, at positions 0 to 7, are those of
-- the whole run
open Own in
#guard (List.range 20).all fun i =>
  let o := run wc (chal tiny 1)
  let o' := run wc ((chal tiny 1).take i)
  o'.sent.getD i [] == o.sent.getD i [] && (List.range o.roots.length).all fun t => decide (i < o.roots.getD t 0) || (List.range 8).all fun x => (o'.cols.getD t fun _ => []) x == (o.cols.getD t fun _ => []) x
-- the function of the prefix gives the run's messages
open Own in
#guard (List.range 20).all fun i => (ownStep blocks tiny cn wa wb wc (((chal tiny 1).take i).map fun v => (v.els, v.poss))).1 == (run wc (chal tiny 1)).sent.getD i []
open Own in
#guard (List.range 20).map (fun i => (ownStep blocks tiny cn wa wb wc (((chal tiny 1).take i).map fun v => (v.els, v.poss))).2.length) == [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]

end Fmt.M1
