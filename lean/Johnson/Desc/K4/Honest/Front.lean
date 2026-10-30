-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Front.lean: what the honest prover of the layers' own rounds (K4) reads: a
place's public data, the values sampled so far, and the small input: what the parts read of the
prover's input. Definitions with code. No theorem.

NOT SHOWN HERE. No test stands in this file. That `ptsOf` lays each sampled value under the name
under which the verifier's text holds it, and that `envOf` and `namedPts` make what the verifier's
`hear` and `pointsOf` make (`namedPts` less the points that are empty), is by reading; no law of the
library says so.
A VALUE THAT HAS NOT BEEN SAMPLED YET IS AN EMPTY ARRAY: nothing here returns an error, and a caller
that reads a value too early reads that placeholder.

K4 is the part of a layers' sub-proof between the lookup on the calls and the commitment to the
reads (OnBytes/Desc/First/K4/Rounds.lean has its rounds as a table; Hear.lean what the verifier does
while it hears them). The prover's summands are made of three things: cells of the segment's
committed matrices, the committed weights, and values that the verifier has sampled. In the first
group the merge's summand reads the request's tokens too. This file lays the third so that the
verifier's public functions can be called on them as they stand.

  `K4Pub`      a place's public data
  `K4In`       the small input: cells, weights, tokens, and what the lookup in front has sampled
  `Pts`        K4's own sampled values so far
  `rowsNamed`, `starts`, `cutOf`   where the rounds and the parts of K4's row stand, off the
               verifier's table
  `elemsOf`, `onesFrom`, `levelR`, `whole`   helpers that read challenges
  `ptsOf`      the sampled values, of all challenges heard so far
  `matsOf`, `laidOf`, `envOf`   the structure that the verifier's forms read, as Hear.lean makes it
  `ztOf`, `namedPts`   the points at which the tables of the reads are taken, by name

WHERE A ROUND STANDS is read off `rounds P hp g` by the rounds' names: the seven rounds named
"PSC epsilon" begin the seven masked sumchecks; the four named "BAT-sigma" batch. WHAT IS WRITTEN BY
HAND is the ordinal among the rounds of one name (the first, second, third "ZERO"; the four
"BAT-sigma"; the two "JOIN"; the sumchecks 0 to 5); that a sumcheck's own challenges follow its
first round; how many these are, and how many powers a batching element yields (the table's numbers,
typed here a second time); the order in which a level's challenges are laid, and that the batched
sumcheck's are turned round: that is where a slip would sit.

Limits. `K4In.look` is a parameter: which of the lookup's rounds hold its points is the lookup's
matter; `k4LookAt` (Johnson/Desc/ProofFile/Honest/K4/Look.lean) is a text for it, with limits of its
own. Of the structure that it returns K4's parts read three fields: zx, zk, e.
The reads' two tables of bits on the lookup's own matrix, which no part of K4 reads, want shape,
zb0, zb1 as well. What is laid in the other fields is read by nothing here. `ptsOf` calls `look` at
every move: a field that is dear to make (tT: a pass over the lookup's tables) is better left at its
default.
Nothing on any property.
No property is claimed.
-/
import OnBytes.Desc.First.K4.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (RoundName powers lastOf longPoint orderDefault orderRange)
open OnBytes.Model.Layer (Pub HPlan2 Env TableAsk layTables tableAsks)

/-- **A place's public data.** -/
structure K4Pub where
  /-- the layers' public data; its field tokv is never read -/
  P : Pub
  /-- the sub-proof's plan -/
  hp : HPlan2
  /-- the group of layers -/
  g : Nat
  /-- the link's number in the first chain -/
  link : Nat
  /-- the sub-protocol's number inside the link -/
  piece : Nat
  /-- how many rounds of the first chain stand in front of K4's first -/
  r0 : Nat
  /-- the segment's number, from 0, as the reader of the cells counts segments -/
  seg : Nat

/-- **The small input**: all that K4's parts read of the prover's input; and, beside it, `look`,
which is no input: it is public, and the seat lays it from a parameter. -/
structure K4In where
  /-- a cell of this segment: the matrix's number in the sub-proof's list of matrices
  (`P.tails[g].mats`), the row, the column -/
  cell : Nat → Nat → Nat → F
  /-- an entry of the matrix of all committed weights' digits: row, column -/
  w : Nat → Nat → F
  /-- the request's tokens; read in the first group alone -/
  tokv : Array Nat
  /-- what the lookup in front has sampled: of all challenges heard in front of K4's first round -/
  look : List Fmt.Drawn → Model.Forest.Heard

/-- **K4's own sampled values so far.** Each field says where the verifier's text holds the value
(OnBytes/Model/Layer.lean: `Heard`, `HeardStack`; OnBytes/Model/Psc.lean: `Level`); the numbers in
r6, r12, r14 are the steps' in docs/format/11-2-feed-forward-segment.md. -/
structure Pts where
  /-- what the lookup in front has sampled: `Heard.fo` -/
  fo : Model.Forest.Heard
  /-- `Heard.PV` -/
  PV : Array E := #[]
  /-- `Heard.ZE` -/
  ZE : Array E := #[]
  /-- `Heard.tkh` -/
  tkh : Array E := #[]
  /-- `Heard.gp`: the powers of the sampled element, as a batching round returns them -/
  gp : Array E := #[]
  /-- the point on the norms' numbers: a local of `hearNorms` -/
  rhoI : Array E := #[]
  /-- `Heard.wpl.r`: the challenge of variable v at place mu - 1 - v -/
  r6 : Array E := #[]
  /-- `Heard.omV`: powers -/
  omV : Array E := #[]
  /-- `Heard.tV.r`: in the order sampled -/
  rtV : Array E := #[]
  /-- `Heard.tT`'s r: in the order sampled -/
  rt : Array E := #[]
  /-- the powers 1, x of the element that joins two claims: a local of `hearStack` -/
  om : Array E := #[]
  /-- `HeardStack.rs`: the challenge of bit t at place t -/
  rs : Array E := #[]
  /-- the first gated level's r, as r6 -/
  r12 : Array E := #[]
  /-- the point on the layers with routed experts: a local of `hearGated` -/
  rhoM : Array E := #[]
  /-- the second gated level's r, as r6 -/
  r14 : Array E := #[]
  /-- the powers that batch the claims on the weights: the merge's rho -/
  rhoW : Array E := #[]

/-! ## Where the rounds stand -/

/-- The numbers, from 0, of the rows of K4's table that bear a name. -/
def rowsNamed (Q : K4Pub) (r : RoundName) : List Nat :=
  ((rounds Q.P Q.hp Q.g).zipIdx.filter fun x => x.1.name == r).map (·.2)

/-- The numbers of the rounds that begin the seven masked sumchecks. -/
def starts (Q : K4Pub) : List Nat := rowsNamed Q .pscEpsilon

/-- **The cut of K4's row**: how many rounds each part has: a masked sumcheck, from its
"PSC epsilon" to its "PSC values", is one part; every other round is a part by itself. -/
def cutOf (Q : K4Pub) : List Nat :=
  let step (s : List Nat × Nat) (d : Rd) : List Nat × Nat :=
    -- s.2: the rounds of the sumcheck that is open; 0 if none is
    if d.name == .pscEpsilon then (s.1, 1)
    else if d.name == .pscValues then (s.1 ++ [s.2 + 1], 0)
    else if s.2 != 0 then (s.1, s.2 + 1)
    else (s.1 ++ [1], 0)
  ((rounds Q.P Q.hp Q.g).foldl step ([], 0)).1

/-! ## The sampled values -/

/-- The elements that one challenge holds. -/
def elemsOf (d : Fmt.Drawn) : Array E := (d.elems.map E.ofTriple).toArray

/-- The first element of each of the n challenges from number i on; fewer if fewer were heard; 0 for
a challenge that holds no element. -/
def onesFrom (own : List Fmt.Drawn) (i n : Nat) : Array E :=
  (((own.drop i).take n).map fun d => (d.elems.head?.map E.ofTriple).getD zeroE).toArray

/-- The challenges of a product layer's rounds as `Level.r` has them: round j runs in variable
order[j], whose challenge stands at place mu - 1 - order[j]. Empty until all mu have been sampled.
-/
def levelR (mu : Nat) (order : List Nat) (xs : Array E) : Array E :=
  if xs.size != mu then #[]
  else (order.zip xs.toList).foldl (fun r x => r.set! (mu - 1 - x.1) x.2) (Array.replicate mu zeroE)

/-- An array, or nothing of it until it has n members. -/
def whole (n : Nat) (a : Array E) : Array E := if a.size == n then a else #[]

/-- **The sampled values**, of all challenges heard so far in the first chain. -/
def ptsOf (Q : K4Pub) (w : K4In) (heard : List Fmt.Drawn) : Pts :=
  let P := Q.P
  let y := P.y
  let h := y.h
  let own := heard.drop Q.r0
  let at_ (l : List Nat) (k : Nat) : Option Nat := l[k]?
  let elems (i : Option Nat) : Array E := ((i.bind fun j => own[j]?).map elemsOf).getD #[]
  let one (i : Option Nat) : Option E := (elems i)[0]?
  let pw (i : Option Nat) (n : Nat) : Array E := ((one i).map fun x => powers x n).getD #[]
  let zs := rowsNamed Q .zero
  let bs := rowsNamed Q .batSigma
  let js := rowsNamed Q .join
  let ss := starts Q
  -- the challenges of the n rounds behind the "PSC epsilon" of sumcheck number k
  let inner (k n : Nat) : Array E :=
    ((at_ ss k).map fun s => whole n (onesFrom own (s + 1) n)).getD #[]
  let first := Q.g == 0
  { fo := w.look (heard.take Q.r0)
    PV := elems (at_ zs 0)
    ZE := if first then elems (at_ zs 1) else #[]
    tkh := if first then elems (at_ zs 2) else #[]
    gp := pw (at_ bs 0) (Model.ledNS h.xl)
    rhoI := elems (at_ js 0)
    r6 := levelR P.rd.muV (orderDefault P.rd.muV) (inner 0 P.rd.muV)
    omV := pw (at_ bs 1) (Model.ledNP h.xl * y.NI)
    rtV := inner 1 h.lt
    rt := inner 2 h.lt
    om := pw (at_ bs 2) 2
    rs := (inner 3 Q.hp.lamS).reverse
    r12 := levelR P.rd.muH (orderRange P.rd.muH) (inner 4 P.rd.muH)
    rhoM := elems (at_ js 1)
    r14 := levelR P.rd.muH2 (orderRange P.rd.muH2) (inner 5 P.rd.muH2)
    rhoW := pw (at_ bs 3) Q.hp.NCL }

/-! ## What the verifier's forms read -/

/-- The rows and columns of the segment's matrices, in the list's order. -/
def matsOf (Q : K4Pub) : Array (Nat × Nat) :=
  (Q.P.tails.getD Q.g {}).mats.map fun M => (M.m, M.k)

/-- The families of tables of the reads with their parts' places, as `hear` lays them. -/
def laidOf (Q : K4Pub) : Option (List (TableAsk × List (Nat × Nat))) :=
  (layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0).map (·.2.1)

/-- **The structure that the verifier's forms read**, made as `hear` makes it
(OnBytes/Desc/First/K4/Hear.lean). K3, by which a virtual row's number is multiplied (`valAff`,
Johnson/Desc/K4/Honest/Cells.lean), is read off the plan's list of trees, and is 0 where that list
has no tree of the reads' number: a padding of public data alone; a form's entries would then name
other entries of the reads. -/
def envOf (Q : K4Pub) (p : Pts) : Option Env := do
  let iU3 ← Q.hp.tl.ix.U.getD 2 none
  let (tab, _, _) ← layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0
  let K3 := ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0
  pure { y := Q.P.y, sc := Q.P.sc, g := Q.g, iU3, K3, tab, zk := p.fo.zk }

/-- The last lt coordinates of the lookup's point: the lookup's token point. -/
def ztOf (Q : K4Pub) (p : Pts) : Array E := ((lastOf p.fo.zx Q.P.y.h.lt).toOption).getD #[]

/-- **The points at which the tables of the reads are taken**, under the verifier's names
(`pointsOf`, OnBytes/Model/Layer.lean). A point that is not yet whole is left out, and so is a point
without a coordinate: `pointsOf` lists the embedding's point, empty, in every group but the first.
-/
def namedPts (Q : K4Pub) (p : Pts) : List (String × Array E) :=
  let y := Q.P.y
  let la := y.h.la
  let lt := y.h.lt
  let last (n : String) (z : Array E) : List (String × Array E) :=
    match (lastOf z la).toOption with
    | some x => if z.isEmpty then [] else [(n, x)]
    | none => []
  let full (n : String) (k : Nat) (z : Array E) : List (String × Array E) :=
    if z.size == k && k != 0 then [(n, z)] else []
  let Z := last "Z" p.fo.zx
  Z ++ full "zt" lt (ztOf Q p) ++ last "Z_V" p.r6 ++ full "P_V" lt p.PV ++
    full "Z_E" la p.ZE ++ full "r_tV" lt p.rtV ++ last "Z_a" p.r12 ++
    (match Z, p.rt.size == lt with
     | [(_, z)], true => [("Y", longPoint (z.extract 0 y.ls) p.rt), ("rt", p.rt)]
     | _, _ => []) ++
    last "Z_b" p.r14

end OnBytes.Desc.First.K4.Honest
