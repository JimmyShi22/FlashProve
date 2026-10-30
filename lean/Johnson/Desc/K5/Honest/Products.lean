-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Products.lean: the honest prover's side of an attention segment's own rounds:
the summands of the five kinds of masked sumcheck whose weights hang on the lookup calls' key
points. Definitions with code; no theorem. Tests: Johnson/Desc/K5/Honest/ProductsToy.lean [not in
this library; so here read: not tested in this library].

Each of the five sums, over a cube and over the pieces b of a list of keys, W_b A_b B_b, with W_b
public and A_b, B_b hidden, all three of degree at most 1 in each variable
(docs/format/11-3-attention-segment.md, "The eight kinds of sumcheck of rows 4 to 15").

  `ofProducts`   such a sum in the form of Johnson/Desc/K5/Honest/Terms.lean: the end value number 2
                 b is A_b, number 2 b + 1 is B_b; one term a piece, W_b times the two end values
  `noProducts`   the same lengths, 0 everywhere
  `sK`           a softmax-table unit: query times key; below the diagonal or on it, by the unit's
                 flag
  `sSE`          the softmax denominator times the output
  `sVM`, `sVD`   the value product: softmax weight times (a batching element + value), below the
                 diagonal and on it
  `timesN`, `underN`, `overHeads`, `atTokens`, `planeAt`, `weightAt`, `pairOf`, `DivIn`, `divIn`,
  `belowAt`      what these share

Where each letter comes from. A sumcheck's prover needs W, A and B at points that are not yet
challenges; the verifier's text speaks of them at the challenges alone. So each is typed as a
function of a point r, in such a way that at the challenges it is what the verifier's text reads
there.
  W: the verifier's own functions are called at r: `scoreW` (Johnson/Desc/First/Att/LeftP.lean) and
     `wDivision`, `wBelow`, `wOn` (Att/K5LeftAll.lean: the lines of `leftP` under names).
  A, B: the verifier ties an end value to cells in two steps: a claim reads entries of the array of
     tables (Att/RunsP.lean: `endValues`, `endValuesE`, `valueProduct`), and each table is a sum of
     cells under a weight vector (Att/TablesP.lean: `placeAll`). Here the two steps are joined: a
     sum of cells under the product of the claim's weights and the table's. The weight vectors are
     made by the verifier's own `tok`, `scoreTiles`, `pointM`, `pointD`, `lastCoords`, `eqTab`; the
     named cuts of the key points are read from its `pointsOf` (Johnson/Desc/K5/Honest/Points.lean).
     Cuts of r itself are typed after the verifier's lines: where these lines have no name of their
     own, and in `belowAt`, whose line stands inside `pointsOf`: a call of that function makes all
     the place's points anew. Each definition's docstring names the lines.
A constant in a hidden map (128 in a softmax weight, the batching element beside a value) lies
inside the end value, as in the verifier's claims; every factor is the bare end value.

A piece's layer and head are the piece's own (`W1`), as the verifier's claims take them; the pair's
number among the cells is layer times HA plus head.

Limits. The joined sums suppose the plan's lengths: a region's point has as many coordinates as the
region has bits, a channel point ldh. Where the verifier's `pointsOf` refuses, or the place has no
such unit or list, the summand has its stated lengths and is 0 everywhere. Neither this file nor its
tests hold the joined sums against the verifier's claims on an array of tables: the tests hold them
against the format's table on the cube, at three small plans and made-up cells. The claims
themselves are the matter of Johnson/Desc/ProofFile/Honest/K5/Toy1.lean, which plays the row and
evaluates the verifier's two runs of claims on an array of tables made of the cells. That a matrix's
cell stands where a table's weight vector reads it is not this file's.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Terms
import Johnson.Desc.K5.Honest.Points
import Johnson.Desc.First.Att.K5LeftAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE mulE zeroE oneE)
open VerifiableInference.Desc.First.Att.P (Geo W1 DivP Heard eqTab ofNat weights inner scoreW
  scoreTiles tileSums tok lastCoords pointM pointD wDivision wBelow wOn)

/-! ## The common form -/

/-- **A sum of weighted products of two hidden maps**, over np pieces. W r: the pieces' public
weights at the point r. A r b, B r b: the two hidden maps of piece b at r. -/
def ofProducts (vars np : Nat) (W : Array E → Array E) (A B : Array E → Nat → E) : Summand :=
  { vars := vars, ends := 2 * np
    endAt := fun x n => if n % 2 == 0 then A x.toArray (n / 2) else B x.toArray (n / 2)
    terms := fun x =>
      let Wx := W x.toArray
      (List.range np).map fun b =>
        ⟨Wx.getD b zeroE, [⟨oneE, 2 * b, zeroE⟩, ⟨oneE, 2 * b + 1, zeroE⟩]⟩ }

/-- The same lengths; 0 everywhere. -/
def noProducts (vars np : Nat) : Summand :=
  ofProducts vars np (fun _ => #[]) (fun _ _ => zeroE) fun _ _ => zeroE

/-! ## Sums of cells -/

/-- The number, among the cells, of a piece's pair of layer and query head. -/
def pairOf (g : Geo) (p : W1) : Nat := p.lam * g.HA + p.a

/-- a times f (), without the call of f where a is 0. At a point of zeros and ones most weights are
0, and a sumcheck's prover evaluates its maps mostly at such points. -/
def timesN (a : E) (f : Unit → E) : E := if a == zeroE then zeroE else mulE a (f ())

/-- The sum of w[i] f i over w's entries: the value of `under`, by `timesN`. -/
def underN (w : Array E) (f : Nat → E) : E :=
  sumTo w.size fun i => timesN (w.getD i zeroE) fun _ => f i

/-- The sum over the heads hk of keys and values of eq(the first lgk coordinates of z, hk) f hk.
After `overG`, Att/RunsP.lean:212-213. -/
def overHeads (g : Geo) (z : Array E) (f : Nat → E) : E :=
  let e := eqTab (z.extract 0 g.lgk)
  sumTo g.G fun hk => timesN (e.getD hk zeroE) fun _ => f hk

/-- The sum over tokens i and channels n of tk[i] ec[n] f i n. A claim's `xl`
(Att/RunsP.lean:203-209) on a table whose weight vector is `lng` of a channel point and tk
(Att/TablesP.lean:172-176): the claim's weights are eq of the channel point's first coordinates, the
table's are eq of its last ls coordinates times tk; ec is eq of the whole channel point. -/
def atTokens (tk ec : Array E) (f : Nat → Nat → E) : E :=
  underN tk fun i => underN ec fun n => f i n

/-- Plane x of pair b at a point of its region, e being eq of that point as a table. A claim's
`plane` (Att/RunsP.lean:190-196) on a table whose weight vector is eq of the point's last lmS
coordinates (`addAs` at `lastN`, Att/TablesP.lean:163-169, :203-204). -/
def planeAt (w : K5In) (onDiag : Bool) (e : Array E) (x b : Nat) : E :=
  underN e fun n => w.c onDiag x b n

/-- The softmax weight of pair b at the point pt of its region: plane 3 + 128 + 256 plane 4.
After `valueProduct`, Att/RunsP.lean:342-344. -/
def weightAt (w : K5In) (onDiag : Bool) (pt : Array E) (b : Nat) : E :=
  let e := eqTab pt
  addE (addE (planeAt w onDiag e 3 b) (ofNat 128)) (mulE (planeAt w onDiag e 4 b) (ofNat 256))

/-! ## A softmax-table unit: query times key -/

/-- **The summand of the softmax-table unit number i**, which is the row's part i. The variables:
head of keys and values; below the diagonal slot row and tile slot, on it the tile; channel. W:
`scoreW` at the unit's call's key point (Att/LeftP.lean:57-68), called. A_b: `endValues`' first
claim (Att/RunsP.lean:268) on the table tQ (Att/TablesP.lean:215-216): the queries of the piece's
pair under eq(r's first lgk coordinates, head), the token weights tok (scoreTiles at r).1 zi, and
eq(r's last ldh coordinates, channel). B_b: its second claim (:270) on the table tK
(Att/TablesP.lean:217): the keys of the piece's layer, with (scoreTiles at r).2 and zj. `scoreTiles`
reads the unit's flag and the sumcheck's challenges alone: r is laid in their place. -/
def sK (P : Pub5) (w : K5In) (c : Chal) (i : Nat) : Summand :=
  let g := P.g
  let vars := (cut P.x).getD i 3 - 3
  let np := ((g.scores[i]?).map (·.pcs.length)).getD 0
  match g.scores[i]?, (ptsOf P c).bind (·.scores[i]?) with
  | some u, some k =>
    let key := c.zk.getD u.call #[]
    let tiles (r : Array E) : Array E × Array E :=
      scoreTiles g { k with sc := { k.sc with r := r } }
    ofProducts vars np (fun r => (scoreW g u key r).getD #[])
      (fun r b =>
        let p := k.pw.getD b ⟨0, 0, zeroE⟩
        let tk := tok g (tiles r).1 k.zi
        let ec := eqTab (lastCoords r g.ldh)
        overHeads g r fun hk => atTokens tk ec fun pos ch => w.q (pairOf g p) hk pos ch)
      (fun r b =>
        let p := k.pw.getD b ⟨0, 0, zeroE⟩
        let tk := tok g (tiles r).2 k.zj
        let ec := eqTab (lastCoords r g.ldh)
        overHeads g r fun hk => atTokens tk ec fun pos ch => w.kx p.lam hk pos ch)
  | _, _ => noProducts vars np

/-! ## The division and the value product -/

/-- What the three sumchecks of the division and the value product share; nothing of it hangs on a
point of theirs. -/
structure DivIn where
  /-- the verifier's named points and weights at the challenges so far -/
  d : DivP
  /-- the weights of the pieces of the list of the remainders' low bits, and that list's inner
  point, as
  `leftP` takes them (Att/LeftP.lean:102-104) -/
  pw : Array E
  zW : Array E
  /-- what was heard so far, in the verifier's form -/
  h : Heard
  /-- eq of the channel point zcW, as a table -/
  ec : Array E

/-- These, of the challenges so far; nothing where `pointsOf` refuses or the place lacks that list.
-/
def divIn (P : Pub5) (c : Chal) : Option DivIn := do
  let pts ← ptsOf P c
  let wl ← P.g.single .wl
  let key := c.zk.getD wl.call #[]
  pure ⟨pts.d, weights wl key, inner wl key, heardAt P c fun _ => none, eqTab pts.d.zcW⟩

/-- **Denominator times output.** The variables: head of keys and values; token. W: `wDivision`
(Att/K5LeftAll.lean:62-65, which is Att/LeftP.lean:109-110), called at what was heard, with r laid
in the place of this sumcheck's challenges. A_b: `endValuesE`'s first claim (Att/RunsP.lean:304,
with `readDenominator` :216-217) on the table hE (Att/TablesP.lean:200, :208): the denominators
under eq(r's first lgk coordinates, head) and eq(r's next lt coordinates, token). B_b: its second
claim (:306) on the table qO (Att/TablesP.lean:219): the outputs under the same two and eq(zcW,
channel). -/
def sSE (P : Pub5) (w : K5In) (c : Chal) : Summand :=
  let g := P.g
  let vars := (cut P.x).getD (iSE P.x) 3 - 3
  match divIn P c with
  | some D =>
    ofProducts vars g.NP (fun r => wDivision g D.pw D.zW { D.h with division := sumAt r })
      (fun r b =>
        let p := D.d.pwW.getD b ⟨0, 0, zeroE⟩
        let ei := eqTab (r.extract g.lgk (g.lgk + g.lt))
        overHeads g r fun hk => underN ei fun i => w.zd (pairOf g p) hk i)
      (fun r b =>
        let p := D.d.pwW.getD b ⟨0, 0, zeroE⟩
        let ei := eqTab (r.extract g.lgk (g.lgk + g.lt))
        overHeads g r fun hk => atTokens ei D.ec fun i ch => w.o (pairOf g p) hk i ch)
  | none => noProducts vars g.NP

/-- The verifier's points and weights of the division and the value product (`DivP`), with r in the
place of the challenges of the value product's sumcheck below the diagonal. Two fields hang on
these: the challenges themselves, and the tile columns' weights wJv, whose line is typed here after
`pointsOf`, Att/Points.lean:181-183 and :188. To call `pointsOf` itself at every point makes all the
place's points anew for each end value; a test (ProductsToy.lean) holds the two fields against that
call. -/
def belowAt (g : Geo) (d : DivP) (r : Array E) : DivP :=
  let atS := g.lgk + (g.lnT - 1)
  let w := tileSums g (eqTab (r.extract g.lgk atS)) (eqTab (r.extract atS (atS + g.lnT)))
  { d with vpm := { d.vpm with r := r }, wJv := w.2 }

/-- **The value product below the diagonal.** The variables: head of keys and values; slot row; tile
slot; the key's place in its tile. W: `wBelow` (Att/K5LeftAll.lean:67-72, which is
Att/LeftP.lean:111-114), called at what was heard, with r laid in the place of this sumcheck's
challenges. A_b: `valueProduct`'s first claim (Att/RunsP.lean:342-344, :353) on the table tVM
(Att/TablesP.lean:203): the softmax weight at the point `pointM`. B_b: its second claim (:345-346)
on the table qVM (Att/TablesP.lean:220): the batching element, plus the values of the piece's layer
under eq(r's first lgk coordinates, head), the token weights tok wJv (r's last lB coordinates), and
eq(zcW, channel). -/
def sVM (P : Pub5) (w : K5In) (c : Chal) : Summand :=
  let g := P.g
  let vars := (cut P.x).getD (iVM P.x) 3 - 3
  match divIn P c with
  | some D =>
    ofProducts vars g.NP (fun r => wBelow g D.pw D.zW { D.h with below := sumAt r })
      (fun r b =>
        let p := D.d.pwW.getD b ⟨0, 0, zeroE⟩
        weightAt w false (pointM g (belowAt g D.d r)) (pairOf g p))
      (fun r b =>
        let p := D.d.pwW.getD b ⟨0, 0, zeroE⟩
        let d := belowAt g D.d r
        let tk := tok g d.wJv (lastCoords d.vpm.r g.lB)
        addE d.gam (overHeads g d.vpm.r fun hk => atTokens tk D.ec fun pos ch =>
          w.v p.lam hk pos ch))
  | none => noProducts vars g.NP

/-- **The value product on the diagonal.** The variables: head of keys and values; tile; the key's
place in its tile. W: `wOn` (Att/K5LeftAll.lean:74-77, which is Att/LeftP.lean:115-116), called at
what was heard, with r laid in the place of this sumcheck's challenges. A_b: `valueProduct`'s first
claim (Att/RunsP.lean:342-344, :354) on the table tVD (Att/TablesP.lean:204): the softmax weight at
the point `pointD`, which reads this sumcheck's challenges and a cut of a key point alone: r is laid
in the challenges' place. B_b: its second claim (:345-346) on the table qVD
(Att/TablesP.lean:221-223): the batching element, plus the values under eq(r's first lgk
coordinates, head), the token weights tok (eq of r's next lnT coordinates) (r's last lB
coordinates), and eq(zcW, channel). -/
def sVD (P : Pub5) (w : K5In) (c : Chal) : Summand :=
  let g := P.g
  let vars := (cut P.x).getD (iVD P.x) 3 - 3
  match divIn P c with
  | some D =>
    ofProducts vars g.NP (fun r => wOn g D.pw D.zW { D.h with on := sumAt r })
      (fun r b =>
        let p := D.d.pwW.getD b ⟨0, 0, zeroE⟩
        weightAt w true (pointD g { D.d with vpd := { D.d.vpd with r := r } }) (pairOf g p))
      (fun r b =>
        let p := D.d.pwW.getD b ⟨0, 0, zeroE⟩
        let tk := tok g (eqTab (r.extract g.lgk (g.lgk + g.lnT))) (lastCoords r g.lB)
        addE D.d.gam (overHeads g r fun hk => atTokens tk D.ec fun pos ch => w.v p.lam hk pos ch))
  | none => noProducts vars g.NP

end H2K5.Honest
