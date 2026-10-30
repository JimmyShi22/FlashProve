-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Sides.lean: what the honest prover's second sumcheck over the tokens and its
batched sumcheck have in common: the verifier's own panels, and the values that the panels leave
open: the committed weights under each weight claim's factors, and the gated products. Definitions
with code. No theorem.

NOT SHOWN HERE. No theorem, and no test in this file. Nothing here says that the tables made here
are what the verifier's claims speak of: that is left to trials at fixed data
(Johnson/Desc/K4/Honest/SidesToyKit.lean). Which panels there are, their rows, columns, weights and
forms, and the list of the weight claims are the verifier's own functions
(OnBytes/Model/LayerPanels.lean: panelsA, panelsT, placePanels, ClaimEnv.weightClaims, headWeights,
ropeFactor); they are called here, not typed again.

The setting (docs/format/11-2-feed-forward-segment.md, "The panels of step 11"). The keys of the
segment's lookup hold inner products. A panel is a family of them: rows (layers, or the experts of
one layer) and columns (the index that is summed over), with a first factor FA and a second factor
FB at each place. The verifier's structure for a panel (SBlk) gives a factor as a linear form in the
reads where it is one. Two sorts of factor are no such form:
  * "weights": FB(row, column) is a sum over one unit of the committed weights, under the factors
    that the panel's weight claim gives to the unit's other indices;
  * a vector that is never sent: the gated product s u of a feature, summed over the tokens under
    the equality weights of a token point.
This file makes both.

  `Open`, `openOf`         one weight claim's unit, summed under the claim's factors, with the index
                          groups left open whose factor reads a challenge that is sampled later
  `Sides`, `Sides.of`       all that the two jobs share, of a place, the input, the sampled values
  `Sides.weights`, `Sides.kkOf`   each claim's table by (row,) column, at the equality table of a
                          token point; the length of its rows
  `at2`                    an entry of such a table
  `Sides.panels`          the verifier's panels, placed, at given values for the shown factors
  `Sides.gatedUnder`, `Sides.routedAt`   the gated products summed over the tokens under given
                          weights; where the routed experts' columns stand in that table
  `Sides.readsTok`        the honest reads with the second token sumcheck's end point at a point
  `endsOn`                the values that the second token sumcheck shows, on given reads
  `Trip`, `tripsOf`, `Sides.trips`, `Sides.summand`   the second pass's products at a token point

WHICH GROUPS ARE LEFT OPEN. A weight claim's factors on the groups named "kk" and "e" are made of
the batched sumcheck's challenges, and the factor on "cd" (the coordinate within a head) of the
second token sumcheck's end point. The other groups of a layer's unit are named "hd" and "x", AT A
LAYOUT MADE BY THE VERIFIER's `WsLay.build` (OnBytes/Model/Weights.lean), and the panels' claims
name layers' units alone (the embedding's unit has a group "v"); their factors are made of the
lookup's points, which are sampled in front of these rounds. So the unit is summed once under these
other factors, and "cd", "e", "kk" stay open. The claims are made with placeholders in the place of
the challenges that are not yet sampled; the factors that read the placeholders are those of the
open groups, which are not read. At a unit with a group of any other name `openOf` returns none.

Limits. The tables are as large as the panels: these are definitions for small sizes. `tripsOf`
returns none for a panel with two factors whose first factor is never sent: the verifier's list has
such a panel in the first pass alone. Where a table is read beyond its end the value is 0.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Desc.K4.Honest.Cube
import Johnson.Desc.K4.Honest.Units
import Johnson.Desc.K4.Honest.Gated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (Aff WsLay WsClaim eqTab lastOf longPoint)
open OnBytes.Model.Layer (Env SBlk PanelEnv ClaimEnv panelsA panelsT placePanels callsTS stubO)

/-! ## 1 The weights under a claim's factors -/

/-- **One weight claim's unit, summed under the claim's factors on the closed groups.** -/
structure Open where
  /-- by the open groups' indices in mixed radix, in the order "cd", "e", "kk" -/
  tab : Array E := #[]
  /-- the extent of the group "kk" -/
  kk : Nat := 0
  /-- the extent of the group "cd"; 0 if the unit has none -/
  cd : Nat := 0
  /-- the unit's layer, counted inside the group of layers -/
  lam : Nat := 0
  deriving Inhabited

/-- The table of one claim. g0: the number, in the model, of the group's first layer. It returns
none where the layout lacks the claim's unit, where the unit has a group that is named otherwise
than "hd", "x", "cd", "e", "kk", or where `fbFree` returns none. -/
def openOf (lay : WsLay) (w : Nat → Nat → F) (g0 : Nat) (c : WsClaim) : Option Open := do
  let u ← lay.U[c.ui]?
  if !(u.g.all fun G => ["hd", "x", "cd", "e", "kk"].contains G.name) then none
  let ext (n : String) : Nat := ((u.g.find? fun G => G.name == n).map (·.R)).getD 0
  let free := ["cd", "e", "kk"].filter fun n => u.g.any fun G => G.name == n
  let tab ← fbFree lay w c free
  pure { tab, kk := ext "kk", cd := ext "cd", lam := u.l - g0 }

/-- Entry (hi, yv) of a table whose rows have kk entries; 0 from column kk on. -/
def at2 (t : Array E) (kk hi yv : Nat) : E := if yv < kk then t.getD (hi * kk + yv) zeroE else zeroE

/-! ## 2 What the two jobs share -/

/-- **What the second token sumcheck's job and the batched sumcheck's job share.** -/
structure Sides where
  Q : K4Pub
  w : K4In
  /-- what the lookup in front has sampled -/
  fo : Model.Forest.Heard
  /-- the structure that the verifier's forms read -/
  v : Env
  /-- the numbers of the calls that have terms in the second token sumcheck -/
  TS : List Nat
  /-- the lookup's token point -/
  zt : Array E
  /-- the first ls coordinates of the point at which the lookup's long tables are read -/
  zlow : Array E
  /-- what the verifier's rotation factor reads; its challenges are placeholders -/
  ce : ClaimEnv
  /-- the equality table of the coordinates within a head, at the point of the queries' and keys'
  call -/
  lfc : Array E
  /-- the panels' weight claims, by their numbers -/
  opens : Array Open
  /-- the gated product s u of layer lam, feature x and token t, at the index (lam Pf + x) T + t -/
  hh : Tab
  /-- the verifier's claims on the values that the second token sumcheck shows, in the order sent:
  each is (the slot) less (a form in the reads at the sumcheck's end point) -/
  ends : List Aff

/-- **All that the two jobs share.** It reads, of the sampled values, what the lookup has sampled
alone. It returns none where `envOf` or one of the verifier's public functions returns none, where
`openOf` does, or where the layout lacks one of the two tensors of the gated products. -/
def Sides.of (Q : K4Pub) (w : K4In) (p : Pts) : Option Sides := do
  let y := Q.P.y
  let v ← envOf Q p
  let TS ← callsTS Q.P
  let Z ← (lastOf p.fo.zx y.h.la).toOption
  let ce : ClaimEnv :=
    { v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := Array.replicate Q.hp.lamS zeroE, rt := #[] }
  let cls ← ce.weightClaims TS
  let (_, lfc) ← ce.headWeights
  let opens ← cls.toArray.mapM (openOf Q.P.wsLay w.w (Q.g * y.Lam))
  let (gl, gr) ← gatedTabs Q w
  let ends ← termsForms v
    { fo := p.fo, PV := #[], ztF := #[], sW := 0, gp := #[], wpl := {}, sPv := 0, omV := #[],
      tV := {}, tT := some {} }
  let hh : Tab := (Array.range gl.size).map fun i => mulE (gl.getD i zeroE) (gr.getD i zeroE)
  pure
    { Q, w, fo := p.fo, v, TS, zt := ztOf Q p, zlow := Z.extract 0 y.ls, ce, lfc, opens, hh, ends }

namespace Sides

/-- The extent of the group "kk" of claim number a. -/
def kkOf (S : Sides) (a : Nat) : Nat := (S.opens.getD a {}).kk

/-- **Each claim's table by (row,) column.** et: the equality table of a token point. Where the unit
has the group "cd", that group is closed here under the verifier's rotation factor at et; every
other table is as it was made. A unit with "cd" is taken to have no group "e", as at a layout made
by `WsLay.build`: its table is read at the index c kk + column. -/
def weights (S : Sides) (et : Array E) : Array (Array E) :=
  S.opens.map fun o =>
    if o.cd == 0 then o.tab
    else
      let kap := S.ce.ropeFactor et S.lfc o.lam
      (Array.range o.kk).map fun k2 =>
        (List.range o.cd).foldl
          (fun s c => maddE s (kap.getD c zeroE) (o.tab.getD (c * o.kk + k2) zeroE)) zeroE

/-- **The verifier's panels**, both passes, in the list's order, each with its first place; and the
number of all places. shownT: what stands in the place of the values that the second token sumcheck
has shown. It returns none where the verifier's list does, or where the panels count another
number of weight claims than the verifier's list of claims has. -/
def panels (S : Sides) (shownT : Array E) : Option (Array SBlk × Nat) := do
  let pe : PanelEnv :=
    { v := S.v, e := S.fo.e, shownT, zt := S.zt, stubO := stubO S.v.y }
  let pans ← panelsT pe S.TS (panelsA pe {})
  if pans.nextV != S.opens.size then none
  pure (placePanels pans.bl)

/-- **The gated products summed over the tokens** under the weights et: at the index lam Pf + x. -/
def gatedUnder (S : Sides) (et : Array E) : Tab :=
  let T := S.v.y.T
  (Array.range (S.hh.size / T)).map fun i =>
    (List.range T).foldl (fun s t => maddE s (et.getD t zeroE) (S.hh.getD (i * T + t) zeroE)) zeroE

/-- The place, in a table by lam Pf + x, of column yv of the routed experts' never-sent vector of
the layer with routed experts number lm. -/
def routedAt (S : Sides) (lm yv : Nat) : Nat := (2 * lm + 1) * S.v.y.Pf + S.v.y.h.fe + yv

/-- The reads with the second token sumcheck's end point laid at z: the short tables of that point
("rt") at z, the long ones ("Y") at (zlow, z). A family of any other point has no weights in these
reads: `Reads.has` is false there. -/
def readsTok (S : Sides) (z : Array E) : Option Reads :=
  readsAt S.Q S.w S.fo [("rt", z), ("Y", longPoint S.zlow z)]

end Sides

/-- **The values that the second token sumcheck shows**, on given reads: each of the verifier's
claims on them is (the slot) less (a form); with 0 under every slot its value is minus the form's.
-/
def endsOn (S : Sides) (R : Reads) : Option (Array E) :=
  S.ends.toArray.mapM fun a => (valAff? S.v R (fun _ => zeroE) a).map negE

/-! ## 3 The second pass's products at a token point -/

/-- One product of the second token sumcheck's summand: its weight, its first and its second
factor. -/
abbrev Trip : Type := E × E × E

/-- **The products of one panel of the second pass.** val: a form's value on the reads at the token
point. F: the claims' tables at that point (`Sides.weights`). hh: the routed experts' never-sent
vector at that point: the layer's number among those with routed experts, the column.
A panel with two factors gives one product for each place: (the call's weight times the row's, FA,
FB). A panel whose rows carry the selector gives one product for each expert e: (the call's weight
times the panel's, the selector's entry, the sum over the columns of the column factor times
FB(e, column)). The number and the order of the products, and their weights, depend on public
numbers and on the lookup's points alone. -/
def tripsOf (S : Sides) (val : Aff → Option E) (F : Array (Array E)) (hh : Nat → Nat → E)
    (b : SBlk) : Option (Array Trip) :=
  let wt (i : Nat) : E := mulE b.ec (b.wt.getD i zeroE)
  if b.tri then do
    let v0 ← b.v0
    let cols ← (Array.range b.ny).mapM fun yv =>
      match b.virt with
      | some k => some (hh (k - 1) yv)
      | none => val (b.xx.getD yv {})
    let t := F.getD v0 #[]
    let kk := S.kkOf v0
    pure ((Array.range b.ni).map fun e =>
      (wt 0, b.sl.getD e zeroE,
        (List.range b.ny).foldl
          (fun s yv => maddE s (cols.getD yv zeroE) (at2 t kk e yv)) zeroE))
  else if b.virt.isSome then none
  else do
    let A ← b.A
    let rows ← (Array.range b.ni).mapM fun i =>
      (Array.range b.ny).mapM fun yv => do
        let a ← val (← A i yv)
        let c ← match b.v0, b.B with
          | none, some B => do val (← B i yv)
          | some v0, _ => some (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
          | none, none => none
        pure ((wt i, a, c) : Trip)
    pure (rows.flatMap id)

namespace Sides

/-- **All products of the second pass**, in the order of the verifier's list of panels. R: the reads
at the token point; et: the point's equality table; hh: as in `tripsOf`; shownT: the values in the
place of the shown factors. -/
def trips (S : Sides) (R : Reads) (et : Array E) (hh : Nat → Nat → E) (shownT : Array E) :
    Option (Array Trip) := do
  let (bl, _) ← S.panels shownT
  let F := S.weights et
  let l ← (bl.filter fun b => b.claim == 1).mapM
    (tripsOf S (fun a => valAff? S.v R (fun _ => zeroE) a) F hh)
  pure (l.flatMap id)

/-- **The second token sumcheck's summand at a point z, on given values of the shown factors**: each
other factor is taken at z by itself. -/
def summand (S : Sides) (shownT z : Array E) : Option E := do
  let R ← S.readsTok z
  let et := eqTab z
  let g := S.gatedUnder et
  let l ← S.trips R et (fun lm yv => g.getD (S.routedAt lm yv) zeroE) shownT
  pure (l.foldl (fun s x => maddE s x.1 (mulE x.2.1 x.2.2)) zeroE)

end Sides

end OnBytes.Desc.First.K4.Honest
