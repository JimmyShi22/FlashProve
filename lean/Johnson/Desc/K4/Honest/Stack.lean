-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Stack.lean: what the honest prover of the layers' own rounds (K4) sums in the
batched sumcheck of all inner products. Definitions with code. No theorem.

NOT SHOWN HERE. No theorem, and no test in this file. That the sum of the two long vectors' products
is the hidden value of the verifier's start form (`joinStart`, OnBytes/Desc/First/K4/Hear.lean)
depends on the lookup's join and on the sumcheck in front, and is shown nowhere here. To hold this
job against the verifier's three claims on it (`back`, OnBytes/Desc/First/K4/Claims.lean) is left to
a file that plays the whole row (Johnson/Desc/ProofFile/Honest/K4/Toy2.lean (no part of the library
yet)). `cornerAgrees` is a test's tool, not a test; Johnson/Desc/K4/Honest/SidesToyKit.lean (no
part of the library yet) calls it. THOSE TRIALS MEET A PANEL's PLACES BEYOND ITS COLUMNS AT ONE
SMALL PLAN ALONE (a stream of width 12), and places beyond a panel's rows at none: the layout's
maker admits powers of two alone for the numbers of rows. At the plan at which the whole row is
played every extent is a power of two.

What is summed (docs/format/11-2-feed-forward-segment.md: step 11; "The panels of step 11"). The sum
over n below 2 ^ lamS of SA[n] SB[n]. The two long vectors are made of panels. Which panels there
are, where each lies, its rows, columns and weights, and its factors as far as they are forms in the
reads are the verifier's own (`Sides.panels`). At the place off + row 2 ^ wy + column of a panel,
with om the weight of the panel's pass, ec that of its call and wt that of the row:
  * the down product's panel of the first pass, whose first factor is never sent:
      SA = om (the gated products under the lookup's token point),   SB = ec wt FB;
  * a panel whose rows carry the selector:
      SA = om ec wt (the selector's entry AS IT WAS SENT) (the column factor),   SB = FB;
  * every other panel:   SA = om ec wt FA,   SB = FB.
Outside the panels, and in a panel's places beyond its rows or columns, both are 0. FA and FB are
the values of the verifier's forms on the honest reads; where FB is "weights" it is the unit's
weights under the claim's other factors (`Sides.weights`). THE FIRST FACTORS THAT THE SECOND TOKEN
SUMCHECK HAS SHOWN ENTER AS THEY WERE SENT (shownT): so the job takes these sent scalars as an
argument.

The end values, in the order sent: A0; the down product's never-sent vector at the challenges; the
routed experts' never-sent vector at the challenges, for each layer that has them; B0; then each
weight claim's value, in the order of the claims. A0 and B0 are the values of the two forms that the
verifier's `stackEnd` returns for them. The summand on given end values is the product of the two
numbers that `stackEnd` makes of them: so it has degree 2 in the extra variable Y of the masked
sumcheck, in which each end value is its true value plus Y times its mask entry.

  `panelTabs`, `fillAt`, `longTabs`   a panel's two sides; the two long vectors
  `StackData`, `stackDataOn`, `stackData`   what the job's functions read, made once
  `StackData.val`, `nVirt`, `under`   a form's value; how many vectors are never sent; a sum
  `endsAt`, `sidesOn`, `summandOn`   the true end values; the two sides, and the summand, on given
                                    end values
  `jobStackOn`, `jobStack`            THE SUMCHECK
  `cornerAgrees` for a test: the long vectors against `stackEnd` at a corner

The order. The first round binds the highest bit of n. The verifier keeps the challenges by bit
(rs[t] for bit t); a list of challenges in the order of the rounds is that array reversed.

Limits. The second token sumcheck's end point and the element that joins the two passes must have
been sampled. Without the element `stackDataOn` returns none. Without the end point it returns none
where a panel's form names a point that is made of it ("rt", "Y"); a list of panels in which no form
does so is not refused for the lack of it. `endsAt` and `summandOn` return none where `stackEnd`
rejects, which depends on public numbers alone, and `endsAt` also where one of the two forms names
an entry of the reads whose point is not yet sampled; the job's functions then return the empty list
and 0. Neither the number of the sent scalars (shownT) nor that of given end values is tested: one
that lacks counts as 0. The tables have 2 ^ lamS entries and are laid anew at each call: definitions
for small sizes. No function here divides in the field.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Sides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (Aff eqTab eqLow orderDefault)
open OnBytes.Model.Layer (SBlk stackEnd)

/-! ## 1 The two long vectors -/

/-- **A panel's two sides**, row by row: entry row ny + column. val: a form's value on the honest
reads. om: the weights of the two passes. F: the claims' tables at the second token sumcheck's end
point. hZ, hR: the gated products under the lookup's token point and under that end point
(`Sides.gatedUnder`). -/
def panelTabs (S : Sides) (val : Aff → Option E) (om : Array E) (F : Array (Array E)) (hZ hR : Tab)
    (b : SBlk) : Option (Array E × Array E) :=
  let omb := om.getD b.claim zeroE
  let co := mulE omb b.ec
  let wt (i : Nat) : E := b.wt.getD i zeroE
  let grid (f : Nat → Nat → E) : Array E :=
    (Array.range (b.ni * b.ny)).map fun x => f (x / b.ny) (x % b.ny)
  if b.tri then do
    let v0 ← b.v0
    let cols ← (Array.range b.ny).mapM fun yv =>
      match b.virt with
      | some k => some (hR.getD (S.routedAt (k - 1) yv) zeroE)
      | none => val (b.xx.getD yv {})
    let c := mulE co (wt 0)
    let t := F.getD v0 #[]
    let kk := S.kkOf v0
    pure (grid fun e yv => mulE (mulE c (b.sl.getD e zeroE)) (cols.getD yv zeroE),
      grid fun e yv => at2 t kk e yv)
  else
    match b.virt with
    | some _ => do
      let v0 ← b.v0
      pure (grid fun i yv => mulE omb (hZ.getD (i * S.v.y.Pf + yv) zeroE),
        grid fun i yv =>
          mulE (mulE b.ec (wt i)) (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv))
    | none => do
      let A ← b.A
      let a ← (Array.range (b.ni * b.ny)).mapM fun x => do
        pure (mulE (mulE co (wt (x / b.ny))) (← val (← A (x / b.ny) (x % b.ny))))
      let c ← match b.v0, b.B with
        | none, some B =>
          (Array.range (b.ni * b.ny)).mapM fun x => do val (← B (x / b.ny) (x % b.ny))
        | some v0, _ =>
          some (grid fun i yv => at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
        | none, none => none
      pure (a, c)

/-- Lays a panel's side into a long vector. -/
def fillAt (b : SBlk) (x : Array E) (t : Tab) : Tab :=
  (List.range (b.ni * b.ny)).foldl
    (fun t i => t.setIfInBounds (b.off + i / b.ny * 2 ^ b.wy + i % b.ny) (x.getD i zeroE)) t

/-- **The two long vectors**, 2 ^ lam entries each. sides: each panel's two sides, in the order of
bl. -/
def longTabs (lam : Nat) (bl : Array SBlk) (sides : Array (Array E × Array E)) : Tab × Tab :=
  let lay (pick : Array E × Array E → Array E) : Tab :=
    (bl.zip sides).foldl (fun t x => fillAt x.1 (pick x.2) t) (Array.replicate (2 ^ lam) zeroE)
  (lay (·.1), lay (·.2))

/-! ## 2 The ends -/

/-- What the job's functions read. -/
structure StackData where
  S : Sides
  /-- the honest reads at the points sampled so far -/
  R : Reads
  /-- the verifier's panels, placed, at the shown values as they were sent -/
  bl : Array SBlk
  /-- the weights of the two passes -/
  om : Array E
  /-- the claims' tables at the second token sumcheck's end point -/
  F : Array (Array E)
  /-- the gated products under the lookup's token point; under that end point -/
  hZ : Tab
  hR : Tab
  SA : Tab
  SB : Tab

namespace StackData

/-- A form's value on the honest reads; none if it names an entry whose point is not yet sampled.
THE TEST IS ON EVERY ENTRY, whatever its coefficient (`affFits`): so whether a given form has a
value hangs on none of its coefficients. For the VALUE an entry whose coefficient is 0 is left out:
it adds 0; at a corner nearly all are such, and each entry that is valued costs a sum over cells. -/
def val (D : StackData) (a : Aff) : Option E :=
  if affFits D.S.v D.R a then
    some (valAff D.S.v D.R (fun _ => zeroE)
      { a with ents := a.ents.filter fun x => !isZeroE x.coef })
  else none

/-- The number of never-sent vectors. -/
def nVirt (D : StackData) : Nat := 1 + D.S.v.y.LamM

/-- The sum over row below ni and column below ny of EI[row] EY[column] f(row, column). -/
def under (EI EY : Array E) (ni ny : Nat) (f : Nat → Nat → E) : E :=
  (List.range ni).foldl
    (fun s i =>
      maddE s (EI.getD i zeroE)
        ((List.range ny).foldl (fun u yv => maddE u (EY.getD yv zeroE) (f i yv)) zeroE))
    zeroE

/-- **The true end values**, in the order sent. rs: the challenges by bit. -/
def endsAt (D : StackData) (rs : Array E) : Option (List E) := do
  let S := D.S
  let y := S.v.y
  let ncl := S.opens.size
  let fin ← stackEnd y D.bl rs S.Q.hp.lamS D.om (Array.replicate D.nVirt zeroE)
    (Array.replicate ncl zeroE) zeroE zeroE
  let A0 ← D.val fin.Alin
  let B0 ← D.val fin.Blin
  let dn ← D.bl.find? fun b => !b.tri && b.virt.isSome
  let H1 := under (eqLow rs dn.wy dn.w) (eqLow rs 0 dn.wy) dn.ni dn.ny
    fun i yv => D.hZ.getD (i * y.Pf + yv) zeroE
  let e2 := eqLow rs 0 y.lfe
  let H2 := (List.range y.LamM).map fun lm =>
    under #[oneE] e2 1 y.h.fe fun _ yv => D.hR.getD (S.routedAt lm yv) zeroE
  let V := D.bl.foldl
    (fun (V : Array E) b =>
      match b.v0 with
      | none => V
      | some v0 =>
        let EY := eqLow rs 0 b.wy
        if b.tri then
          V.setIfInBounds v0
            (under (eqLow rs b.wy b.w) EY b.ni b.ny (at2 (D.F.getD v0 #[]) (S.kkOf v0)))
        else
          (List.range b.ni).foldl
            (fun V i =>
              V.setIfInBounds (v0 + i)
                (under #[oneE] EY 1 b.ny
                  fun _ yv => at2 (D.F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv))
            V)
    (Array.replicate ncl zeroE)
  pure ([A0, H1] ++ H2 ++ [B0] ++ V.toList)

/-- The two numbers that the verifier's `stackEnd` makes of given end values: the two sides at the
challenges. rs: the challenges by bit. e: the end values in the order sent. -/
def sidesOn (D : StackData) (rs e : Array E) : Option (E × E) := do
  let nv := D.nVirt
  let fin ← stackEnd D.S.v.y D.bl rs D.S.Q.hp.lamS D.om (e.extract 1 (1 + nv))
    (e.extract (2 + nv) e.size) (e.getD 0 zeroE) (e.getD (1 + nv) zeroE)
  pure (fin.As, fin.Bs)

/-- **The summand at the challenges on given end values.** -/
def summandOn (D : StackData) (rs e : Array E) : Option E :=
  (D.sidesOn rs e).map fun x => mulE x.1 x.2

/-- For a trial: at the corner n, on the true end values there, the verifier's two numbers are
SA[n] and SB[n]. -/
def cornerAgrees (D : StackData) (n : Nat) : Bool :=
  let rs := (bitsOf D.S.Q.hp.lamS n).reverse
  match (D.endsAt rs).bind fun e => D.sidesOn rs e.toArray with
  | some x => x.1 == D.SA.getD n zeroE && x.2 == D.SB.getD n zeroE
  | none => false

end StackData

/-- **What the job's functions read**, made once. p: K4's own sampled values; what the lookup has
sampled is taken from S. shownT: the end values of the second token sumcheck as they were sent. It
returns none where a public function of the verifier rejects; where a form names a point that is not
yet sampled; where the element that joins the two passes is not yet sampled; where the panels'
places are not what the plan's number of rounds says, or the weight claims not as many as the plan
says. -/
def stackDataOn (S : Sides) (p : Pts) (shownT : Array E) : Option StackData := do
  let Q := S.Q
  let R ← readsAt Q S.w S.fo (namedPts Q { p with fo := S.fo })
  let (bl, places) ← S.panels shownT
  if ceilLog2 places != Q.hp.lamS || p.om.size != 2 ||
      S.opens.size != Q.hp.NCL - (if Q.g == 0 then 1 else 0) then none
  let et := eqTab p.rt
  let F := S.weights et
  let hZ := S.gatedUnder (eqTab S.zt)
  let hR := S.gatedUnder et
  let sides ← bl.mapM
    (panelTabs S (fun a => valAff? S.v R (fun _ => zeroE) a) p.om F hZ hR)
  let (SA, SB) := longTabs Q.hp.lamS bl sides
  pure { S, R, bl, om := p.om, F, hZ, hR, SA, SB }

/-- The same, of a place, the input and the sampled values. -/
def stackData (Q : K4Pub) (w : K4In) (p : Pts) (shownT : Array E) : Option StackData :=
  (Sides.of Q w p).bind fun S => stackDataOn S p shownT

/-! ## 3 The job -/

/-- **The batched sumcheck**, of what its functions read. -/
def jobStackOn (D : StackData) : Job :=
  let lam := D.S.Q.hp.lamS
  let cube : Cube :=
    { n := lam, order := orderDefault lam, way := .plain, maps := #[D.SA, D.SB]
      pairs := [(oneE, 0, 1)] }
  { lead := [], cube, dY := 2
    ends := fun rs => (D.endsAt rs.toArray.reverse).getD []
    atEnds := fun rs e => (D.summandOn rs.toArray.reverse e.toArray).getD zeroE }

/-- **The batched sumcheck**, of a place, the input and the sampled values. shownT: the end values
of the second token sumcheck as they were sent. -/
def jobStack (Q : K4Pub) (w : K4In) (p : Pts) (shownT : Array E) : Option Job :=
  (stackData Q w p shownT).map jobStackOn

end OnBytes.Desc.First.K4.Honest
