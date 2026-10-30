-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/SidesToyKit.lean: trials of the honest prover's second sumcheck over the
tokens and of its batched sumcheck (Johnson/Desc/K4/Honest/Terms.lean, Stack.lean), at two small
plans, on a synthetic input and synthetic challenges: the trials as definitions.
Johnson/Desc/K4/Honest/SidesToy.lean and SidesToyOdd.lean (neither is in this library; so here read:
not tested in this library) evaluate them. No theorem.

WHAT IT DOES NOT SHOW. No sumcheck is played here, and the verifier's lists of claims (`front`,
`back`: OnBytes/Desc/First/K4/Claims.lean) are not made: the masked rounds, the mask row, the ledger
and the start form of the batched sumcheck do not occur. Forms of single claims are valued, with no
ledger under them: those on the token sumcheck's end values (`termsForms`, with 0 under each slot:
trials 2, 4, 18, 19), the two that `stackEnd` returns (their values are two of the true end values)
and the weight claims (8, 23). The input is synthetic (Johnson/Desc/K4/Honest/Witness.lean): no
model is run. What the lookup has sampled is synthetic. Each trial compares field elements, or
counts, at fixed synthetic data; it says nothing at other data.

THE TWO PLANS. The first is Johnson/Desc/K4/Honest/ToyPlan.lean's. ALL ITS EXTENTS ARE POWERS OF
TWO, so no panel has a place beyond its rows or columns there, a row's stride 2 ^ wy cannot be told
from the number of columns, and every index group of the weights has one high part. The second plan
(`oddShape`) differs in the stream's width, 12, and in the number of heads, 3: the panels whose
columns run over the stream then have 12 columns in 16 places, and the index group "kk" of their
units has three high parts. A PLACE BEYOND A PANEL's ROWS IS MET AT NEITHER PLAN: the rows are
layers, layers with routed experts or experts, and the layout's maker
(OnBytes/Model/LayerLayout.lean) admits powers of two alone for these three numbers. `strideTrial`
lays the rows at the bent stride: the bend is not seen at the first plan and breaks trial 7 at the
second.

WHAT IS TRIED, in each run. The trials 1 to 4 are on the sumcheck over the tokens, 6 to 13 on the
batched one. Y is the extra variable of the masked sumcheck, in which each end value is its true
value plus Y times its mask entry.
   1  the summand by tables is the summand by the panels: the maps' extensions at a synthetic point,
      paired and weighted, give what the verifier's panels give when they are made at that point.
      THE MAPS' ENTRIES ARE MADE OF THE SAME PANELS, laid at the corners (`Sides.trips`): the trial
      holds the step from the corners to the point, not the products
   2  the end values by tables are the values of the verifier's forms for them at that point. The
      tables' entries are the same forms' values at the corners (`endsOn`): as in 1
   3  the summand has degree 1 in Y
   4  the claimed sum is the sum over the tokens, under the equality weights of the lookup's token
      point, of the panels' products at each token. BOTH SIDES ARE MADE OF THE SAME PRODUCTS: the
      trial holds how they are laid into tables (which product, which token, which weight) and the
      way of summing, not the products
   5  each of the two sumchecks has as many end values as the verifier's table of rounds
      (OnBytes/Desc/First/K4/Rounds.lean) says are sent in its last round. At the sumcheck over the
      tokens the job takes its number from the verifier's `nEndT`, which the table calls too: that
      half holds where the round stands (`starts`), not the number
   6  at synthetic challenges the product of the two long vectors' extensions is the product of the
      two numbers that the verifier's `stackEnd` makes of the true end values
   7  AT EVERY CORNER n the two numbers that `stackEnd` makes of the true end values there are SA[n]
      and SB[n]. At a never-sent vector both sides are made of one table: see 12 and 13
   8  the weight claims' end values are the values, on the committed matrix, of the verifier's own
      weight claims at these challenges
   9  THE TWO SUMCHECKS FIT: with the weights 0 and 1 for the two passes, the sum of SA[n] SB[n] is
      the token sumcheck's summand at its end point on the values AS SENT
  10  the summand has degree 2 in Y
  11  each of the verifier's panels has a place at which SA and SB are both other than 0
  12  the end value of the down product's never-sent vector is the sum of the first product layer of
      the gated products (Johnson/Desc/K4/Honest/Gated.lean). BOTH SIDES ARE MADE OF THE SAME TWO
      TABLES (`gatedTabs`): the trial holds the weights and the way of summing, not the products
  13  the routed experts' end values, under the equality weights of a synthetic point on their
      layers, give the sum of the second product layer. Both sides read the same two tensors through
      `layerTab`, laid twice (`gatedTabs`, `gatedTabs2`)
THAT THEY CAN FAIL: the trials 14 to 28: each turns one thing on one side of a trial above (a
weight, a cell, an entry of a table, a sent value or an end value raised by one; a degree stated too
low) and asks that the trial then breaks. Trial 5 compares counts, and trial 11 asks for values
other than 0; nothing here shows these two failing.

  `el`, `drawn`, `ptsAt`, `dot`, `raised`   synthetic numbers; small tools
  `oddShape`, `oddPlans`   the second plan
  `nHold`, `nAll`   how many of a run's trials must hold; how many trials a run has
  `runAt`   ONE RUN: its trials, each with whether it is as it must be
  `bentStride`, `strideTrial`   the trial on the rows' stride
  `Run`, `runsAt`, `smallRuns`, `oddRuns`   the runs at a plan
  `linesOf`, `tallyOf`   a print, as lines; the count

Limits. "As sent" is here: the true end value plus a synthetic factor times a synthetic mask entry.
No file of the library prints `linesOf`: it is for a sheet that evaluates it when a count is not as
it must be.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Terms
import Johnson.Desc.K4.Honest.Stack
import Johnson.Desc.K4.Honest.Merge
import Johnson.Desc.K4.Honest.ToyPlan
import Johnson.Desc.K4.Honest.ToyState
import Johnson.Desc.K4.Honest.Witness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.SidesToy
open OnBytes
open OnBytes.Model (fOfNat powers eqTab tenCell wsLayOf)
open OnBytes.Model.Layer (Pub HPlan2 Shape matIx)

/-- Synthetic element number i under a seed. -/
def el (seed i : Nat) : E :=
  let h (k : Nat) : F :=
    fOfNat (((seed * 1000003 + i * 7919 + k * 104729 + 12345) ^ 3) % 2305843009213693951)
  ⟨h 1, h 2, h 3⟩

/-- A synthetic challenge of n elements. -/
def drawn (seed n : Nat) : Fmt.Drawn :=
  ⟨(List.range n).map fun i => (el seed i).triple, [], [], none⟩

/-- The sampled values that the two jobs read: what the lookup has sampled, of six synthetic
challenges; the token sumcheck's end point; the element that joins the two passes. -/
def ptsAt (Q : K4Pub) (seed : Nat) : Pts :=
  { fo := toyLook Q.P ((toyFrontSizes Q.P).zipIdx.map fun x => drawn (seed + 10 * x.2) x.1)
    rt := (Array.range Q.P.y.h.lt).map (el (seed + 100))
    om := powers (el (seed + 200) 0) 2 }

/-- The sum of the products of two tables' entries. -/
def dot (a b : Tab) : E := (a.zip b).foldl (fun s x => maddE s x.1 x.2) zeroE

/-- A list with member number i raised by one. -/
def raised (l : List E) (i : Nat) : List E :=
  l.zipIdx.map fun x => if x.2 == i then addE x.1 oneE else x.1

/-- The second plan's shape: the first's, with a stream of width 12 in three heads. -/
def oddShape : Shape := { toyShape with d := 12, H := 3 }

/-- The second plan, made as Johnson/Desc/K4/Honest/ToyPlan.lean makes the first. -/
def oddPlans : Except String (Pub × Array HPlan2) := do
  let h := oddShape
  let y ← Model.Layer.layout h Model.Layer.Test.pc
  let sc ← Model.Layer.scalesOf h toyKL
  Model.Layer.scalesHeld h sc
  Model.Layer.noWrap h sc y.dq
  Model.Layer.weightWidthsHeld h y.kinds
  let wsLay ← wsLayOf
    { D := h.D, L := h.L, d := h.d, dh := h.dh, dkv := y.dkv, dq := y.dq, f := h.f, fe := h.fe,
      NE := h.NE, V := toyV } h.p3 toyLk
  let rope ← Model.Layer.ropeOf h
  let P ← Pub.of y sc rope wsLay toyV toyTokens { lidb := h.lidb, tau := h.tau, hb := 128 }
  pure (P, ← Model.Layer.plansG P)

/-- How many of a run's trials must hold; the others must break. -/
def nHold : Nat := 13

/-- How many trials a run has. -/
def nAll : Nat := 28

/-- **One run**: group g of layers, synthetic numbers under a seed. Each trial: its name, and
whether it is as it must be. None where a job cannot be made. -/
def runAt (x : Pub × Array HPlan2) (g seed : Nat) : Option (List (String × Bool)) := do
  let Q ← toyQOf x g
  let y := Q.P.y
  let lt := y.h.lt
  let lam := Q.hp.lamS
  let look := toyLook Q.P
  let m := made Q seed toyTokens
  let w := m.input look
  let p := ptsAt Q seed
  let S ← Sides.of Q w p
  -- the sumcheck over the tokens
  let J ← jobTermsOn S
  let rt := p.rt.toList
  let e3 := J.ends rt
  let masks := (List.range e3.length).map (el (seed + 300))
  let beta := el (seed + 400) 0
  let shown := (e3.zip masks).map fun z => addE z.1 (mulE beta z.2)
  let eR ← endsOn S (← S.readsTok p.rt)
  let gY := polyInY 1 (J.atEnds rt) e3 masks
  let byToken ← (List.range y.T).mapM fun t => do
    let z := bitsOf lt t
    S.summand (← endsOn S (← S.readsTok z)) z
  let sum := (byToken.zip (eqTab S.zt).toList).foldl (fun s z => maddE s z.1 z.2) zeroE
  -- the batched sumcheck
  let D ← stackDataOn S p shown.toArray
  let K := jobStackOn D
  let rsL := (List.range lam).map (el (seed + 500))
  let rsA := rsL.toArray.reverse
  let e4 := K.ends rsL
  let masks4 := (List.range e4.length).map (el (seed + 600))
  let shown4 := (e4.zip masks4).map fun z => addE z.1 (mulE beta z.2)
  let gY4 := polyInY 2 (K.atEnds rsL) e4 masks4
  let p4 : Pts := { p with rs := rsA, rhoM := (Array.range (y.h.ll - 1)).map (el (seed + 700)) }
  let cls ← panelClaims Q p4
  let D01 ← stackDataOn S { p with om := #[zeroE, oneE] } shown.toArray
  let second := dot D01.SA D01.SB
  let atShown ← S.summand shown.toArray p.rt
  let sentAt (k n : Nat) : Option Nat :=
    ((rounds Q.P Q.hp g)[(starts Q).getD k 0 + n + 2]?).map (·.sent)
  let G1 ← jobGated Q w p4
  let G2 ← jobGated2 Q w p4
  let routed := (((e4.drop 2).zip (eqTab p4.rhoM).toList).take y.LamM).foldl
    (fun s z => maddE s z.1 z.2) zeroE
  -- bent inputs: a digit of the first layer's queries' and keys' weights; a cell of the first
  -- norm's clamped output, of the selector, of a norm's reciprocal, of the gate's output
  let bentAt (c : Nat × Nat × Nat) : K4In := (bentCell m c.1 c.2.1 c.2.2).input look
  let u ← Q.P.wsLay.U[(← Q.P.wsLay.unitOf 0 (g * y.Lam))]?
  let wW := (bentWeight m u.off 0).input look
  let atShownW ← (← Sides.of Q wW p).summand shown.toArray p.rt
  let atShownC ← (← Sides.of Q (bentAt ((matIx y).iAD, 0, 0)) p).summand shown.toArray p.rt
  let sel ← y.T_ "sel"
  let Ss ← Sides.of Q (bentAt (featAt y sel.mat (tenCell sel.place 0 0 0) 0)) p
  let eRs ← endsOn Ss (← Ss.readsTok p.rt)
  let row ← y.T_ "row"
  let Sr ← Sides.of Q (bentAt (featAt y row.mat (tenCell row.place 0 0 80) 0)) p
  let eRr ← endsOn Sr (← Sr.readsTok p.rt)
  let ts ← y.T_ "s"
  let G1b ← jobGated Q (bentAt (featAt y ts.mat (tenCell ts.place 0 0 0) 0)) p4
  let G2b ← jobGated2 Q (bentAt (featAt y ts.mat (tenCell ts.place 0 1 y.h.fe) 0)) p4
  let nE := e3.length
  let bentCube : Cube :=
    { J.cube with maps := J.cube.maps.modify nE fun t => t.modify 0 (addE · oneE) }
  let n0 := (D.bl.getD 0 {}).off
  let atBent ← S.summand (raised shown 0).toArray p.rt
  pure
    [(" 1 tokens: tables against panels at a point", J.atEnds rt e3 == J.cube.summandAt rt),
     (" 2 tokens: end values against the verifier's forms", e3.toArray == eR && nE != 0),
     (" 3 tokens: degree 1 in Y", gY.length == 2 && valueP gY beta == J.atEnds rt shown),
     (" 4 tokens: the claimed sum, token by token", J.lead == [sum]),
     (" 5 both: the numbers of end values against the table of rounds",
        sentAt 2 lt == some nE && sentAt 3 lam == some e4.length),
     (" 6 batched: tables against stackEnd at a point", K.atEnds rsL e4 == K.cube.summandAt rsL),
     (" 7 batched: tables against stackEnd at every corner",
        (List.range (2 ^ lam)).all D.cornerAgrees),
     (" 8 batched: the weight claims' values",
        (e4.drop (3 + y.LamM)) == cls.map (claimVal Q.P.wsLay w.w) && !cls.isEmpty),
     (" 9 the two fit: the second pass's sum is the tokens' summand as sent", second == atShown),
     ("10 batched: degree 2 in Y", gY4.length == 3 && valueP gY4 beta == K.atEnds rsL shown4),
     ("11 batched: no panel is 0 throughout",
        !D.bl.isEmpty && D.bl.all fun b =>
          (List.range (b.ni * b.ny)).any fun i =>
            let n := b.off + i / b.ny * 2 ^ b.wy + i % b.ny
            !isZeroE (D.SA.getD n zeroE) && !isZeroE (D.SB.getD n zeroE)),
     ("12 batched: the down product's end value is the first product layer's sum",
        e4[1]? == some G1.cube.total),
     ("13 batched: the routed experts' end values give the second product layer's sum",
        routed == G2.cube.total),
     ("14 a weight raised by one on the tokens' side alone: 9", second != atShownW),
     ("15 a cell raised by one on the tokens' side alone: 9", second != atShownC),
     ("16 an entry of a map raised by one: 1", J.atEnds rt e3 != bentCube.summandAt rt),
     ("17 an entry of a map raised by one: 4", bentCube.total != sum),
     ("18 a cell of the selector raised by one under the forms alone: 2", e3.toArray != eRs),
     ("19 a digit of a norm's reciprocal raised by one under the forms alone: 2",
        e3.toArray != eRr),
     ("20 degree 0 stated: 3",
        valueP (polyInY 0 (J.atEnds rt) e3 masks) beta != J.atEnds rt shown),
     ("21 an entry of SA raised by one: 7, there",
        !({ D with SA := D.SA.modify n0 (addE · oneE) } : StackData).cornerAgrees n0),
     ("22 an entry of SB raised by one: 7, there",
        !({ D with SB := D.SB.modify n0 (addE · oneE) } : StackData).cornerAgrees n0),
     ("23 a weight raised by one under the verifier's claims alone: 8",
        (e4.drop (3 + y.LamM)) != cls.map (claimVal Q.P.wsLay wW.w)),
     ("24 a sent value raised by one: 9", second != atBent),
     ("25 an end value raised by one: 6", K.atEnds rsL (raised e4 1) != K.cube.summandAt rsL),
     ("26 degree 1 stated: 10",
        valueP (polyInY 1 (K.atEnds rsL) e4 masks4) beta != K.atEnds rsL shown4),
     ("27 a cell of the gate's output raised by one on the product layer's side alone: 12",
        e4[1]? != some G1b.cube.total),
     ("28 such a cell at a routed expert's feature, on the second product layer's side alone: 13",
        routed != G2b.cube.total)]

/-- SA with each panel's rows laid at the stride ny, the number of its columns, in the place of
2 ^ wy. -/
def bentStride (D : StackData) : Tab :=
  D.bl.foldl
    (fun t b =>
      (List.range (b.ni * b.ny)).foldl
        (fun t i =>
          t.setIfInBounds (b.off + i) (D.SA.getD (b.off + i / b.ny * 2 ^ b.wy + i % b.ny) zeroE))
        t)
    (Array.replicate D.SA.size zeroE)

/-- **The trial on the rows' stride**: how many panels have fewer columns than places for them; and
whether trial 7 breaks, at the first place that differs, when SA is laid at the bent stride. Where
no place differs the answer is false: the bend is then not seen. -/
def strideTrial (x : Pub × Array HPlan2) (g seed : Nat) : Option (Nat × Bool) := do
  let Q ← toyQOf x g
  let p := ptsAt Q seed
  let S ← Sides.of Q ((made Q seed toyTokens).input (toyLook Q.P)) p
  let shown := (Array.range (Model.Layer.nEndT Q.P.y)).map (el (seed + 800))
  let D ← stackDataOn S p shown
  let SA := bentStride D
  pure ((D.bl.filter fun b => b.ny < 2 ^ b.wy).size,
    match (List.range SA.size).find? fun n => SA.getD n zeroE != D.SA.getD n zeroE with
    | none => false
    | some n => !({ D with SA := SA } : StackData).cornerAgrees n)

/-- A run: what it is run at; its trials, or none if it could not be made. -/
abbrev Run : Type := String × Option (List (String × Bool))

/-- The runs at a plan: at each listed pair of a group of layers and a seed. The plan is made once.
-/
def runsAt (name : String) (plans : Except String (Pub × Array HPlan2)) (at_ : List (Nat × Nat)) :
    List Run :=
  match plans.toOption with
  | none => [(name ++ ": the plan", none)]
  | some x =>
    at_.map fun a => (s!"{name}, group {a.1}, synthetic numbers {a.2}", runAt x a.1 a.2)

/-- The first plan: two groups of layers, two lists of synthetic numbers. -/
def smallRuns : List Run := runsAt "the small plan" toyPlans [(0, 1), (0, 2), (1, 1), (1, 2)]

/-- The second plan: two groups of layers, one list each. -/
def oddRuns : List Run := runsAt "the plan of width 12" oddPlans [(0, 3), (1, 4)]

/-- **The count**: the runs that were made with all their trials; of these runs' trials, those that
must hold and do; those that must break and do. -/
def tallyOf (r : List Run) : Nat × Nat × Nat :=
  let ok := (r.filterMap (·.2)).filter (·.length == nAll)
  let count (l : List (String × Bool)) : Nat := (l.filter (·.2)).length
  (ok.length, (ok.map fun l => count (l.take nHold)).foldl (· + ·) 0,
    (ok.map fun l => count (l.drop nHold)).foldl (· + ·) 0)

/-- **A print, as lines.** -/
def linesOf (r : List Run) : List String :=
  let t := tallyOf r
  ["Trials of the honest prover's second token sumcheck and batched sumcheck, at synthetic data.",
   s!"Trials 1 to {nHold} must hold. Trials {nHold + 1} to {nAll} bend one thing, and the trial " ++
     "that is named behind the colon must then break."] ++
  (r.flatMap fun a =>
    a.1 :: match a.2 with
      | none => ["  this run could not be made: the plan's or a job's maker returned none"]
      | some l => l.zipIdx.map fun x =>
        let word :=
          if x.2 < nHold then (if x.1.2 then "holds" else "FAILS")
          else (if x.1.2 then "breaks, as it must" else "DID NOT BREAK")
        s!"  {x.1.1}: {word}") ++
  [s!"Runs made: {t.1} of {r.length}. Held: {t.2.1} of {r.length * nHold}. " ++
     s!"Broke, as they must: {t.2.2} of {r.length * (nAll - nHold)}."]

end OnBytes.Desc.First.K4.Honest.SidesToy
