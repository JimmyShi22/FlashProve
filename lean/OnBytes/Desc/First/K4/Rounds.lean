-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/Rounds.lean: the layers' own rounds as a table: in each round, how many field
elements the prover sends and how many the verifier draws.

K4, the layers' own rounds, is the part of a layers' sub-proof between the lookup on the calls and
the commitment to the reads. The technical report calls what it proves the constraints of a
feed-forward segment.

THE ROUNDS, IN ORDER (group g of layers; all numbers are the plan's).
  1. The verifier draws the norms' point over the tokens; in the first group also the embedding's
     two points.
  2. The prover sends the sums of limb products of all norms, hidden. One element batches them, a
     point joins the norms, and a masked sumcheck over a product layer proves the squares.
  3. The prover sends the row products, hidden. One element batches them, and a masked sumcheck over
     the tokens proves them at the norms' point.
  4. A second masked sumcheck over the tokens, at the lookup's token point; then one element joins
     its claim to the lookup's.
  5. The batched sumcheck over all panels of matrix products.
  6. A masked sumcheck over the product layer of the gated products; a point over the layers with
     routed experts; a second such sumcheck.
  7. In the first group the prover sends the embedding's value, hidden. One element batches the
     claims on the weights, and a masked sumcheck merges them into one.

A masked sumcheck of k rounds takes k + 3 rounds of the chain. First the prover sends the sum of a
hiding polynomial (over the tokens: the claimed value, hidden, in front of it), and an element joins
it to the claim. Then k rounds of two coefficients and a challenge. Then the coefficients of an
extra round over the end values, with a challenge that is never 0. Last the end values, to which the
verifier says nothing.

WHAT THIS TEXT COVERS (`covers`), FIVE CONDITIONS ON THE PLAN: norms of five limbs (xl = 5); routed
experts; more than one layer bit (ll > 1); more than one norm in the group (lNI ≠ 0); some call with
terms for the second token sumcheck. Every file in the stored scope meets these, and so does the
small stored example. At any other plan K4 refuses.

Main names (namespace `OnBytes.Desc.First.K4`): `covers`, `Rd`, `masked`, `rounds`, `Rd.fits`.
Limits. Definitions alone: no law ties the table to `hear`. Before `hear` runs, K4/Steps.lean and
K4/Block.lean hold a row's five numbers (`Rd.fits`) against the plan's entry and the view's round,
for each round of the stretch; what else a plan's entry says (its work; its bytes) is not asked
there.
-/
import OnBytes.Model.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- The plans for which K4 is written: five limbs; routed experts; ll > 1; lNI ≠ 0; the second token
sumcheck is not empty. -/
def covers (P : Pub) : Bool :=
  P.y.h.xl == 5 && P.y.h.p3 && P.y.h.ll > 1 && P.rd.lNI != 0 && !P.rd.tscCalls.isEmpty

/-- One round: its name in the plan; how many elements the prover sends; how many the verifier
draws, and how many of these by the rule that never gives 0; how many rows it batches. -/
structure Rd where
  name : RoundName
  sent : Nat := 0
  drawn : Nat := 1
  notZero : Nat := 0
  rows : Nat := 0

/-- A round in which the verifier draws a point of n coordinates. -/
def pointRd (r : RoundName) (n : Nat) : Rd := { name := r, drawn := n }

/-- A round that batches rows; the prover's message in front of it holds sent hidden values. -/
def batchRd (sent rows : Nat) : Rd := { name := .batSigma, sent, rows }

/-- A masked sumcheck of k rounds. first: the elements of its first message; y: the coefficients of
the extra round; ends: the end values. -/
def masked (k first y ends : Nat) : List Rd :=
  [{ name := .pscEpsilon, sent := first }] ++ List.replicate k { name := .pscRound, sent := 2 } ++
    [{ name := .pscY, sent := y, notZero := 1 }, { name := .pscValues, sent := ends, drawn := 0 }]

/-- A masked sumcheck over a product layer of mu variables, and the point on the line. -/
def layerRds (mu : Nat) : List Rd := masked mu 1 2 2 ++ [{ name := .line }]

/-- The own rounds of the sub-proof of group g, under the seven numbers of the head. -/
def rounds (P : Pub) (hp : HPlan2) (g : Nat) : List Rd :=
  let y := P.y
  let h := y.h
  let first := g == 0
  -- 1
  [pointRd .zero h.lt] ++
  (if first then [pointRd .zero (y.ls + h.lt), pointRd .zero (y.lPd - y.ls)] else []) ++
  -- 2
  [batchRd (ledNS h.xl * y.NI) (ledNS h.xl), pointRd .join P.rd.lNI] ++ layerRds P.rd.muV ++
  -- 3
  [batchRd (ledNP h.xl * y.NI) (ledNP h.xl * y.NI)] ++ masked h.lt 2 2 (ledNO h.xl * y.NI) ++
  -- 4
  masked h.lt 2 1 (nEndT y) ++ [batchRd 0 2] ++
  -- 5
  masked hp.lamS 1 2 (2 + (1 + y.LamM) + (hp.NCL - (if first then 1 else 0))) ++
  -- 6
  layerRds P.rd.muH ++ [pointRd .join (h.ll - 1)] ++ layerRds P.rd.muH2 ++
  -- 7
  [batchRd (if first then 1 else 0) hp.NCL] ++ masked P.wsLay.lk 1 1 1

/-- The row fits the plan's entry and the round as a view shows it. -/
def Rd.fits (d : Rd) (e : Fmt.Entry) (r : Fmt.RoundView) : Bool :=
  e.name == d.name.name && r.vals.length == d.sent && e.drawE == d.drawn &&
    r.drawn.elems.length == d.drawn && e.drawNZ == d.notZero && e.rows == d.rows

/-- How many rows of the table fit, row by row from the first. -/
def fitting : List Rd → List Fmt.Entry → List Fmt.RoundView → Nat
  | d :: ds, e :: es, r :: rs => (if d.fits e r then 1 else 0) + fitting ds es rs
  | _, _, _ => 0

end OnBytes.Desc.First.K4
