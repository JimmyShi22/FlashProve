-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Gated.lean: what the honest prover of the layers' own rounds (K4) sums in the
two product layers of the gated products. Definitions with code. No theorem.

NOT SHOWN HERE. No theorem ties these tables to the verifier's text. Which cell holds which value is
`tensorAt`'s (Johnson/Desc/K4/Honest/Cells.lean). Nor is it shown here that the two end values are
what the verifier's claims on them say (`gatedForms`, OnBytes/Desc/First/K4/Claims.lean), that the
sums are the hidden values from which the two layers start, or that the claim which each sumcheck
leaves is 0. The letters (T, f, fe, Pf, ll, lPf, lfe, mu) are those of the format's page.

What is summed (docs/format/11-2-feed-forward-segment.md: steps 12 and 14; "The scalars by name";
groups 8 and 9 of the claims). The gated product of a layer is hh = sl up, feature by feature and
token by token; sl and up are committed, hh is not. A product layer is a masked sumcheck whose
summand is the product of two maps, summed under the equality weights of a point.
  Step 12, all layers of the group: the maps are MINUS sl and MINUS up under the index
  (lam Pf + x) T + t, for layer lam, feature x below f and token t; 0 for x from f on. The point:
  the challenges of the bits ll + lPf - 1 down to 0 of the batched sumcheck, then the lookup's token
  point.
  Step 14, the layers with routed experts: the same two tensors at layer 2 m + 1 and feature fe + x,
  under the index (m fe + x) T + t, for x below fe. The point: the point sampled on these layers'
  numbers, the challenges of the bits lfe - 1 down to 0 of the batched sumcheck, then the end point
  of the second token sumcheck.
Both layers bind their variables in the order 2, 1, 0, 5, 4, 3, 8, 7, 6 and then from the highest
down to 9 (`orderRange`). The two signs cancel in the product.

  `layerTab`                 minus a tensor, as a table over (row, feature, token)
  `gatedTabs`, `gatedTabs2`    the two tables of step 12; of step 14: THEY READ NO SAMPLED VALUE
  `levelJob`                 a product layer's sumcheck, of its point and its two tables
  `jobGated`, `jobGated2`      THE TWO SUMCHECKS

Limits. The names of the two tensors in the layout are "s" and "u". The index of step 14 takes fe
for a power of two: the layout's maker rejects another fe where there are routed experts
(`layoutBase`, OnBytes/Model/LayerLayout.lean). It also asks f = 2 fe there, and the verifier's text
of these rounds covers plans with routed experts alone: so at every plan that it covers Pf is f, and
the branch "0 for x from f on" is never reached; no test reaches it. BOTH LAYERS WANT AT LEAST 9
VARIABLES: `orderRange` lists nine variables at the least, so below that the order does not fit the
cube; the verifier's `OnBytes.Model.Layer.readsOf` (OnBytes/Model/LayerLayout.lean) rejects such a
plan. A table has 2 ^ mu entries and is laid anew at each call. A point that is not yet sampled
whole is too short: its coordinates then fall on other variables than they are meant for, and a
coordinate that lacks is read as 0; a job is meant to be asked when the challenges in front of its
part have all been sampled.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Desc.K4.Honest.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (orderRange)
open OnBytes.Model.Layer (Lay Ten downFrom)

/-- **Minus a tensor, as a table of 2 ^ mu entries.** Entry (r stride + x) T + t holds minus the
tensor's value at instance lamOf r, feature first + x and token t, for x below width, and 0 for x
from width on. -/
def layerTab (y : Lay) (cell : Nat → Nat → Nat → F) (X : Ten) (mu stride width : Nat)
    (lamOf : Nat → Nat) (first : Nat) : Tab :=
  Array.ofFn (n := 2 ^ mu) fun i =>
    let x := i.val / y.T % stride
    if x < width then
      negE (tensorAt y cell X (lamOf (i.val / y.T / stride)) (first + x) (i.val % y.T))
    else zeroE

/-- The two tables of step 12: minus sl, minus up. Nothing if the layout lacks one of the tensors.
-/
def gatedTabs (Q : K4Pub) (w : K4In) : Option (Tab × Tab) := do
  let y := Q.P.y
  let ts ← y.T_ "s"
  let tu ← y.T_ "u"
  let tab (X : Ten) : Tab := layerTab y w.cell X Q.P.rd.muH y.Pf y.h.f id 0
  pure (tab ts, tab tu)

/-- The two tables of step 14. -/
def gatedTabs2 (Q : K4Pub) (w : K4In) : Option (Tab × Tab) := do
  let y := Q.P.y
  let ts ← y.T_ "s"
  let tu ← y.T_ "u"
  let tab (X : Ten) : Tab :=
    layerTab y w.cell X Q.P.rd.muH2 y.h.fe y.h.fe (fun m => 2 * m + 1) y.h.fe
  pure (tab ts, tab tu)

/-- A product layer's sumcheck: two maps, one pair of weight 1; no lead; degree 2 in the further
variable; the two end values are the maps at the challenges, and the summand on end values is their
product. -/
def levelJob (mu : Nat) (order : List Nat) (rho : Array E) (t : Tab × Tab) : Job :=
  let cube : Cube :=
    { n := mu, order, way := .point rho, maps := #[t.1, t.2], pairs := [(oneE, 0, 1)] }
  { lead := [], cube, dY := 2
    ends := fun rs => (cube.valuesAt rs).toList
    atEnds := fun _ e => mulE (e.getD 0 zeroE) (e.getD 1 zeroE) }

/-- **Step 12.** -/
def jobGated (Q : K4Pub) (w : K4In) (p : Pts) : Option Job :=
  (gatedTabs Q w).map
    (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p))

/-- **Step 14.** -/
def jobGated2 (Q : K4Pub) (w : K4In) (p : Pts) : Option Job :=
  (gatedTabs2 Q w).map
    (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2) (p.rhoM ++ downFrom p.rs Q.P.y.lfe ++ p.rt))

end OnBytes.Desc.First.K4.Honest
