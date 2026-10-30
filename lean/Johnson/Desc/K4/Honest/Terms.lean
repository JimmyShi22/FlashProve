-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Terms.lean: what the honest prover of the layers' own rounds (K4) sums in the
second sumcheck over the tokens. Definitions with code. No theorem.

NOT SHOWN HERE. No theorem, and no test in this file. That the claimed sum is the part of the
lookup's keys that it is meant to be is shown nowhere here: the verifier makes no claim of its own
on this sumcheck; what it leaves enters the start form of the batched sumcheck (`hearTerms`,
`joinStart`: OnBytes/Desc/First/K4/Hear.lean). This job is not held against that text here.

What is summed (docs/format/11-2-feed-forward-segment.md: step 9; "Three pieces of a key"; "What
C_11 stands for"). Some keys of the segment's lookup hold a term: a product of two vectors over the
tokens. The claimed sum is the sum over the tokens t, under the equality weights of the lookup's
token point, of all terms at t, each under the weight that the lookup's point gives to its key. The
batched sumcheck that follows proves the same terms with each term's two factors taken one by one at
this sumcheck's end point: they are the panels of its second pass.
SO THE SUMMAND IS MADE OF THE VERIFIER's OWN PANELS. For each token t the panels are made with the
end point laid at the corner t: the reads at that corner, the rotation at that token, the gated
products of that token, and, in the place of the values that this sumcheck will show, their true
values at t.
`Sides.trips` lists the panels' products as (weight, first factor, second factor). Product number k
gives two maps over the tokens, and the summand is the sum over k of the weight times the two maps.
Each factor is, as a function of the end point, multilinear (of degree at most 1 in each
coordinate), so the map's multilinear extension at a point is the factor at that point: this is by
reading, no law says so; trial 1 of Johnson/Desc/K4/Honest/SidesToyKit.lean holds at fixed data the
whole summand by the maps against the summand by the panels: one sum against one sum, no factor by
itself.

  `tokenRows`   for each token: the true values of what will be shown, and the panels' products
  `jobTermsOn`, `jobTerms`    THE SUMCHECK: of what the two jobs share; of a place

The end values, in the order sent: the reciprocal of each norm, the score of each layer with routed
experts, the selector's entries of each such layer: what the verifier's claims on them
(`termsForms`, OnBytes/Desc/First/K4/Claims.lean) say. Each occurs in the summand as a first factor
alone, so the summand has degree 1 in them, and so in the extra variable Y of the masked sumcheck,
in which each end value is its true value plus Y times its mask entry.

Limits. The job reads, of the sampled values, what the lookup has sampled alone. `atEnds` makes the
panels anew at the challenges and at the given end values; where `Sides.summand` returns none there,
it returns 0. The products' weights are taken from the first token; the job is not made if another
token's differ. No function here divides. The tables are laid anew at each call: definitions for
small sizes.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Sides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (eqTab orderDefault)
open OnBytes.Model.Layer (nEndT)

/-- **For each token**: the true values, at that token, of what the sumcheck will show, in the order
sent; and the products of the second pass's panels at that token. -/
def tokenRows (S : Sides) : Option (Array (Array E × Array Trip)) :=
  let y := S.v.y
  (Array.range y.T).mapM fun t => do
    let z := bitsOf y.h.lt t
    let R ← S.readsTok z
    let sh ← endsOn S R
    let tr ← S.trips R (eqTab z) (fun lm yv => S.hh.getD (S.routedAt lm yv * y.T + t) zeroE) sh
    pure (sh, tr)

/-- **The second sumcheck over the tokens.** The maps: first those of the end values, in the order
sent; then each product's first factor; then each product's second factor. It returns none where a
public function of the verifier rejects, where the sizes do not fit, or where a product's weight is
not the same at all tokens. -/
def jobTermsOn (S : Sides) : Option Job := do
  let y := S.v.y
  let lt := y.h.lt
  let rows ← tokenRows S
  let nE := nEndT y
  let first := (rows.getD 0 (#[], #[])).2
  let K := first.size
  let zero : Trip := (zeroE, zeroE, zeroE)
  let endMaps : Array Tab := (Array.range nE).map fun i => rows.map fun x => x.1.getD i zeroE
  let aMaps : Array Tab := (Array.range K).map fun k => rows.map fun x => (x.2.getD k zero).2.1
  let bMaps : Array Tab := (Array.range K).map fun k => rows.map fun x => (x.2.getD k zero).2.2
  let cube : Cube :=
    { n := lt, order := orderDefault lt, way := .point S.zt, maps := endMaps ++ aMaps ++ bMaps
      pairs := (List.range K).map fun k => ((first.getD k zero).1, nE + k, nE + K + k) }
  let sameWeights := rows.all fun x => x.2.map (·.1) == first.map (·.1)
  if !(cube.fits && sameWeights && rows.all fun x => x.1.size == nE && x.2.size == K) then none
  pure
    { lead := [cube.total], cube, dY := 1
      ends := fun rs => (endMaps.map fun t => mle t (cube.pointOf rs)).toList
      atEnds := fun rs e => (S.summand e.toArray (cube.pointOf rs)).getD zeroE }

/-- **The second sumcheck over the tokens**, of a place, the input and the sampled values. -/
def jobTerms (Q : K4Pub) (w : K4In) (p : Pts) : Option Job := (Sides.of Q w p).bind jobTermsOn

end OnBytes.Desc.First.K4.Honest
