-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Merge.lean: what the honest prover of the layers' own rounds (K4) needs for
the claims on the committed weights: the list of the claims, the embedding's hidden value, and the
merge's sumcheck. Definitions with code. No theorem.

NOT SHOWN HERE. No theorem ties these definitions to the verifier's text. That `mergeClaimsAt` makes
the list that the verifier's hearing hands to its merge (`mergeClaims`,
OnBytes/Desc/First/K4/MergeClaims.lean) is by reading: it follows the same lines of
OnBytes/Desc/First/K4/Hear.lean and calls the same public functions, WITH ONE DIFFERENCE: the
request's tokens are read off the prover's input (`K4In.tokv`), where the verifier's `hear` reads
the field `Pub.tokv` of the structure that it is handed. The sub-protocol that seats `hear` lays the
tokens of the verifier's state into that field first (`hearAt`, Johnson/Desc/First/K4/Block.lean),
so the field of the place's own data (`K4Pub.P`) is read by neither side. That the input's tokens
are the state's is asked nowhere here. That the product of a claim's two tables, summed over the
columns, is the claim's value is not shown here. The letters lk, T, V and the names of the rounds
are those of the format's pages.

What the merge sums (docs/format/11-5-weights-in-the-table.md, "From a segment's claims to a row on
the table"; docs/format/11-1-machinery.md, "The merge"). The committed matrix has 2 ^ lk columns. A
claim's value is the sum over the columns c of a(c) b(c): a(c) is the claim's weight on column c,
and b(c) the sum over the rows of the claim's unit of (the claim's weight on the row) times the
entry in that row and column c. Claim number i, from 0, is taken times the power i of the element
that the round in front of the sumcheck samples. The sumcheck runs over the lk column bits, each
summed plainly, THE HIGHEST FIRST. The whole summand counts as one map of the column's number, and
its value at the challenges is the one end value.

  `colTab`, `rowTab`, `claimVal`    a claim's two tables, by column; its value
  `claimEnvOf`                      what the verifier's list of claims reads, of the sampled values
  `panelClaims`, `embClaim`, `mergeClaimsAt`   the panels' claims; the embedding's; all, in order
  `claimSame`                       a test: two claims are the same
  `embValue`                        the embedding's hidden value, sent in the first group alone
  `mergeJobOf`, `jobMerge`          THE MERGE's SUMCHECK: of a list of claims; at a place

WHICH MASK ENTRY LIES OVER THE END VALUE is not said here: a job holds true values alone. By the
format's page it is an entry of the request's index-mask message and not of the segment's mask row.

Limits. Where a factor of some panel's claim reads a challenge of the batched sumcheck,
`panelClaims` yields nothing while `Pts.rs` is empty, which it is until these challenges are all
sampled (`ptsOf`, Johnson/Desc/K4/Honest/Front.lean): the verifier's function returns none at a list
that lacks a challenge which it reads. `embClaim` yields nothing outside the first group, and where
there are not T tokens, each below the vocabulary's size. `rowTab` reads the matrix in the rows of
the claim's unit AT ALL 2 ^ lk COLUMNS, also where the claim's weight on the column is 0: the value
at the challenges hangs on these entries too. Its cost is one step for each such cell, for each
call; these are definitions for small sizes. A HYPOTHESIS ON THE LAYOUT, WHICH NOTHING HERE ASKS.
The sumcheck binds `colTab` as a table, so off the corners it reads the table's multilinear
extension. That extension is the verifier's `wsEpsT` at the challenges, which stands in the row that
the merge hands on, only where `wsEpsT` is a line in each coordinate. The library states that under
a condition on the unit, of a claim whose unit the layout has and which has one factor for each of
the unit's groups (`eps_multilinear` under `UnitOK`, Johnson/Road/FormsKeysMerge.lean,
FormsKeysWOk.lean), and the condition on the unit of every unit of a layout that the verifier's
maker returns (`unitOK_of_layout`, Johnson/Road/FormsKeysWLay.lean). No definition here calls these.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Front
import Johnson.Desc.K4.Honest.Cube
import Johnson.Desc.K11.Honest.Summand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (WsLay WsClaim wsGamma wsRowPart orderDefault)
open OnBytes.Model.Layer (ClaimEnv callsTS)

/-! ## 1 A claim's two tables, and its value -/

/-- A claim's weight on each column: the verifier's `wsEpsT` at the corners. Bit s of an entry's
number is column bit s. -/
def colTab (lay : WsLay) (c : WsClaim) : Tab :=
  (Johnson.Desc.First.ForkMerge.Honest.onColumns lay c).toArray

/-- Column by column: the rows of the claim's unit summed under the claim's weights on them, which
are the verifier's `wsGamma` of `wsRowPart` at the scalar 1. w: the committed matrix, by row and
column. A claim whose unit the layout lacks has the table of zeros: a padding of public data alone.
-/
def rowTab (lay : WsLay) (w : Nat → Nat → F) (c : WsClaim) : Tab :=
  match lay.U[c.ui]? with
  | none => Array.replicate (2 ^ lay.lk) zeroE
  | some u =>
    let gam := wsGamma u (wsRowPart lay c oneE) oneE
    Array.ofFn (n := 2 ^ lay.lk) fun col =>
      (gam.foldl (fun (s : E × Nat) k => (maddS s.1 (w (u.off + s.2) col.val) k, s.2 + 1))
        (zeroE, 0)).1

/-- **A claim's value**: the sum over the columns of the product of its two tables: the sum over the
unit's weights, each times the product of the claim's factors on its indices. -/
def claimVal (lay : WsLay) (w : Nat → Nat → F) (c : WsClaim) : E :=
  ((colTab lay c).zip (rowTab lay w c)).foldl (fun s y => maddE s y.1 y.2) zeroE

/-! ## 2 The claims -/

/-- What the verifier's list of weight claims reads, made as `hear` makes it
(OnBytes/Desc/First/K4/Hear.lean). -/
def claimEnvOf (Q : K4Pub) (p : Pts) : Option ClaimEnv :=
  (envOf Q p).map fun v =>
    { v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := p.rs, rt := p.rt }

/-- The weight claims of the panels, in the verifier's order. -/
def panelClaims (Q : K4Pub) (p : Pts) : Option (List WsClaim) := do
  let ce ← claimEnvOf Q p
  ce.weightClaims (← callsTS Q.P)

/-- The embedding's claim; nothing outside the first group. -/
def embClaim (Q : K4Pub) (w : K4In) (p : Pts) : Option WsClaim :=
  if Q.g == 0 then (claimEnvOf Q p).bind fun ce => ce.claimE p.ZE p.tkh Q.P.V w.tokv else none

/-- **The claims that the merge joins, in its order**: the panels'; then, in the first group, the
embedding's. -/
def mergeClaimsAt (Q : K4Pub) (w : K4In) (p : Pts) : Option (List WsClaim) := do
  let cp ← panelClaims Q p
  let ce ← if Q.g == 0 then (embClaim Q w p).map ([·]) else some []
  pure (cp ++ ce)

/-- Two claims are the same: the unit's number, and each factor's three arrays. -/
def claimSame (a b : WsClaim) : Bool :=
  a.ui == b.ui && a.f.length == b.f.length &&
    (a.f.zip b.f).all fun y => y.1.HV == y.2.HV && y.1.pt == y.2.pt && y.1.AV == y.2.AV

/-- **The embedding's hidden value**: its claim's value on the committed matrix. 0 where there is no
such claim. -/
def embValue (Q : K4Pub) (w : K4In) (p : Pts) : E :=
  ((embClaim Q w p).map (claimVal Q.P.wsLay w.w)).getD zeroE

/-! ## 3 The merge -/

/-- **The merge's sumcheck, of a list of claims.** rho: the claims' coefficients. The maps 2 i and
2 i + 1 are the two tables of claim number i; their pair has the weight rho[i]. No lead; degree 1 in
the further variable; one end value: the summand at the challenges. A claim for which rho has no
member counts with the weight 0. -/
def mergeJobOf (lay : WsLay) (w : Nat → Nat → F) (cls : List WsClaim) (rho : Array E) : Job :=
  let cube : Cube :=
    { n := lay.lk, order := orderDefault lay.lk, way := .plain
      maps := cls.foldl (fun a c => (a.push (colTab lay c)).push (rowTab lay w c)) #[]
      pairs := cls.zipIdx.map fun x => (rho.getD x.2 zeroE, 2 * x.2, 2 * x.2 + 1) }
  { lead := [], cube, dY := 1
    ends := fun rs => [cube.summandAt rs]
    atEnds := fun _ e => e.headD zeroE }

/-- **The merge's sumcheck** at a place: at the claims of `mergeClaimsAt`, under the powers of the
element that the round in front has sampled. -/
def jobMerge (Q : K4Pub) (w : K4In) (p : Pts) : Option Job :=
  (mergeClaimsAt Q w p).map fun cls => mergeJobOf Q.P.wsLay w.w cls p.rhoW

end OnBytes.Desc.First.K4.Honest
