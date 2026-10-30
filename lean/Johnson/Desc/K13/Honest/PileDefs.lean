-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/PileDefs.lean: THE PILE's FILLER AND THE TWO LAWS THAT ARE ASKED OF IT: THE
DEFINITIONS, IN ONE FILE, OVER THE LIBRARY ALONE. Definitions: seven with code, two premises' forms.
No theorem.

What is wanted. Kind K13's honest part, and the data of the message W, read of each row on the pile
its weights and its column point. A filler yields these as a function of the public instance and the
challenges heard. Here it is made of the verifier's own functions, called by name, segment by
segment, CUT AT THE MERGES' CLAIMS: a row is made of what its segment's merge of the claims on the
weights leaves; that is a function of the merge's claims, its batching element and its column
challenges. The claims themselves are a parameter: each segment's, of the instance and the
challenges in front of the merge's batching round.
Two words. A chain's "sub-protocol number j" is entry number j of its list of blocks. A state
"without a mark" is one with failed = none.
Main names:
  `rowReadsOf lay S claims recs rm`: a pending row's weights and column point: the tests 4 to 19 of
    `pendingRowO` (Johnson/Desc/First/Pend/Row.lean) and its own functions, without the ledger.
  `mergeRecs lay cl sigma rm`: what a merge leaves of its claims: the one line that `flatForkEnd`
    (OnBytes/K/Kc/QuietLink.lean) and `mergeHear` (Johnson/Desc/First/Fork/MergeKind.lean) share.
  `mergeDraws lk own`: of the 2 + lk challenges from the batching round on: the batching element and
    the column challenges. It tests its own slice: nothing unless these are just 2 + lk challenges
    of one element each.
  `MergeSite`: a segment whose merge leaves a row: PUBLIC: its number, its number of claims, the
    number of its merge's batching round on the first chain.
  `SiteClaims Xi`: the parameter: by the segment's number: the claims, of the instance and THE
    CHALLENGES IN FRONT OF THE BATCHING ROUND.
  `pileRowAt`, `pileBySites`: a site's row; **the filler**: the sites' rows in the list's order. THE
    LIST's ORDER MATTERS AND NOTHING TESTS IT: the verifier lays a new row at the END of its pile
    (`pendingKept`, Johnson/Desc/First/Walk/Quiet.lean): so the sites must stand in the order in
    which their segments are cleared along the chain, the earliest first. ALL OR NOTHING: where one
    site yields nothing the pile is empty: no row comes to stand at another number. A row's mask
    form and target are idle: empty and 0.
  `PileIs bs start b n pile asked`: **the law on a filler, asked of the verifier's own fold**:
    wherever the fold over the first b sub-protocols, from the first state at the instance x,
    returns a state without a mark whose reply is the one asked: the filler at x and at what the
    first n rounds sampled, whatever is laid behind these, agrees with the state's pile in the rows'
    weights and column points.
  `ClaimsIs bs start j m lay left claims asked head`: **what is asked at a site, of the fold**: j:
    the number of the sub-protocol that merges; left: how what the merge left is read off the state.
    Wherever the fold over the first j + 1 sub-protocols returns a state without a mark (at the
    head: whose reply is the one asked): the parameter yields claims cl at what the rounds in front
    of the batching round sampled; `mergeDraws` returns at the next 2 + lk rounds; and the state
    holds what a merge of cl at these leaves.

What is not claimed. That any parameter meets `ClaimsIs` or any filler `PileIs`. The list of sites,
its order and its numbers at any plan; that a site's `ncl` is the public number of claims that the
verifier's text hands the row's function. That lay.lk is the shape's kCol: `rowReadsOf` gives the
column point lk coordinates, the batching asks kCol. These are none of the library's goals. Nothing
on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Pend.Row
import Johnson.Desc.First.State
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (span addClaim)

/-- **A pending row's weights and column point**: the tests 4 to 19 of `pendingRowO` and its own
functions, without the ledger. -/
def rowReadsOf (lay : WsLay) (S : LinShape) (claims : Nat) (recs : List WsRecClaim)
    (rm : Array E) : Option (List Tensor × List E) :=
  if lay.m0 == S.matrixRows && !recs.isEmpty && recs.length == claims && rm.size == lay.lk then
    match span lay recs with
    | .ok (first, last) =>
      if first < last ∧ last ≤ lay.m0 ∧ S.kRow ≤ 62 ∧ lay.m0 ≤ 2 ^ S.kRow then
        match recs.foldlM (addClaim lay) (Array.replicate last zeroE) with
        | .ok Gamma =>
          (VerifiableInference.Desc.Own.weightsOnRows S first (Gamma.extract first last)).map
            fun g => (g, rm.toList.reverse)
        | .error _ => none
      else none
    | .error _ => none
  else none

/-- **What a merge leaves of its claims**: claim number a under the scalar sigma^a times `wsEpsT` of
the claim at the merge's point (OnBytes/Model/Weights.lean: the product of the groups' factors on
their column bits, times 1 - the coordinate for each column bit that no group of the unit takes). -/
def mergeRecs (lay : WsLay) (cl : Array WsClaim) (sigma : E) (rm : Array E) : List WsRecClaim :=
  (cl.zip (Model.powers sigma cl.size)).toList.map fun y =>
    wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm))

/-- **A merge's batching element and its column challenges**, of the 2 + lk challenges from the
batching round on: the first; those from the third on. The second is the masked sumcheck's own first
challenge (the round "PSC epsilon"): no row reads it. -/
def mergeDraws (lk : Nat) (own : List Fmt.Drawn) : Option (E × Array E) :=
  if own.length == 2 + lk && own.all (fun d => d.elems.length == 1) then
    some ((own.flatMap fun d => d.elems.map E.ofTriple).headD zeroE,
      ((own.flatMap fun d => d.elems.map E.ofTriple).drop 2).toArray)
  else none

/-- **A segment whose merge leaves a row.** All three are public. -/
structure MergeSite where
  /-- the segment's number -/
  link : Nat
  /-- its public number of claims on the weights -/
  ncl : Nat
  /-- the number, from 0, of its merge's batching round on the first chain -/
  sigmaAt : Nat

variable {Xi Cl : Type}

/-- **The parameter**: by the segment's number: the claims that its merge merges, of the instance
and the challenges in front of the merge's batching round; nothing where they cannot be made. -/
abbrev SiteClaims (Xi : Type) : Type := Nat → Xi → List Fmt.Drawn → Option (Array WsClaim)

/-- A site's row, of the instance and the challenges heard. Its mask form and target are idle. -/
def pileRowAt (lay : WsLay) (S : LinShape) (claims : SiteClaims Xi) (x : Xi)
    (hd : List Fmt.Drawn) (m : MergeSite) : Option TensorRow := do
  let cl ← claims m.link x (hd.take m.sigmaAt)
  let y ← mergeDraws lay.lk ((hd.drop m.sigmaAt).take (2 + lay.lk))
  let q ← rowReadsOf lay S m.ncl (mergeRecs lay cl y.1 y.2) y.2
  pure { g := q.1, psi := q.2, masks := [], target := zeroE }

/-- **THE FILLER**: the sites' rows in the list's order: that must be the order in which the
segments are cleared along the chain, the earliest first: nothing tests it. ALL OR NOTHING. -/
def pileBySites (lay : WsLay) (S : LinShape) (sites : List MergeSite) (claims : SiteClaims Xi) :
    Xi → List Fmt.Drawn → List TensorRow :=
  fun x hd => (sites.mapM (pileRowAt lay S claims x hd)).getD []

/-- **THE LAW ON A FILLER, OF THE FOLD.** bs: the chain's sub-protocols. start: its first state, of
the instance. b: the border. n: how many rounds of the chain the filler may read: meant: at most as
many as the first b sub-protocols have. asked: what an instance asks about, as a field element. r,
c: the rounds and the columns that the fold leaves: free. -/
def PileIs (bs : List (Block S Cl)) (start : Xi → S) (b n : Nat)
    (pile : Xi → List Fmt.Drawn → List TensorRow) (asked : Xi → E) : Prop :=
  ∀ x rs cols s r c, foldBlocks 0 (bs.take b) (start x) rs cols = .ok (s, r, c) →
    s.failed = none → s.out.reply = some (asked x) → ∀ tl,
      ((pile x ((rs.take n).map (·.drawn) ++ tl)).map fun q => (q.g, q.psi)) =
        s.out.pending.map fun q => (q.g, q.psi)

/-- **WHAT IS ASKED AT A SITE, OF THE FOLD.** j: the number of the sub-protocol that merges. left:
how what the merge left is read off the state. head: the site is the head's: there the reply is
asked. -/
def ClaimsIs (bs : List (Block S Cl)) (start : Xi → S) (j : Nat) (m : MergeSite) (lay : WsLay)
    (left : S → Option WsForkOut) (claims : SiteClaims Xi) (asked : Xi → E) (head : Bool) : Prop :=
  ∀ x rs cols s r c, foldBlocks 0 (bs.take (j + 1)) (start x) rs cols = .ok (s, r, c) →
    s.failed = none → (head = true → s.out.reply = some (asked x)) →
    ∃ cl sigma w, claims m.link x ((rs.take m.sigmaAt).map (·.drawn)) = some cl ∧
      mergeDraws lay.lk (((rs.drop m.sigmaAt).take (2 + lay.lk)).map (·.drawn)) =
        some (sigma, w.rm) ∧
      left s = some w ∧ w.recs = mergeRecs lay cl sigma w.rm

end VerifiableInference.Desc.K13.Honest
