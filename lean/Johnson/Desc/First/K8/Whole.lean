-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/Whole.lean: THE SMALLNESS TEST AS ONE BLOCK: its first half
  (Johnson/Desc/First/K8/Hear.lean: the draw of the matrix) with its second half laid into the same
  block's fields (Johnson/Desc/First/TailClaims/K8Claims.lean: the run of claims "K8.equations";
  behind the batching "K8.lsTail", then "K8.tests"). A JOIN: NO TEST AND NO FORMULA OF ITS OWN.
  DEFINITIONS, WITH CODE. NO THEOREM. NO SOUNDNESS IS CLAIMED.
HOW THE TWO MEET. The first half lays, at the draw, the matrix as one sequence and each matrix's
  first column. The second reads these two through `verify-on-bytes`'s sums over the matrix, which
  it calls by name, and beside them: the first free masking slot in front of the lookup on the
  digits and the first free one behind it (the lookup's block reads both off the ledger and lays
  them into the test's record) · the closed list of parts · what the lookup on the digits handed on.
TWO SIZES ON WHICH THE SECOND HALF LEANS ARE SO BY THE FIRST HALF's TESTS; THE SECOND HALF ASKS
  NEITHER: the sequence has (the record's columns) x (the record's combinations) entries: the frame
  holds the view's round against the declared round (columns p * p.tau entries), and tests (e) and
  (f) hold the place's numbers against the record's · there are NM + 1 first columns: firstColumns p
  has p.ks.length + 1, and test (d) holds that length against the record's NM.
WHERE THE RUNS STAND IN A LINK's ORDER is the driver's to say
  (Johnson/Desc/First/Driver/Chain.lean: orderCuts, orderAfterOf): it names this block's three runs
  by the names that they bear here.
The second half is typed at a part of the carried record (K8Part); here each run is lifted to the
  record: outside a link it refuses.
Written with K8Claims.lean and the files that it imports open.
-/
import Johnson.Desc.First.K8.AtS
import Johnson.Desc.First.TailClaims.K8Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-- The numbers of a place, for both halves. -/
structure ParW extends Par where
  /-- the plan's lengths of the vectors of reads at this place -/
  nU : Array Nat

/-- A run at the part, as a run at the record. -/
def atRecord {α : Type} (f : K8Part → Except String (α × K8Part)) (s : S) :
    Except String (α × S) :=
  match k8PartP.get? s with
  | none => .error "no link is open"
  | some q => (f q).map fun x => (x.1, k8PartP.set s x.2)

/-- **The kind, whole.** -/
def whole : Kind ParW S Claim := fun p =>
  { approximateRangeProofDrawKind (Cl := Claim) atS p.toPar with
    claims := k8Claims.map fun r => (r.1, fun front => atRecord (r.2 front))
    after := [k8LsTail, k8Tests p.nU].map fun r =>
      (r.1, fun s => (atRecord (fun q => (r.2 q).map fun q' => ((), q')) s).map (·.2)) }

end VerifiableInference.Desc.First.K8
