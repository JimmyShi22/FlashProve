-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/SeatN.lean: kind K5's block at an attention segment of the first chain, with
its four named runs of claims typed at the one type of a claim (Claim, Johnson/Desc/Claim.lean).

  `claimOf f`: the claim that the form f is 0: no runs of entries; the claim's own number's weight.
  `runsN A`: runsO A (Johnson/Desc/First/Att/SeatO.lean): "first", "keys", "join", "second", in that
    order, under these names; each run's list of forms carried to claims by claimOf; the record
    behind the run and every refusal as they are.
  `k5AtN W l g before`: attentionKind seatSO (runsN p) at segment l, group g, with the claims' tests on the
    plan (claimsOkAtO) beside the hearing's. None where W has no plan of group g.
  `runsN_names`, `k5AtN_states`: the four names in that order; no run behind the batching; the
    place.
  `runN_ok`, `claimOf_plain`: a run of claims returns just where the run of forms does, the same
    record, the forms' claims; each claim is a form alone.
It is k5AtO (Att/SeatO.lean) at another type of claims: the hearing, the tests on the plan and the
runs' texts are that block's. The names are those under which the driver's order of an attention
segment asks for them of the segment's hearing block number 2 (orderCuts,
Johnson/Desc/First/Driver/Chain.lean).

Definitions with code, and what they unfold to. Nothing is claimed on soundness, completeness or
hiding.

-/
import Johnson.Desc.Claim
import Johnson.Desc.First.Att.SeatO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)

/-- The claim that the form is 0. -/
def claimOf (f : Aff) : Claim := { form := f }

/-- A run of forms as a run of claims. -/
def runN (r : Nat → First.S → Except String (List Aff × First.S)) (n : Nat) (s : First.S) :
    Except String (List Claim × First.S) :=
  (r n s).map fun y => (y.1.map claimOf, y.2)

/-- K5's four named runs, typed at Claim. -/
def runsN (A : Attention.Plan) :
    List (String × (Nat → First.S → Except String (List Claim × First.S))) :=
  (runsO A).map fun r => (r.1, runN r.2)

/-- K5's block at segment l, group g, with its runs. -/
def k5AtN (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) :
    Option (VerifiableInference.Desc.Block First.S Claim) :=
  (W.A[g]?).map fun p =>
    let b := attentionKind seatSO (runsN p)
      { link := l, piece := 3, work := (Params.settingOf W.P.frame).workOf .field .request
        own := p.own, before := before }
    { b with planOk := b.planOk && claimsOkAtO p }

/-- The four names, in the driver's order. -/
theorem runsN_names (A : Attention.Plan) :
    (runsN A).map (·.1) = ["first", "keys", "join", "second"] := rfl

/-- What the block states, and where: the four lists, no run behind the batching, piece 3, kind
K5. -/
theorem k5AtN_states {W : Verify.Public} {l g : Nat} {before : List (Nat × Nat)}
    {b : VerifiableInference.Desc.Block First.S Claim} (h : k5AtN W l g before = some b) :
    b.claims.map (·.1) = ["first", "keys", "join", "second"] ∧ b.after = [] ∧
      b.place = ⟨1, some l, 3, .K5⟩ := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, rfl, rfl⟩

/-- A run of claims returns just where the run of forms does: the same record; the forms' claims. -/
theorem runN_ok {r : Nat → First.S → Except String (List Aff × First.S)} {n : Nat} {s : First.S}
    {y : List Claim × First.S} (h : runN r n s = .ok y) :
    ∃ l, r n s = .ok (l, y.2) ∧ y.1 = l.map claimOf := by
  unfold runN at h
  cases e : r n s with
  | error w => rw [e] at h; cases h
  | ok x =>
    rw [e] at h
    cases h
    exact ⟨x.1, rfl, rfl⟩

/-- Each claim of the runs is a form alone. -/
theorem claimOf_plain (f : Aff) :
    (claimOf f).form = f ∧ (claimOf f).runs = #[] ∧ (claimOf f).eqFirst = none :=
  ⟨rfl, rfl, rfl⟩

end VerifiableInference.Desc.First.Att.P
