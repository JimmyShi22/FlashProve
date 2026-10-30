-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RidesMore.lean: WHAT MORE OF THE VERIFIER's STATE RIDES PAST AN
ACCEPTING RUN OF K10's SUB-PROTOCOL: beside the twelve fields of `k10_rides` (RidesBehind.lean,
beside this file). Statements and proofs. (In the Lean names a "block" is a sub-protocol.)

Why. Other files walk the first chain with relations between two states and ask each kind for its
own step: the links' result with the reply; the live frame's fields that the closing does not write;
each message's shape WITH its stored sample rows, as one pair; the groups' number, members and
flags.
  `behind_rows`: at every number the pair (shape, stored sample rows) of the message is as it was,
    at `spent (begun S g G) id` (StBehind.lean). `closing_sameRows`: so along `closing`'s yes: the
    same codes and these pairs: `SameRows` (Johnson/Top/H0/K2Hands/SampleChain.lean), written out.
  `closeFrame_frame`: the frame that `closeFrame` returns has the group, the groups' list, the
    shape, the moment and the own list of the frame that it took (`closeFrame_lays`, Lays.lean: it
    writes rows, mask, link, next alone).
  `k10_rides_more`: at a yes of `closeFrame` at what K10 reads of s, with s' K10's writing: s'.out =
    s.out (the reply in it); what K10 reads of s' has the frame that was returned: so the LIVE
    FRAME's GROUP behind is the live frame's group in front; the same codes and pairs (shape, stored
    sample rows); as many groups, each with its members and flags.
  `closing_no_runs`: K10's sub-protocol over the first chain's state has no run of claims and no run
    behind the batching.
Limits. WHAT DOES NOT RIDE: the closed group's mark (its test has begun) and its open rows (none are
left); its members' ledgers (closed); the mark "spent as a mask" at the fold's fresh mask; the live
frame's rows, mask, link and next; what was owed (nothing is). On the state alone. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.RidesBehind
import Johnson.Desc.First.Close.Law.GroupsStay
import Johnson.Desc.First.Close.Law.LensAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (recOf putRec)

/-- The pair that is asked to stay at a message. -/
abbrev rowsK (x : OnBytes.Oracle) : OracleShape × Array OnBytes.Row := (x.shape, x.sampleRows)

theorem behind_rows (T : Statement) (g : Nat) (G : Group) (id : Nat) (o : Nat) :
    ((spent (begun T g G) id).oracles[o]?).map rowsK = (T.oracles[o]?).map rowsK := by
  have h1 := behind_shape T g G id o
  have h2 := behind_samples T g G id o
  cases ha : (spent (begun T g G) id).oracles[o]? with
  | none =>
    rw [ha] at h1
    cases hb : T.oracles[o]? with
    | none => rfl
    | some y => rw [hb] at h1; cases h1
  | some x =>
    rw [ha] at h1 h2
    cases hb : T.oracles[o]? with
    | none => rw [hb] at h1; cases h1
    | some y =>
      rw [hb] at h1 h2
      have e1 : x.shape = y.shape := Option.some.inj h1
      have e2 : x.sampleRows = y.sampleRows := Option.some.inj h2
      show some (x.shape, x.sampleRows) = some (y.shape, y.sampleRows)
      rw [e1, e2]

/-- **Along the closing's yes: the same codes; each message's shape and stored sample rows.** -/
theorem closing_sameRows {P : Plan} {T T' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P T g mask rs = .ok (out, T')) :
    T'.codes = T.codes ∧ ∀ j : Nat, (T'.oracles[j]?).map rowsK = (T.oracles[j]?).map rowsK := by
  obtain ⟨G, id, -, -, rfl⟩ := closing_st h
  exact ⟨behind_codes T g G id, behind_rows T g G id⟩

/-- The frame that the frame's closing returns: what it does not write. -/
theorem closeFrame_frame {owed : Option Nat} {f : ReqFrame} {T : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f T es rs = .ok x) :
    x.1.group = f.group ∧ x.1.groups = f.groups ∧ x.1.shape = f.shape ∧
      x.1.moment = f.moment ∧ x.1.own = f.own := by
  obtain ⟨Gr, rows, -, -, e⟩ := closeFrame_lays (f' := x.1) (S' := x.2) h
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **WHAT MORE RIDES PAST AN ACCEPTING RUN OF K10's SUB-PROTOCOL.** -/
theorem k10_rides_more (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView) (x : ReqFrame × Statement)
    (hx : closeFrame (recOf s).owed (recOf s).frame (recOf s).st es rs = .ok x) :
    (putRec s ⟨none, x.1, x.2⟩).out = s.out ∧
      (recOf (putRec s ⟨none, x.1, x.2⟩)).frame = x.1 ∧
      (recOf (putRec s ⟨none, x.1, x.2⟩)).frame.group = (recOf s).frame.group ∧
      (putRec s ⟨none, x.1, x.2⟩).st.codes = s.st.codes ∧
      (∀ j : Nat, ((putRec s ⟨none, x.1, x.2⟩).st.oracles[j]?).map rowsK =
        (s.st.oracles[j]?).map rowsK) ∧
      (putRec s ⟨none, x.1, x.2⟩).st.groups.size = s.st.groups.size ∧
      ∀ g' : Nat, ((putRec s ⟨none, x.1, x.2⟩).st.groups[g']?).map memK =
        (s.st.groups[g']?).map memK := by
  obtain ⟨Gr, rows, -, hc, -⟩ := closeFrame_lays (f' := x.1) (S' := x.2) hx
  have hf := (recOf_putRec s ⟨none, x.1, x.2⟩).1
  refine ⟨(putRec_keeps s _).2.2.2.1, hf, ?_, (closing_sameRows hc).1, (closing_sameRows hc).2,
    (closing_groups hc).1, (closing_groups hc).2⟩
  rw [hf]
  exact (closeFrame_frame hx).1

/-- K10's sub-protocol has no run of claims and no run behind the batching. -/
theorem closing_no_runs {Cl : Type} (Q : Par) :
    (K9.closing (Cl := Cl) Q).claims = [] ∧ (K9.closing (Cl := Cl) Q).after = [] := ⟨rfl, rfl⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.behind_rows
#print axioms VerifiableInference.Desc.First.Close.closing_sameRows
#print axioms VerifiableInference.Desc.First.Close.closeFrame_frame
#print axioms VerifiableInference.Desc.First.Close.k10_rides_more
#print axioms VerifiableInference.Desc.First.Close.closing_no_runs
