-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/KeepsM.lean: CONDITIONAL: WHAT AN ACCEPTING STEP OF THE KIND "an
attention segment's own rounds" (K5) LEAVES OF THE VERIFIER's STATE, AS ONE CLAUSE WITH "NO MARK
BEHIND" INSIDE IT: an equation on the whole state behind. A definition, and lemmas on it over the
library alone.

The clause. `K5KeepsM x s s'` (x: the planner's numbers of these rounds, public): the state behind
bears no mark of failure; in front an attention segment stands open; the kind's hearing returns from
that segment's ledger at some rounds, all used up; AND THE STATE BEHIND IS THE STATE IN FRONT WITH
THREE FIELDS TURNED (`behind`, Johnson/Desc/First/Att/K05BehindLay.lean): the count of rows owed is
struck, the open segment's ledger is the one that the hearing returns, and what the segment's own
rounds have heard is laid. Nothing is asked of the state in front beside what the yes itself says.

Against `K5Keeps` (Johnson/Desc/K5/Honest/Law/Returns.lean). That older clause says "the mark is as
it was" and speaks of the two ledgers through two relations. `K5KeepsM` GIVES IT WHERE THE LEDGER IN
FRONT HAS ITS ARRAYS' LENGTHS (`k5Keeps_of_M`). NO CONVERSE IS SHOWN, and none is looked for: of the
mark `K5Keeps` says only that it is as it was (`k5Keeps_failed`), and it names no hearing.

  `K5KeepsM`             THE CLAUSE
  `k5KeepsM_of_decide`   CONDITIONAL: the kind's own decision's yes, with no mark behind, gives it
  `k5KeepsM_rest`        whatever is read through the library's `restO` is kept; so
  `k5KeepsM_clean`       the state in front bears no mark either
  `k5KeepsM_st`, `k5KeepsM_out`, `k5KeepsM_reply`, `k5KeepsM_pile`   the statement, what was put
                         out, the reply, and the number of rows on the pile are as they were
  `k5KeepsM_here`        of the open segment's own part all fields but the ledger and what its own
                         rounds have heard are as they were
  `k5KeepsM_not_head`    neither in front nor behind does the chain stand in the head's segment
  `k5Keeps_of_M`         CONDITIONAL: **`K5Keeps`**, where the ledger in front has its arrays'
                         lengths
  `k5Keeps_failed`       CONDITIONAL: under the older clause the mark is as it was
  `K5KeepsAt`, `k5KeepsAt_iff`   THE CLAUSE BY THE MEMBER's PLACE: the numbers x are read off the
                         public input at the place's segment; at the kind's place of group g it is
                         the clause at that group's plan's numbers

Limits. Every lemma has the clause as a premise. Nothing shows here that any step meets it but
`k5KeepsM_of_decide`, whose premise is a yes.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att.P

/-- **WHAT THE KIND's ACCEPTING STEP LEAVES, WITH "NO MARK BEHIND" INSIDE.** x: the planner's
numbers of the segment's own rounds. It is a definition: a premise's form. Nothing is claimed of
it. -/
def K5KeepsM (x : Params.AttentionRounds) (s s' : First.S) : Prop :=
  s'.failed = none ∧ ∃ (a : First.AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
    s.here = .att a ∧ hear x (a.F, rs, 0) = some (hd, G, [], 0) ∧ s' = behind s a hd G

/-- **The kind's own yes gives the clause.** CONDITIONAL: the yes; no mark behind. -/
theorem k5KeepsM_of_decide (p : Par) {s s' : First.S} {rs : List Fmt.RoundView}
    (h : decide seatSO p s rs = .ok s') (hm : s'.failed = none) : K5KeepsM p.own s s' := by
  obtain ⟨a, hd, G, e, hh, e'⟩ := k5_yes_is p h
  exact ⟨hm, a, hd, G, rs, e, hh, e'⟩

section
variable {x : Params.AttentionRounds} {s s' : First.S}

/-- The rest of the state is as it was. CONDITIONAL: the clause. -/
theorem k5KeepsM_rest (K : K5KeepsM x s s') : restO s' = restO s := by
  obtain ⟨-, a, hd, G, rs, e, -, rfl⟩ := K
  unfold restO
  rw [e]
  rfl

/-- No mark in front either: the step leaves the mark as it was. CONDITIONAL: the clause. -/
theorem k5KeepsM_clean (K : K5KeepsM x s s') : s.failed = none :=
  (rest_failed s s' (k5KeepsM_rest K).symm).trans K.1

/-- The statement is as it was. CONDITIONAL: the clause. -/
theorem k5KeepsM_st (K : K5KeepsM x s s') : s'.st = s.st := rest_st s' s (k5KeepsM_rest K)

/-- What was put out is as it was. CONDITIONAL: the clause. -/
theorem k5KeepsM_out (K : K5KeepsM x s s') : s'.out = s.out := rest_out s' s (k5KeepsM_rest K)

/-- The reply is as it was. CONDITIONAL: the clause. -/
theorem k5KeepsM_reply (K : K5KeepsM x s s') : s'.out.reply = s.out.reply := by
  rw [k5KeepsM_out K]

/-- As many rows lie on the pile as did. CONDITIONAL: the clause. -/
theorem k5KeepsM_pile (K : K5KeepsM x s s') : s'.out.pending.length = s.out.pending.length := by
  rw [k5KeepsM_out K]

/-- **Of the open segment's own part: all fields but the ledger and what its own rounds have
heard.** CONDITIONAL: the clause. -/
theorem k5KeepsM_here (K : K5KeepsM x s s') :
    ∃ (a : First.AttOwn) (hd : Heard) (G : Fork),
      s.here = .att a ∧ s'.here = .att { a with F := G, heard5 := some hd } := by
  obtain ⟨-, a, hd, G, rs, e, -, rfl⟩ := K
  exact ⟨a, hd, G, e, rfl⟩

/-- The chain stands in the head's segment neither in front nor behind. CONDITIONAL: the clause. -/
theorem k5KeepsM_not_head (K : K5KeepsM x s s') (o : VerifiableInference.Desc.First.HeadOwn) :
    s.here ≠ .head o ∧ s'.here ≠ .head o := by
  obtain ⟨a, hd, G, e, e'⟩ := k5KeepsM_here K
  rw [e, e']
  exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- **THE OLDER CLAUSE, WHERE THE LEDGER IN FRONT HAS ITS ARRAYS' LENGTHS.** CONDITIONAL: the
clause; hz. -/
theorem k5Keeps_of_M (K : K5KeepsM x s s') (hz : ∀ a, s.here = .att a → Road.Sized a.F) :
    K5Keeps s s' := by
  have hr := k5KeepsM_rest K
  obtain ⟨-, a, hd, G, rs, e, hh, rfl⟩ := K
  obtain ⟨lt, zG⟩ := later_behind hh (hz a e)
  exact ⟨hr, a, _, e, rfl, ⟨lt.next, lt.ns, fun _ => ⟨zG.vp, zG.mf, zG.got⟩, lt.keep⟩,
    (hear_below hh (hz a e)).2⟩

/-- Under the older clause the mark is as it was. CONDITIONAL: `K5Keeps`. -/
theorem k5Keeps_failed (K : K5Keeps s s') : s'.failed = s.failed := rest_failed s' s K.1

end

/-- **THE CLAUSE BY THE MEMBER's PLACE.** X: the public input; p: a place. The attention plan of the
place's segment (number l: group l / 2) hands the numbers. It is a definition: a premise's form.
Where the place names no segment, or the public input has no such plan, it says nothing. -/
def K5KeepsAt (X : Verify.Public) (p : VerifiableInference.Desc.Place) (s s' : First.S) : Prop :=
  ∀ l a, p.link = some l → X.A[l / 2]? = some a → K5KeepsM a.own s s'

/-- At the kind's place of group g it is the clause at that group's plan's numbers. CONDITIONAL: the
public input has the plan a at g. -/
theorem k5KeepsAt_iff {X : Verify.Public} {g : Nat} {a : Attention.Plan} (ha : X.A[g]? = some a)
    (s s' : First.S) :
    K5KeepsAt X ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s' := by
  have e : (2 * g + 1) / 2 = g := by omega
  constructor
  · intro K
    exact K (2 * g + 1) a rfl (by rw [e]; exact ha)
  · intro K l a' hl ha'
    obtain rfl : 2 * g + 1 = l := Option.some.inj hl
    rw [e, ha] at ha'
    obtain rfl := Option.some.inj ha'
    exact K

end H2K5.Honest

#print axioms H2K5.Honest.k5KeepsM_of_decide
#print axioms H2K5.Honest.k5KeepsM_rest
#print axioms H2K5.Honest.k5KeepsM_clean
#print axioms H2K5.Honest.k5KeepsM_st
#print axioms H2K5.Honest.k5KeepsM_out
#print axioms H2K5.Honest.k5KeepsM_reply
#print axioms H2K5.Honest.k5KeepsM_pile
#print axioms H2K5.Honest.k5KeepsM_here
#print axioms H2K5.Honest.k5KeepsM_not_head
#print axioms H2K5.Honest.k5Keeps_of_M
#print axioms H2K5.Honest.k5Keeps_failed
#print axioms H2K5.Honest.k5KeepsAt_iff
