-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Keeps.lean: CONDITIONAL. One definition of a proposition, and
two statements with their proofs.

What is here. WHAT THE STEP OF K4 LEAVES OF THE VERIFIER's STATE AS IT WAS, AND WHAT IT LAYS ANEW.
K4 is the sub-protocol of the feed-forward layers' own rounds. The definition is meant as K4's
clause of a thread's parameter `keeps` (Honest/Thread/Thr.lean); the theorem says that it holds
wherever the sub-protocol at the first chain's state accepts.

  `K4Keeps s s'`   the clause:
      * every field that `Rest` names (Johnson/Desc/First/K4/ReadsAtS.lean) is as it was, the
        statement and the book of trees among them;
      * a layers' segment is open in front;
      * WHAT TURNS IS NAMED: behind the step the segment holds a ledger G and what K4 has heard, o;
      * G is a later state of the ledger in front (`PscRun.Later`: what lies under a filled slot is
        kept);
      * and, where the ledger in front has its arrays' lengths (`PscRun.Sized`): the arrays that the
        claims read are the ledger's in front; nothing has turned under a slot below the ledger's
        next in front, or from its next behind on (`Fresh`, Johnson/Road/K4/Slots/HearSpares.lean),
        so a slot that was free there is free still; and THE MERGE's END VALUE's SLOT (o.wo.sFv),
        which the table's public test bars a form from naming, is the last that the step takes: it
        is not below the ledger's next in front, and the ledger's next behind is one more.
  `hear_last`   where K4's hearing returns from a ledger with its arrays' lengths, that slot lies
      so.
  `k4_keeps`   **where `(blockAtS p).decide` accepts, `K4Keeps` holds.**

Called, of the library: `kept_atS` (Johnson/Road/K4/KeptAtS.lean) · `hear_trees`
(Johnson/Road/K4/Slots/HearTrees.lean) · `hear_end_first`, `hear_end_later`
(Johnson/Road/K4/HearSlotsEnd.lean).

Kin. BOTH HALVES OF `hear_last` ARE LAWS OF THE LIBRARY TO THE LETTER, each under the same two
hypotheses: the first is `next_le_sFv` (Johnson/Road/K4/Riders/ObjectsAtMeans.lean), the second
`merge_last` (Johnson/Road/K4/MergeBelow.lean), which goes by the same steps as the proof here; the
last clause of `k4_keeps` is near the second file's `mergeBelow_kept`. Neither file is imported
here: by a walk of import lines the imports of each are more than four times this file's.
`K4Keeps`'s clauses on the open segment, on the ledger and what is heard behind, `Later`, `Rest`
and `Fresh` are clauses of the library's `KeptAtS p s s'` (Johnson/Road/K4/KeptAtS.lean), which
takes the parameters p and holds more; the clause on the arrays and the one on the last slot are
not among that definition's. Other kinds' clauses of `keeps`: `K7Keeps` (Honest/K7/Keeps.lean),
`K13Keeps` (Johnson/Desc/K13/Honest/KeepsM3.lean). The short names `hear_last` and `k4_keeps` stand
for other statements in other namespaces (Johnson/Desc/Kinds/Law/KeepsHear.lean;
Johnson/Road/K4/RoomKeepK4.lean, Honest/K10/Wipe/KeepK4.lean).

Not shown here. ONE WAY, FROM AN ACCEPTING DECISION. Nothing on the member as a chain seats it
(guarded, retyped). Whether the clause is strong enough for an item that reads the state is for
whoever proves that item to say. Following import lines, and stopping unopened at every module
under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name
begins Cb.Bridge, its imports reach none of these. Nothing on soundness, on completeness or on any
other property.

No property is claimed.
-/
import Johnson.Road.K4.KeptAtS
import Johnson.Road.K4.Slots.HearTrees
import Johnson.Road.K4.HearSlotsEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Later Sized)
open OnBytes.Desc.First.K4.Slots (Fresh hear_trees)
open OnBytes.Desc.First.K4 (Par blockAtS Rest hear engFl hear_end_first hear_end_later k4Slots hPAt
  kPAt tClAt sClAt sPvAt)
open VerifiableInference.Desc.First (S)

/-- **What K4's step leaves of the state as it was, and what it lays anew.** Meant as a clause of a
thread's parameter `keeps`. Nothing is claimed by the definition. -/
def K4Keeps (s s' : S) : Prop :=
  Rest s s' ∧ ∃ a G o, s.here = .lay a ∧ s'.fork? = some G ∧ s'.own? = some o ∧ Later a.F G ∧
    (Sized a.F → G.trees = a.F.trees ∧ Fresh a.F G ∧ a.F.next ≤ o.wo.sFv ∧ o.wo.sFv + 1 = G.next)

/-- The merge's end value's slot is the last that the hearing takes, and none of those in front. -/
theorem hear_last {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    F.next ≤ o.wo.sFv ∧ o.wo.sFv + 1 = G.next := by
  have hn : F.next ≤ (k4Slots P hp g F.next).nx := by
    simp only [k4Slots, hPAt, kPAt, tClAt, sClAt, sPvAt]
    omega
  cases hg : (g == 0) with
  | true =>
    obtain ⟨_, _, e1, _, e2⟩ := hear_end_first Reading.gl hF h hg
    omega
  | false =>
    obtain ⟨_, _, e1, _, e2⟩ := hear_end_later Reading.gl hF h hg
    omega

/-- **Where the kind's sub-protocol accepts, that holds.** -/
theorem k4_keeps {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s') :
    K4Keeps s s' := by
  obtain ⟨a, _, o, G, ha, _, hG, hL, ho, _, _, _, hR, _, hS, _, _, hh⟩ := OnBytes.Road.K4.kept_atS h
  exact ⟨hR, a, G, o, ha, hG, ho, hL, fun hz =>
    ⟨hear_trees hz hh, (hS hz).2, (hear_last hz hh).1, (hear_last hz hh).2⟩⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4Keeps
#print axioms ProofFile.Honest.K4.hear_last
#print axioms ProofFile.Honest.K4.k4_keeps
