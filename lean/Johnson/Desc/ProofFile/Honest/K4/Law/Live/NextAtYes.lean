-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/NextAtYes.lean: CONDITIONAL.

What is here. BEHIND A YES OF THE BLOCK OF THE LAYERS' OWN ROUNDS (sub-protocol K4; `blockAtS`,
Johnson/Desc/First/K4/AtS.lean): a.F.next ≤ o.wo.sFv AND G.next = o.wo.sFv + 1, so a.F.next ≤
o.wo.sFv < G.next: sFv, the slot of the merge's end value, read off what the hearing returns, lies
at or above the ledger's next free number in front of K4's step, and it is the last number below the
next free number behind the step. One statement, with both clauses at one pair o, G. Its proof: the
yes holds a return of the hearing (`blockAtS_hears`, Johnson/Desc/First/K4/AtSHears.lean); at that
return the merge's window begins at or above the ledger's next free number in front (`hear_wins`,
Johnson/Road/K4/Slots/RunsSpare.lean, the first half of its second pair), the next free number
behind is the window's first number plus 2 lk + 3 (`hear_next`, there; lk: the number of column bits
of the layout in the block's public parameters, `p.P.wsLay.lk`), and sFv is the window's first
number plus 2 lk + 2 (`sFv_at`, Johnson/Road/K4/Total/NotFree.lean); the rest is arithmetic. So in
truth a.F.next + 2 lk + 2 ≤ o.wo.sFv.

  `k4_next_le_of_yes`   **a.F.next ≤ o.wo.sFv and G.next = o.wo.sFv + 1, behind a yes of K4's
      block.**

Kin. AT THE HEARING's RETURN THE LIBRARY HAS BOTH CLAUSES UNDER NAMES, from the ledger's sizes and
the return: `next_le_sFv` (Johnson/Road/K4/Riders/ObjectsAtMeans.lean): F.next ≤ o.wo.sFv;
`merge_last` (Johnson/Road/K4/MergeBelow.lean): o.wo.sFv + 1 = G.next. NEITHER IS CALLED HERE, FOR
THEIR FILES' IMPORTS, which would lie beneath every file that imports this one: by a program's walk
from import to import, over the library as it stood when this file was written, which stops unopened
at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module
whose name begins Cb.Bridge, this file's two imports reach 1,101 modules of the library and none at
which the walk stops; with MergeBelow.lean they would be at least 5,794 (behind a stop nothing is
counted), and nine at which it stops (seven under Johnson/Goal/, two under Johnson/Bridge/); with
ObjectsAtMeans.lean at least 4,757, and one (under Johnson/Goal/). `mergeBelow_kept`
(MergeBelow.lean) has the second clause at two states with an accept of K4's sub-protocol between
them (`KeptAtS`), in the readers `own?` and `fork?`; `at_yes` (ObjectsAtMeans.lean) has the first
among its ends, at a yes of K4's piece under premises of its own; `k4_live_of_yes`
(Law/Live/LiveOfYes.lean) and `k4_live_of_yes_words` (Law/Live/TapeOfWords.lean) end in the second
clause at the block's own yes, with the same state behind, under hypotheses on the draws, the ledger
and the layout and behind a return of `frontForms`; here both clauses stand at that yes under h, ha
and hF alone.

Not shown here. THE THREE HYPOTHESES ARE GIVEN NOWHERE HERE: h (the yes of `blockAtS p`, the block
at the carried state: how a member of a description comes to that yes is the caller's), ha (it names
the segment's data a at which the state in front stands; a yes has such data: `blockAtS_hears`'
first clause), hF (a's ledger has arrays of the right sizes): of the three hF alone asks something
beyond the yes. This file gives no example of them together; its writers know of none that has been
through Lean.

No property is claimed.
-/
import Johnson.Desc.First.K4.AtSHears
import Johnson.Road.K4.Total.NotFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (blockAtS blockAtS_hears)
open OnBytes.Desc.First.K4.Slots (hear_wins hear_next)
open OnBytes.Desc.First.K4.Total (sFv_at)
open VerifiableInference.Desc.First

variable {p : OnBytes.Desc.First.K4.Par} {s s' : S} {rs : List Fmt.RoundView}
  {cols : List (List (Nat × List UInt64))} {a : LayOwn}

/-- CONDITIONAL on all three hypotheses. **BEHIND A YES OF K4's BLOCK: THE LEDGER's NEXT FREE NUMBER
IN FRONT IS AT MOST THE SLOT OF THE MERGE's END VALUE, AND THE ONE BEHIND IS ONE ABOVE IT.** -/
theorem k4_next_le_of_yes (h : (blockAtS p).decide s rs cols = .ok s') (ha : s.here = .lay a)
    (hF : Sized a.F) :
    ∃ (o : Layer.Own) (G : Fork),
      s' = { s with here := .lay { a with F := G, own := some o }, rowsOwed := none } ∧
      a.F.next ≤ o.wo.sFv ∧ G.next = o.wo.sFv + 1 := by
  obtain ⟨a', _, o, G, h1, -, -, -, -, h6, h7⟩ := blockAtS_hears h
  obtain rfl : a = a' := by
    have e := ha.symm.trans h1
    injection e
  have w := (hear_wins hF h6).2.1
  have n := hear_next hF h6
  have e := sFv_at h6
  exact ⟨o, G, h7, by omega, by omega⟩

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.k4_next_le_of_yes
