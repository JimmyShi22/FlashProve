-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/KeptAtS.lean: TWELVE THINGS THAT CAN BE HAD OF THE RECORD BEHIND A YES OF K4's BLOCK
AT THE CARRIED RECORD, LAID TOGETHER IN ONE STATEMENT, THE HEARING's OWN EQUATION AMONG THEM: for
whoever fills the promise behind K4's place. One definition and one statement with its proof: laws
that are proved elsewhere, called: `blockAtS_hears`
(Johnson/Desc/First/K4/AtSHears.lean), `heard_reads` (ReadsAtS.lean), `hearFl_later`
(OnBytes/Desc/First/K4/HearGrows.lean), `own_fo`, `hear_fills`
(Johnson/Road/K4/Slots/HearFills.lean), `hear_fresh` (Slots/HearSpares.lean).

  `KeptAtS p s s'`: there are the layers' link's record a in front, the lookup's record fo in it,
    what was heard o and the ledger G with:
    in front: s.here = .lay a, a.fo = some fo;
    the ledger: s'.fork? = some G; G is later than a.F (`PscRun.Later`: next does not fall, the
      number of slots stays, what is filled stays filled with what lies under it; if a.F's arrays
      have their sizes, so have G's);
    what K4 lays: s'.own? = some o, s'.funs? = some o.funs, s'.rowsOwed = none, and what the link
      has left for its pending row is o.wo (`leftLay`, Johnson/Desc/First/Walk/Frame.lean);
    what stays: `Rest s s'`: seven of the record's nine fields, four readers of the link, and five
      of the link's own fields;
    the lookup's record inside o is fo;
    if a.F has arrays of the right sizes: a list of slots that are filled in G (`Fills7`); and
      NOTHING HAS TURNED UNDER A SLOT BELOW a.F.next OR FROM G.next ON (`Fresh a.F G`): free or
      filled alike, the same shown value, the same factor;
    THE HEARING's OWN EQUATION: there are tapes t, u with `hearFl` at p's parameters (the tokens the
      record's), fo, a.F and t returning (o, G, u): so that whatever is proved of a return of the
      hearing (`wo_sizes`, `hear_wins`, `hear_next`, `hear_count`) can be drawn from
      here.
  **`kept_atS`**: a yes of `(blockAtS p).decide` gives it.

Limits. ONE DIRECTION, FROM A YES. NOTHING ON THE NEXT FREE SLOT's NUMBER. That the pending row's
function returns on o.wo is not said. Nothing on the runs. Nothing on soundness.
-/
import Johnson.Desc.First.K4.ReadsAtS
import Johnson.Desc.First.Walk.Frame
import Johnson.Road.K4.Slots.HearSpares

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par blockAtS blockAtS_hears heard_reads hearFl hearFl_later Rest)
open OnBytes.Desc.First.K4.Slots (Fills7 hear_fills own_fo Fresh hear_fresh)
open VerifiableInference.Desc.First (S LayOwn)
open Johnson.Desc.First.Walk (leftLay)

/-- What can be had of the record behind a yes of K4's block. -/
def KeptAtS (p : Par) (s s' : S) : Prop :=
  ∃ (a : LayOwn) (fo : Forest.Heard) (o : Own) (G : Fork),
    s.here = .lay a ∧ a.fo = some fo ∧ s'.fork? = some G ∧ Later a.F G ∧
      s'.own? = some o ∧ s'.funs? = some o.funs ∧ s'.rowsOwed = none ∧ leftLay s' = some o.wo ∧
      Rest s s' ∧ o.H.fo = fo ∧
      (PscRun.Sized a.F → Fills7 { p.P with tokv := s.tokv } p.hp p.g o G ∧ Fresh a.F G) ∧
      ∃ t u, hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F t = some (o, G, u)

/-- **A yes of K4's block at the carried record gives it.** -/
theorem kept_atS {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s') :
    KeptAtS p s s' := by
  obtain ⟨a, fo, o, G, ha, hfo, hh, h1, h2, h3, h4, hR⟩ := heard_reads h
  obtain ⟨a', _, o', G', ha', _, _, _, _, _, e⟩ := blockAtS_hears h
  have hl : leftLay s' = some o.wo := by
    have e1 : s'.own? = some o' := by
      rw [e]
      rfl
    obtain rfl : o' = o := Option.some.inj (e1.symm.trans h1)
    rw [e]
    rfl
  exact ⟨a, fo, o, G, ha, hfo, h3, hearFl_later hh, h1, h2, h4, hl, hR, own_fo hh,
    fun hS => ⟨hear_fills hS hh, hear_fresh hS hh⟩, _, _, hh⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.kept_atS
