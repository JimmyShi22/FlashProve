-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/ReadsAtS.lean: WHAT THE CARRIED RECORD's OWN READERS FIND BEHIND K4: behind a
yes of K4's block at the carried record (`blockAtS p`), and behind each of its runs. A definition,
statements and proofs: each is read off an equation that is proved elsewhere (`blockAtS_hears`,
Johnson/Desc/First/K4/AtSHears.lean; `Wrote`, Johnson/Desc/First/K4/RunsAtS.lean).

  `Rest s s'`: seven of the record's nine fields are the same (st, book, roots, failed, check, out,
    req: all but `here` and `rowsOwed`), and of the readers of a link: `link?`, `tl?`, `look?`,
    `lookHeard?` find the same; and where s stands in a layers' link, s' stands in a layers' link
    with the same L, fo, tl and lookHeard (four of that link's six fields: all but F, own).
  `heard_reads`: BEHIND A YES OF THE BLOCK, with (o, G) what K4's plain hearing returned: `own?`
    finds o; `funs?`, THE TABLES WITH THEIR WEIGHTS AS THE SMALLNESS TEST's CLAIMS TAKE THEM, finds
    o.funs; `fork?` finds G; nothing is owed; `Rest`.
  `wrote_reads`: BEHIND A RUN (`Wrote s a G s'`): `own?` and `funs?` find what they found; `fork?`
    found the link's ledger and finds G; `Rest`. Of the debt of rows behind a run nothing is said
    here: `Wrote` has it (at "some 0" the run lays none).
  `front_funs`, `back_funs`, `freeSlot_funs`: so none of K4's three runs turns what `funs?` finds.

Limits. NOTHING HERE SHOWS THAT THE BLOCK OR A RUN RETURNS ANYWHERE. What o.funs is (which tables,
which weights) is the hearing's own law's matter, not this file's. One direction, from a return.
Nothing on soundness.
-/
import Johnson.Desc.First.K4.RunsAtS
import Johnson.Desc.First.K4.AtSHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer OnBytes.K.Kc
open VerifiableInference.Desc.First (S LayOwn)

/-- Seven of the record's nine fields are the same; four readers of a link find the same; a layers'
link stays a layers' link, with four of its six fields. -/
structure Rest (s s' : S) : Prop where
  st : s'.st = s.st
  book : s'.book = s.book
  roots : s'.roots = s.roots
  failed : s'.failed = s.failed
  check : s'.check = s.check
  out : s'.out = s.out
  req : s'.req = s.req
  link : s'.link? = s.link?
  tl : s'.tl? = s.tl?
  look : s'.look? = s.look?
  lookHeard : s'.lookHeard? = s.lookHeard?
  here : ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.L = a.L ∧ a'.fo = a.fo ∧
    a'.tl = a.tl ∧ a'.lookHeard = a.lookHeard

/-- The one step: in a layers' link a ledger, a «heard by K4» and a debt of rows are laid. -/
theorem rest_of_laid {s : S} {a : LayOwn} (G : Fork) (w : Option Own) (d : Option Nat)
    (ha : s.here = .lay a) :
    Rest s { s with here := .lay { a with F := G, own := w }, rowsOwed := d } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [S.link?, ha], by simp [S.tl?, ha],
    by simp [S.look?, ha], by simp [S.lookHeard?, ha], fun b hb => by
      cases ha.symm.trans hb
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **Behind a yes of K4's block at the carried record.** -/
theorem heard_reads {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p).decide s rs cols = .ok s') :
    ∃ (a : LayOwn) (fo : Forest.Heard) (o : Own) (G : Fork), s.here = .lay a ∧ a.fo = some fo ∧
      hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F (paired rs (entries p.P p.hp p.g)) =
        some (o, G, []) ∧
      s'.own? = some o ∧ s'.funs? = some o.funs ∧ s'.fork? = some G ∧ s'.rowsOwed = none ∧
      Rest s s' := by
  obtain ⟨a, fo, o, G, ha, _, hfo, _, _, hh, rfl⟩ := blockAtS_hears h
  exact ⟨a, fo, o, G, ha, hfo, hh, rfl, rfl, rfl, rfl, rest_of_laid G (some o) none ha⟩

/-- **Behind a run of K4's.** -/
theorem wrote_reads {s s' : S} {a : LayOwn} {G : Fork} (h : Wrote s a G s') :
    s'.own? = s.own? ∧ s'.funs? = s.funs? ∧ s.fork? = some a.F ∧ s'.fork? = some G ∧ Rest s s' := by
  obtain ⟨ha, rfl⟩ := h
  exact ⟨by simp [S.own?, ha], by simp [S.funs?, ha], by simp [S.fork?, ha], rfl,
    rest_of_laid G a.own _ ha⟩

/-- The run "front" leaves what `funs?` finds. -/
theorem front_funs {p : Par} {run : Nat → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "front" = some run) {n : Nat} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) : s'.funs? = s.funs? := by
  obtain ⟨_, _, _, _, _, _, _, hw⟩ := frontAtS hr h
  exact (wrote_reads hw).2.1

/-- The run "back" leaves what `funs?` finds. -/
theorem back_funs {p : Par} {run : Nat → S → Except String (List Aff × S)}
    (hr : (blockAtS p).claims.lookup "back" = some run) {n : Nat} {s s' : S} {cl : List Aff}
    (h : run n s = .ok (cl, s')) : s'.funs? = s.funs? := by
  obtain ⟨_, _, _, _, _, _, _, hw⟩ := backAtS hr h
  exact (wrote_reads hw).2.1

/-- The run "free-slot" leaves what `funs?` finds. -/
theorem freeSlot_funs {p : Par} {run : S → Except String S}
    (hr : (blockAtS p).after.lookup "free-slot" = some run) {s s' : S} (h : run s = .ok s') :
    s'.funs? = s.funs? := by
  obtain ⟨_, hw⟩ := freeSlotAtS hr h
  exact (wrote_reads hw).2.1

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.heard_reads
#print axioms OnBytes.Desc.First.K4.wrote_reads
#print axioms OnBytes.Desc.First.K4.front_funs
#print axioms OnBytes.Desc.First.K4.back_funs
#print axioms OnBytes.Desc.First.K4.freeSlot_funs
