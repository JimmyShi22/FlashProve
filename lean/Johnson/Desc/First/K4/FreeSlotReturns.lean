-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/FreeSlotReturns.lean: CONDITIONAL: WHERE THE RUN "free-slot", WHICH THE
LAYERS' OWN ROUNDS (K4) STATE BEHIND THE BATCHING, RETURNS. The converses of laws of
Johnson/Desc/First/K4/RunsAtC.lean, which go from a return; and the tie of K4's test to the
batching's own test on the free slot. Statements and proofs.

Not shown here. THAT THE TEST HOLDS ANYWHERE is a premise, on sampled values: an honest run can miss
it. That a chain asks K4's test and the batching's at one number, one ledger and one slot. Nothing
on a run under a guard (`Block.guarded`, Johnson/Desc/SeatGuard.lean): it returns only where the
guard's comparison accepts too. Nothing on `blockAtC p`: its runs behind the batching are those of
`blockAtS p` (`atClaims_same`, RunsAtC.lean). Nothing on the claims' values. Nothing on soundness,
on completeness or on any other property.

A seat (`Seat T`) says where in a state of type T lie the ledger and what K4 has heard (`Own`).
  `freeSlot_returns`: at a seat: where what K4 has heard is there and the test holds (`freeSlotOk`),
    the run returns, and hands the state on as it is. `freeSlot_iff`: both ways.
  `freeSlot_body_returns`, `freeSlotAtS_returns`: `freeSlot_returns` at the first chain's carried
    state, one way: of the run's body; of the run that the name "free-slot" finds in `blockAtS p`.
    THERE THE STATE DOES NOT COME BACK AS IT WAS: the count of rows owed is read through `part?`, so
    "some 0" comes back as none. All else stays (`Wrote`, Johnson/Desc/First/K4/RunsAtS.lean).
  `freeSlotOk_iff`: K4's test on the slots below n, with the merge's slot sFv, is true just where
    the batching's own test (`K9.freeSlot`, Johnson/Desc/First/Batch/Sums.lean) accepts at the same
    number, the same ledger and the merge's slot `some sFv`.

-/
import Johnson.Desc.First.K4.RunsAtC
import Johnson.Desc.First.Batch.Law.SumsMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Model.Layer
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.First (S LayOwn)

/-- At a seat: where what K4 has heard is there and the test holds, the run behind the batching
returns, and hands the state on as it is. -/
theorem freeSlot_returns {T : Type} (L : Seat T) {hp : HPlan2} {s : T} {o : Own}
    (ho : L.own s = some o) (hb : freeSlotOk hp.used o.wo.sFv (L.fork s) = true) :
    freeSlot L hp s = .ok s := by
  unfold freeSlot
  simp [ho, named, test, VerifiableInference.Desc.need, hb, bind, Except.bind, pure, Except.pure]

/-- **What a return of the run behind the batching is**, at a seat. -/
theorem freeSlot_iff {T : Type} (L : Seat T) {hp : HPlan2} {s s' : T} :
    freeSlot L hp s = .ok s' ↔
      ∃ o, L.own s = some o ∧ freeSlotOk hp.used o.wo.sFv (L.fork s) = true ∧ s' = s :=
  ⟨freeSlot_ok L, fun ⟨_, ho, hb, e⟩ => by
    subst e
    exact freeSlot_returns L ho hb⟩

/-- The run's body at the carried state returns where the chain stands in a layers' link, what K4
has heard is there and the test holds. What comes back is `Wrote`'s state, not the state as it was:
the count of rows owed has been read through `part?`. One way. -/
theorem freeSlot_body_returns {p : Par} {s : S} {a : LayOwn} {o : Own} (hs : s.here = .lay a)
    (ho : a.own = some o) (hb : freeSlotOk p.hp.used o.wo.sFv a.F = true) :
    ∃ s', ((named "the part is not there" (part? s)).bind fun q =>
      (freeSlot seatOwn p.hp q).map (setPart s)) = .ok s' ∧ Wrote s a a.F s' := by
  have hq : part? s = some (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) := by
    simp [part?, hs]
  have hd : freeSlot seatOwn p.hp (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) =
      .ok (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) :=
    freeSlot_returns seatOwn (o := o) ho hb
  refine ⟨setPart s (a, (if s.noneWaits then none else s.rowsOwed), s.tokv), ?_, hs, rfl⟩
  simp [hq, named, Except.bind, hd, Except.map]

/-- **The run "free-slot" returns, at the carried state**, where the chain stands in a layers' link,
what K4 has heard is there and the test holds. What comes back is `Wrote`'s state, not the state as
it was. One way. -/
theorem freeSlotAtS_returns {p : Par} {run : S → Except String S}
    (hr : (blockAtS p).after.lookup "free-slot" = some run) {s : S} {a : LayOwn} {o : Own}
    (hs : s.here = .lay a) (ho : a.own = some o)
    (hb : freeSlotOk p.hp.used o.wo.sFv a.F = true) : ∃ s', run s = .ok s' ∧ Wrote s a a.F s' := by
  have e : (blockAtS p).after.lookup "free-slot" = some fun t =>
      (named "the part is not there" (part? t)).bind fun q =>
        (freeSlot seatOwn p.hp q).map (setPart t) := by
    rw [blockAtS_after]
    simp
  obtain rfl := Option.some.inj (e.symm.trans hr)
  exact freeSlot_body_returns hs ho hb

/-- **K4's test is the batching's own**, at the same number of slots, the same ledger and the
merge's slot. -/
theorem freeSlotOk_iff (n sFv : Nat) (F : Fork) :
    freeSlotOk n sFv F = true ↔ VerifiableInference.Desc.K9.freeSlot n (some sFv) F = .ok () := by
  rw [VerifiableInference.Desc.K9L.freeSlot_iff]
  unfold freeSlotOk
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    have h1 := h j (List.mem_range.2 hj)
    rw [beq_iff_eq] at h1
    rw [h1, beq_iff_eq]
    exact ⟨fun e => congrArg some e.symm, fun e => (Option.some.inj e).symm⟩
  · intro h j hj
    have h1 := h j (List.mem_range.1 hj)
    rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq]
    exact h1.trans ⟨fun e => (Option.some.inj e).symm, fun e => congrArg some e.symm⟩

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.freeSlot_returns
#print axioms OnBytes.Desc.First.K4.freeSlot_iff
#print axioms OnBytes.Desc.First.K4.freeSlot_body_returns
#print axioms OnBytes.Desc.First.K4.freeSlotAtS_returns
#print axioms OnBytes.Desc.First.K4.freeSlotOk_iff
