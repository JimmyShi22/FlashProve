-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/AtSeat.lean: FROM A RETURN OF THE PLAIN LISTING TO A RETURN OF K4's RUN AT THE
FIRST CHAIN's CARRIED RECORD. A tool for the law "behind K4's hearing its two runs of claims return"
at the block that rides (blockAtS, Johnson/Desc/First/K4/AtS.lean). Statements and proofs.

Johnson/Desc/First/K4/RunsAtS.lean's frontAtS and backAtS go FROM a return of the run at the carried
record to a return of the plain listing. Here the converses.

  `runOfAtS_returns`: a lifted run of claims of K4's returns where the chain stands in a layers'
    link, what was heard lies in it, and the plain listing returns at the link's ledger.
  `frontAtS_returns`, `backAtS_returns`: so for the two runs of blockAtS p, found under their
    names; the claims are the listing's forms as a list, and what is written is Wrote
    (RunsAtS.lean).
No new argument: liftPart_run, block_front, block_back, runOf_ok, walked forward.
**Limits.** Three premises in each: ha (the chain stands in a layers' link a), ho
(what was heard lies in a), hf (the plain listing returns at a's ledger). Their payers are not here:
ha and ho are what is kept behind a yes of the block; hf is the end of the law RunsReturn, which
stands under the premise "member". Nothing on what a form is worth, nothing on soundness. The law of
K4's kind on its claims is NOT proved by this. Met through Lean at no member; by a run at one honest
proof of each of two sizes both runs of claims return at all 2 and 12 layers' places: that run is
the member of the law that these serve.


-/
import Johnson.Desc.First.K4.RunsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Own)
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.First (S LayOwn)

/-! ## To a return at the carried record -/

/-- A lifted run of claims of K4's returns. -/
theorem runOfAtS_returns {name : String} {f : Own → Fork → Option (Array Aff × Fork)} {s : S}
    {a : LayOwn} {o : Own} {fs : Array Aff} {G : Fork} (ha : s.here = .lay a)
    (ho : a.own = some o) (hf : f o a.F = some (fs, G)) :
    ∃ s', ((named "the part is not there" (part? s)).bind fun q =>
      (runOf seatOwn name f q).map fun y => (y.1, setPart s y.2)) = .ok (fs.toList, s') ∧
      Wrote s a G s' := by
  have hq : part? s = some (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) := by
    simp only [part?, ha]
  have hd : runOf seatOwn name f (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) =
      .ok (fs.toList,
        seatOwn.setFork (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) G) :=
    (runOf_ok seatOwn name f _ _ _).mpr ⟨o, fs, G, ho, hf, rfl, rfl⟩
  refine ⟨{ s with here := .lay { a with F := G },
                   rowsOwed := if s.noneWaits then none else s.rowsOwed }, ?_, ha, rfl⟩
  rw [hq]
  show ((runOf seatOwn name f (a, (if s.noneWaits then none else s.rowsOwed), s.tokv)).map
    fun y => (y.1, setPart s y.2)) = _
  rw [hd]
  rfl

/-- **The run "front" returns at the carried record.** -/
theorem frontAtS_returns {p : Par} {s : S} {a : LayOwn} {o : Own} {fs : Array Aff} {G : Fork}
    (ha : s.here = .lay a) (ho : a.own = some o) (hf : frontOf p o a.F = some (fs, G)) :
    ∃ run s', (blockAtS p).claims.lookup "front" = some run ∧
      (∀ n, run n s = .ok (fs.toList, s')) ∧ Wrote s a G s' := by
  have e := liftPart_run part? setPart (block seatOwn p) "front"
  rw [block_front] at e
  obtain ⟨s', h1, h2⟩ := runOfAtS_returns (name := "K4.claims-front") ha ho hf
  exact ⟨_, s', e, fun _ => h1, h2⟩

/-- **The run "back" returns at the carried record.** -/
theorem backAtS_returns {p : Par} {s : S} {a : LayOwn} {o : Own} {fs : Array Aff} {G : Fork}
    (ha : s.here = .lay a) (ho : a.own = some o) (hf : formsBack o a.F = some (fs, G)) :
    ∃ run s', (blockAtS p).claims.lookup "back" = some run ∧
      (∀ n, run n s = .ok (fs.toList, s')) ∧ Wrote s a G s' := by
  have e := liftPart_run part? setPart (block seatOwn p) "back"
  rw [block_back] at e
  obtain ⟨s', h1, h2⟩ := runOfAtS_returns (name := "K4.claims-back") ha ho hf
  exact ⟨_, s', e, fun _ => h1, h2⟩

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.runOfAtS_returns
#print axioms OnBytes.Desc.First.K4.Total.frontAtS_returns
#print axioms OnBytes.Desc.First.K4.Total.backAtS_returns
