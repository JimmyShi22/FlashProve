-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/FreeSlotChain.lean: the layers' own run behind the batching,
"free-slot" (OnBytes.Desc.First.K4.blockAtS, its list "after"), against the shape of the first
chain's state (chainSh, Johnson/Desc/First/Shape/Chain.lean): one step on the shape, one test on
values, and the two laws; then the same for the run as it stands seated in the proof file's chain.
General laws; nothing is evaluated.

  `freeG`: the step: the chain stands in a layers' link and what the layers' own rounds returned is
    there (the list of tables is laid): THE COUNT OF ROWS OWED IS READ ONCE THROUGH THE LENS:
    "some 0" comes back as "none"; all else stays.
  `freeV p`: THE TEST ON VALUES: the layers' test on the free slot (freeSlotOk): of the slots below
    the plan's number p.hp.used the merge's has coefficient 0 AND EVERY OTHER HAS NOT; a slot beyond
    the array counts as 0. These coefficients hang on the verifier's challenges:
    that an honest prover's run meets the test is not shown here.
  **`free_carries`**, **`free_returns`**: for the run that blockAtS p states under "free-slot".
  `free_seated`: what the term "the proof file's layers' sub-protocol as it stands in the first
    chain, alone" (IM.seatedAs same (ProofFile.k4Block x) name a) states under "free-slot": that run,
    followed by the wrapper's comparison.
  **`freeS_carries`**, **`freeS_returns`**: the two laws for the seated run, at the proof file's own
    comparison (the two states hold the same heard reply).

By the library's freeSlotAtS (Johnson/Desc/First/K4/RunsAtS.lean) and by freeSlotAtS_returns
(Johnson/Desc/First/K4/FreeSlotReturns.lean).

Limits. That freeV accepts anywhere is not shown. noneWaitsSh stands a second time, to the letter,
in Johnson/AtFull/Shape/K4Fit.lean; no law ties the two. freeG asks that the tables are laid where
"own is there" is meant: at a state's shape the two agree in a layers' link; at a shape that is made
by steps they agree only if every step keeps both. free_seated hands out the run at { x.2 with
k3Runs := true }, though freeRun and freeV read p.hp alone; x.1 is idle in it. That the step returns
at a shape that the chain reaches is not shown. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.BehindSeat
import Johnson.Desc.First.K4.FreeSlotReturns
import Johnson.Desc.First.K4.RunsAtS
import Johnson.Desc.ProofFile.Lot.K4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open OnBytes.Desc.First.K4 (blockAtS blockAtS_after freeSlotOk Wrote freeSlotAtS
  freeSlotAtS_returns)

/-- The layers' own numbers at a place. -/
abbrev Par4 : Type := OnBytes.Desc.First.K4.Par

/-! ## 1 The bare run -/

/-- "No count waits", on the shape. -/
def noneWaitsSh (a : ChainSh) : Bool :=
  match a.rowsOwed with
  | none => true
  | some r => r == 0

/-- **The step on the shape.** -/
def freeG (a : ChainSh) : Except String ChainSh :=
  if a.here == 1 && a.funs then
    .ok (a.setRowsOwed (if noneWaitsSh a then none else a.rowsOwed))
  else .error "free-slot: the shape"

/-- **The test on values.** -/
def freeV (p : Par4) (s : S) : Bool :=
  match s.here with
  | .lay a => (a.own.map fun o => freeSlotOk p.hp.used o.wo.sFv a.F).getD false
  | _ => false

theorem wrote_sh {s s' : S} {a : LayOwn} (h : Wrote s a a.F s') :
    chainSh s' =
      (chainSh s).setRowsOwed (if noneWaitsSh (chainSh s) then none else (chainSh s).rowsOwed) := by
  obtain ⟨hs, rfl⟩ := h
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .lay a := hs
  rfl

theorem free_carries {p : Par4} {run : S → Except String S}
    (hr : (blockAtS p).after.lookup "free-slot" = some run) (s s' : S) (t : ChainSh)
    (h : run s = .ok s') (hg : freeG (chainSh s) = .ok t) : t = chainSh s' := by
  obtain ⟨a, hw⟩ := freeSlotAtS hr h
  unfold freeG at hg
  split at hg
  · rw [wrote_sh hw]
    exact (Except.ok.inj hg).symm
  · exact nomatch hg

theorem free_returns {p : Par4} {run : S → Except String S}
    (hr : (blockAtS p).after.lookup "free-slot" = some run) (s : S) (hv : freeV p s = true) :
    ∃ s', run s = .ok s' := by
  unfold freeV at hv
  cases hs : s.here with
  | lay a =>
    rw [hs] at hv
    cases ho : a.own with
    | none => simp [ho] at hv
    | some o =>
      have hb : freeSlotOk p.hp.used o.wo.sFv a.F = true := by simpa [ho] using hv
      obtain ⟨s', h, -⟩ := freeSlotAtS_returns hr hs ho hb
      exact ⟨s', h⟩
  | between => rw [hs] at hv; exact nomatch hv
  | att a => rw [hs] at hv; exact nomatch hv
  | head a => rw [hs] at hv; exact nomatch hv
  | fin a => rw [hs] at hv; exact nomatch hv
  | mem a => rw [hs] at hv; exact nomatch hv

/-! ## 2 The seated run -/

/-- The run that blockAtS p states. -/
def freeRun (p : Par4) : S → Except String S := fun t =>
  (named "the part is not there" (OnBytes.Desc.First.K4.part? t)).bind fun q =>
    (OnBytes.Desc.First.K4.freeSlot OnBytes.Desc.First.K4.seatOwn p.hp q).map
      (OnBytes.Desc.First.K4.setPart t)

theorem freeRun_look (p : Par4) : (blockAtS p).after.lookup "free-slot" = some (freeRun p) := by
  rw [blockAtS_after]
  simp only [List.lookup, beq_self_eq_true]
  rfl

theorem free_seated {bs : List (Block S Claim)} {i : Nat} {x : Bool × Par4} {same : S → S → Bool}
    {name : String} {a : Place} (h : bs[i]? = some (IM.seatedAs same (ProofFile.k4Block x) name a)) :
    ((bs[i]?).bind fun b => b.after.lookup "free-slot") =
      some fun t => (freeRun { x.2 with k3Runs := true } t).bind (seatSame same t) := by
  have ea : (IM.seatedAs same (ProofFile.k4Block x) name a).after =
      [("free-slot", fun t => (freeRun { x.2 with k3Runs := true } t).bind (seatSame same t))] :=
    rfl
  rw [h]
  show (IM.seatedAs same (ProofFile.k4Block x) name a).after.lookup "free-slot" = _
  rw [ea]
  simp [List.lookup]

theorem sameReply_wrote {s s' : S} {a : LayOwn} (h : Wrote s a a.F s') :
    ProofFile.sameReply s s' = true := by
  obtain ⟨-, rfl⟩ := h
  unfold ProofFile.sameReply
  exact beq_self_eq_true _

theorem freeS_carries (p : Par4) (s s' : S) (t : ChainSh)
    (h : (freeRun p s).bind (seatSame ProofFile.sameReply s) = .ok s')
    (hg : freeG (chainSh s) = .ok t) : t = chainSh s' :=
  free_carries (freeRun_look p) s s' t ((bind_seatSame_iff _ _ s s').1 h).1 hg

theorem freeS_returns (p : Par4) (s : S) (hv : freeV p s = true) :
    ∃ s', (freeRun p s).bind (seatSame ProofFile.sameReply s) = .ok s' := by
  obtain ⟨s', h⟩ := free_returns (freeRun_look p) s hv
  obtain ⟨a, hw⟩ := freeSlotAtS (freeRun_look p) h
  exact ⟨s', (bind_seatSame_iff _ _ s s').2 ⟨h, sameReply_wrote hw⟩⟩

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.free_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.free_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.free_seated
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.freeS_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.freeS_returns
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Par4
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.noneWaitsSh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.freeG
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.freeV
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.wrote_sh
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.freeRun
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.freeRun_look
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.sameReply_wrote
