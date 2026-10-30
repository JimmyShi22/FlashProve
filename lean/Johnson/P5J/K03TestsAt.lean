-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03TestsAt.lean: SIX NAMED TESTS OF THE LOOKUPS' CONDITION AT THE CLOSED CONSTANT THAT ARE THEOREMS UNDER THE HEAD, OVER THE PROOF FILE's ENTRY TESTS (typed over the list of thirteen rows; it stands over the list of fourteen rows, too). So that the counts' lists of tests shrink.
EACH IS A CALL OR TWO OF ANOTHER FILE's THEOREM; nothing new is argued here:
  k03_fence_at: fenceFit (At.N Zp cF) linksFull (flatPlacesOf linksFull true) = true: AtMg.fence (Johnson/P5T/FenceAtMg.lean), in the spelling in which the lookups' lemmas ask it.
  k03_digRow_at · k03_readsRow_at · k03_headRow_at: K3Asks.digRow | readsRow (At.X Zp) (K3Asks.sentOf Zp) = true · K3Asks.headRow (At.X Zp) = true: three rows of the entry tests, which the head's field laid.asks holds: LPFD.asks_rest (Johnson/Desc/Laid/ProofAsksLaw2.lean).
  k03_pads_at: OffPad.planK6AtZ Zp = true ∧ OffPad.padsAtZ Zp = true: tests_of_pin (Johnson/Desc/Kinds/Law/HeadCutsOfPin.lean) at the pin, which follows from the row madeRow (AtMg.pins; PlanWritten.pinnedAt_of_row).
  k03_offC_at: h.offC = true, at OnBytes.secondHashFunction: offC_head (Johnson/Top/H0/K2Ties/OffHead.lean) at the same pin.
WHAT THIS IS WORTH: the tests have not become true of themselves: they have MOVED INTO THE HEAD: the head's field laid.asks says that every row of the entry tests accepts (Johnson/Desc/Laid/ProofAsks.lean), and these six are rows of it or follow from two of them (madeRow · cutRow) in scope. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/).

Limits. Over the entry tests' lists of thirteen and of fourteen rows (it compiles over no shorter one). Nothing on soundness by itself.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.FenceAtMg
import Johnson.Desc.Laid.ProofAsksLaw2
import Johnson.Desc.Kinds.Law.HeadCutsOfPin
import Johnson.Top.H0.K2Ties.OffHead
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ OffPad.planK6AtZ)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The fence, in the lookups' spelling.** -/
theorem k03_fence_at (h : AtMg o Z D r Zp Np cF) :
    Desc.First.fenceFit (At.N Zp cF) linksFull (Desc.First.flatPlacesOf linksFull true) = true := h.fence

/-- **The digits' row.** -/
theorem k03_digRow_at (h : AtMg o Z D r Zp Np cF) :
    Desc.K3Asks.digRow (At.X Zp) (Desc.K3Asks.sentOf Zp) = true :=
  (LPFD.asks_rest h.laid.asks h.laid.pub).1

/-- **The row on attention's callers' reading.** -/
theorem k03_readsRow_at (h : AtMg o Z D r Zp Np cF) :
    Desc.K3Asks.readsRow (At.X Zp) (Desc.K3Asks.sentOf Zp) = true :=
  (LPFD.asks_rest h.laid.asks h.laid.pub).2.1

/-- **The output head's row.** -/
theorem k03_headRow_at (h : AtMg o Z D r Zp Np cF) : Desc.K3Asks.headRow (At.X Zp) = true :=
  (LPFD.asks_rest h.laid.asks h.laid.pub).2.2

/-- **The output head's two cheap public tests.** -/
theorem k03_pads_at (h : AtMg o Z D r Zp Np cF) :
    OffPad.planK6AtZ Zp = true ∧ OffPad.padsAtZ Zp = true :=
  Desc.Kinds.Head.Law.tests_of_pin h
    (PlanWritten.pinnedAt_of_row (by rw [h.pins.1, Bool.or_true]))

/-- **No sampled place falls on a pad.** -/
theorem k03_offC_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : h.offC = true :=
  Desc.First.K2Ties.offC_head h (PlanWritten.pinnedAt_of_row (by rw [h.pins.1, Bool.or_true]))

end P5J

#print axioms P5J.k03_fence_at
#print axioms P5J.k03_digRow_at
#print axioms P5J.k03_readsRow_at
#print axioms P5J.k03_headRow_at
#print axioms P5J.k03_pads_at
#print axioms P5J.k03_offC_at
