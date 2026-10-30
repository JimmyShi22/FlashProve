-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/FoldJ3Whole.lean: THE JOIN OF FoldFacts, THE LAST CALL: THE FIELD "fold" OF THE HEAD
WITH THE FACTS ON EVERY REACHED STATE (AtMgR, Johnson/P5J/AtMgR.lean) AS A THEOREM WHOLE: the value
of Johnson/P5J/FoldJ3.lean with its two premises room and roomEarly paid by
room_at_head | roomEarly_at_head (Johnson/P5J/FoldJ1.lean), under the public test startB. A JOINING:
IT PAYS NOTHING OF ITS OWN. NO BLOCK IMPORTS THIS FILE.

  foldFacts_at_head'   (h) (Rch) (hR) (hl) (hs) (hB) ⊢ FoldFacts Rch (fun a => a.1) (At.foldD Zp cF
                    L) At.reqW At.links At.ps
  atMgR_of'         the same premises ⊢ AtMgR OnBytes.secondHashFunction Z D r Zp Np cF Rch (fun a => a.1) L
  atMgR_madeRow     with PlanWritten.madeRow Zp = true in hB's place

Premises that stay, beside the head h and hR: hl (the list of seats is laid) · hs (startB) · hB
(SendsB Zp) or madeRow: tests on the public part alone.
Limits. Nothing is shown met here: NO MEMBER. At Rch := never every field is free. No soundness
statement.

-/
import Johnson.P5J.FoldJ3
import Johnson.P5J.FoldJ1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open OnBytes.Maker (WholeD)
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {Str : Type}
  (Rch : ℕ → ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) × Str → Prop)
  (hR : ∀ k a, Rch k a → RchAt (F0T OnBytes.secondHashFunction Zp Np cF) k a)

include h hR

/-- **FoldFacts at the head's closed term, whole.** -/
theorem foldFacts_at_head' {L : K12.Door.Laid} (hl : At.laid? Zp = some L)
    (hs : FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true)
    (hB : SendsB Zp) :
    FoldFacts Rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps :=
  foldFacts_at_head h Rch hR hl hB (room_at_head h Rch hR L hs) (roomEarly_at_head h Rch hR L hs)

/-- **The head with the facts on every reached state.** -/
theorem atMgR_of' {L : K12.Door.Laid} (hl : At.laid? Zp = some L)
    (hs : FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true)
    (hB : SendsB Zp) : AtMgR OnBytes.secondHashFunction Z D r Zp Np cF Rch (fun a => a.1) L :=
  { h with listed := hl, start := hs, fold := foldFacts_at_head' h Rch hR hl hs hB }

/-- The same, under the row on the made plan. -/
theorem atMgR_madeRow {L : K12.Door.Laid} (hl : At.laid? Zp = some L)
    (hs : FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1) (At.N Zp cF).indexNo = true)
    (hy : VerifiableInference.PlanWritten.madeRow Zp = true) :
    AtMgR OnBytes.secondHashFunction Z D r Zp Np cF Rch (fun a => a.1) L :=
  atMgR_of' h Rch hR hl hs (sendsB_of_madeRow h hy)

end P5J

#print axioms P5J.foldFacts_at_head'
#print axioms P5J.atMgR_of'
#print axioms P5J.atMgR_madeRow
