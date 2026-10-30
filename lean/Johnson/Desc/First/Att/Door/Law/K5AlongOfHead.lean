-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5AlongOfHead.lean: kind K5: **THE KIND's SEVEN FACTS ALONG "REACHED" (K5Along, Door/Law/K5Along.lean) FROM THE HEAD ALONE, AND SO THE KIND's SHARE IN ANOTHER FILE's OWN NAME (P5J.AtMgA.Kind, Johnson/P5J/RowsAtAll.lean) FROM THE HEAD AND THE KIND's NAMED CONDITION.**
A joining: calls. It turns nothing of the condition (K5CondAt, Door/Law/K5LeftOfCond.lean) or of the theorem k05_kind_of_cond (Door/Law/K05KindOfCond.lean).
WHOSE THEOREM PAYS WHAT. (1) Five of the seven are fields of the head with the facts on every reached state (AtMgR, Johnson/P5J/AtMgR.lean): k5Along_of_fold (Door/Law/K5AlongAt.lean). (2) That head, at the head's own condition "reached", from
the head and the two entry tests' accepts: H2K12.reached_of_pins (Johnson/Loose/H2K12/ReachedOfPins.lean), a call of P5J.atMgR_madeRow (Johnson/P5J/FoldJ3Whole.lean): THE INDUCTION ALONG THE RUN STANDS IN OTHER FILES:
these files must lie in the build. (3) The two entry tests' accepts from the head: pins_at_head (Door/Law/K5CondOfHead.lean), a call of P5J.AtMg.pins (Johnson/P5T/FenceAtMg.lean). (4) The four equations Written354 from the head:
H2K12.written354_of_pins (Johnson/Loose/H2K12/ClosedOfPins354.lean). (5) The other two of the seven (bare · left): bare_at | left_at (Door/Law/K5AlongAt.lean).
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)

OVER Johnson/Desc/Laid/ProofAsks.lean AND Johnson/P5J/MgAtAll.lean, WHOSE HEAD HAS THE FIELDS opts · k3.

Main names:
  **k5Along_at_head**: the head · the listed seats are L → K5Along h.toAtMg.rch L (At.d12 Zp L).M h.𝔇.sent.
  **k05_kind_at_head**: the head · the three equations on the letter 𝔏 · (∀ L, the listed seats are L → K5CondAt h L) → h.Kind 𝔏 .K5.
  **k05_kind_at_head₂**: the same with the condition paid as far as Door/Law/K5CondOfHead.lean pays it: from k5PlansB₂ = true (no letter) · pads · cells.
IS IT EMPTY HERE? IMPLICATIONS FROM THE HEAD. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). THAT k5PlansB₂ IS true IS NOT SHOWN IN LEAN. THE KIND's LAW IS NOT PROVED.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05KindOfCond
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead
import Johnson.Desc.First.Att.Door.Law.K5AlongAt
import Johnson.Loose.H2K12.ReachedOfPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Model OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K12.Door (Laid)
open P5J (AtMg AtMgA F0T TS Free)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE SEVEN FACTS ALONG "REACHED", FROM THE HEAD ALONE.** -/
theorem k5Along_at_head {L : Laid} (hl : P5J.At.laid? Zp = some L) :
    K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent :=
  k5Along_of_fold h h.toAtMg.rch
    (H2K12.reached_of_pins h (H2K12.written354_of_pins h.scope h.laid.pub (pins_at_head h.toAtMg).1 h.laid.laidPOf)
      (pins_at_head h.toAtMg).1 (pins_at_head h.toAtMg).2 hl)
    (fun g hg a hr => bare_at h.toAtMg g hg a hr.1) (fun g hg a hr => left_at h.toAtMg g hg a hr.1)

variable (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **THE KIND's SHARE P5J.AtMgA.Kind (RowsAtAll.lean), FROM THE HEAD AND THE NAMED CONDITION.** -/
theorem k05_kind_at_head (U : ∀ L, P5J.At.laid? Zp = some L → K5CondAt h L) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_of_cond h 𝔏 q₁ q₂ q₃ (fun _ hL => k5Along_at_head h hL) U

/-- **The same, with the condition paid as far as it is paid: from one Bool without a letter, pads and cells.** -/
theorem k05_kind_at_head₂ (hW : k5PlansB₂ = true) (pads : PadsAll h)
    (cells : ∀ g, g < 12 → ∀ (a : Attention.Plan) (x₁ : Look.Place), (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ → ∃ idx, K5CellsCond h a x₁ idx) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_at_head h 𝔏 q₁ q₂ q₃ fun _ hL => k5CondAt_of_head₂ hL hW pads cells

end H2K5.Door

#print axioms H2K5.Door.k5Along_at_head
#print axioms H2K5.Door.k05_kind_at_head
#print axioms H2K5.Door.k05_kind_at_head₂
