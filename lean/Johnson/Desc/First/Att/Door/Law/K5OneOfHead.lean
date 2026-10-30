-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/First/Att/Door/Law/K5OneOfHead.lean: THE NAMED TEST oneC (`P5J.AtMgA.oneC`,
Johnson/P5J/K03OneOwnAt.lean: the lookup argument's premise "one" at link l, as a test with code at
the closed constant's own terms) IS A THEOREM UNDER THE HEAD, AT EVERY l < 24. After the pattern of
Johnson/Top/H0/K2Ties/OffAt.lean | OffHead.lean.

  `oneC_at`: h.oneC l = true from `AtWritten` (Johnson/Top/H0/K2Ties/WrittenAt.lean) · hx: the view
    of the public parameters' shape is the written one · hF: they have the full size's shape.
  `oneC_head`: the same under the head at the concrete second hash and the pin `madePinnedAt`.
  **`oneC_at_head`**: FROM THE HEAD ALONE: the pin off `AtMg.pins` (Johnson/P5T/FenceAtMg.lean: over
    the entry tests' list of thirteen rows: GLOSSARY.md, "entry tests").
  **`one_of_head`**: so the field one of `K5CellsCond` (Johnson/Desc/First/Att/Door/Law/
    K5RestCells.lean) at the link 2 g + 1 and idx := `idxAt (At.sentAt Zp) (At.num Zp) (2 * g + 1)`:
    by `AtMgA.one_at` (Johnson/P5J/K03OneOwnAt.lean).
Limits. The full size alone. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction;
side library AtFullSide/Top/). `oneC_at_head` and `one_of_head`
stand over the thirteen-row entry tests alone. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Door.Law.K5OneWritten
import Johnson.P5J.K03OneOwnAt
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Maker
open VerifiableInference.OnPublicFiles (OneNumber)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (idxAt sigListCalls)
open VerifiableInference.Desc.First.K2Ties (AtWritten at_written)
open VerifiableInference.PlanWritten (madePinnedAt xShapeOf pinnedAt_of_row)
open VerifiableInference.PlanWritten.Joined (xShape_in_scope)
open _root_.Meaning.NamedAsk (fullShaped fullShaped_scope)
open Johnson.G (xShapeFull)
open P5J (AtMgA TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **PART 5's NAMED TEST oneC ACCEPTS AT THE CONSTANT's OWN TERMS.** -/
theorem oneC_at (h : AtMgA o Z D r Zp Np cF x) (A : AtWritten Zp cF)
    (hx : xShapeOf Zp.p.X = xShapeFull) (hF : fullShaped Zp.p.X = true) {l : ℕ} (hl : l < 24) :
    h.oneC l = true := by
  show P5J.K03.oneB Zp.p.X (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) (P5J.At.num Zp)
    (idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) l) (_root_.Meaning.tlAt Zp.p.X) l
    (fun j => P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) l j) (P5J.At.arr Zp) id = true
  rw [oneB_view hF _ _ _ _ _ (Nat.lt_succ_of_lt hl), hx,
    oneV_sent _ (D' := sentW) (show P5J.At.shape Zp = _ from A.shape)
      (show P5J.At.layout Zp = _ from A.layout), A.num, A.pseats, A.arr]
  exact List.all_eq_true.1 one_written l (List.mem_range.2 hl)

/-- The same under the head and the pin. -/
theorem oneC_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) {l : ℕ} (hl : l < 24) :
    h.oneC l = true :=
  oneC_at h (at_written h.scope h.laid hy) (xShape_in_scope h.scope h.laid.pub hy)
    (fullShaped_scope h.scope h.reads h.pubOne) hl

/-- **FROM THE HEAD ALONE.** -/
theorem oneC_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 24) :
    h.oneC l = true :=
  oneC_head h (pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true])) hl

/-- **THE FIELD one OF K5's PER-GROUP CONDITION, FROM THE HEAD ALONE.** -/
theorem one_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) :
    OneNumber (P5J.At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (P5J.At.num Zp)
      (idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) (2 * g + 1)) (_root_.Meaning.tlAt (P5J.At.X Zp))
      (2 * g + 1)
      (fun j : Fin (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3
          (2 * g + 1)).length => (h.toAtMg.𝔇 h.𝔇).seat3 (2 * g + 1) false j.1)
      (h.toAtMg.𝔇 h.𝔇).arr id :=
  h.one_at (by omega) (oneC_at_head h (by omega))

end H2K5.Door

#print axioms H2K5.Door.oneC_at
#print axioms H2K5.Door.oneC_head
#print axioms H2K5.Door.oneC_at_head
#print axioms H2K5.Door.one_of_head
