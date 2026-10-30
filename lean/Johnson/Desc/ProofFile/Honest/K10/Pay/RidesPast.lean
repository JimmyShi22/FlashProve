-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/RidesPast.lean: at the first chain's thread of the honest side at the full size (`lettersHead`,
Honest/Thread/FirstHead.lean), at the border in front of the closing of each of the 25 segments: every item that is open there
and that the closing's row neither shuts nor owes says, of every state that the thread's `keeps` ties to the state in
front and at the strings behind any played rounds, what it says in front, in that one direction: where it holds in front it
holds behind (`RidesPastS`, Honest/Thread/PaysS.lean).

  `k10Keeps_of_thread_keeps`        the thread's `keeps` at the border gives `K10Keeps`, from the premise hKp on the letter Kp
  `ridesPastAtS_closing`    one rider
  **`ridesPastS_at_closing`**   all riders

Sort by sort. "No mark": `K10Keeps` says it of the state behind. The index masks' pin: it reads each message's first sample
row alone, which is kept (`ridesPastAt_pinI_older`, Honest/Thread/PinForward.lean). The weights' pin, the pile, the parts of
later segments' relations, and what the own rounds leave for the row on the weights: RidesLaws.lean; the last wants that the
index masks' message is a member of no group in front, which the thread gives (`k10_out_of_groups`,
Honest/K10/Law/FormBehind.lean). Which sorts ride: RidesList.lean.

Limits. hKp is a premise: the letter Kp at a place of the kind K10 gives `K10Keeps`. The head is a hypothesis. That the thread
holds of any run is not shown; where it holds of none the theorem says nothing. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.RidesLaws
import Johnson.Desc.ProofFile.Honest.K10.Pay.RidesList
import Johnson.Desc.ProofFile.Honest.K10.Law.FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.PinForward
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (K10Keeps keeps_st)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

set_option quotPrecheck false in
/-- The first chain's thread at the head's letters. -/
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- The thread's `keeps` at the border in front of a closing gives `K10Keeps`. -/
theorem k10Keeps_of_thread_keeps (hKp : ∀ p s s', p.kind = KindName.K10 → Kp p s s' → K10Keeps s s')
    {l : Nat} (hl : l < 25) (s s' : TS) (hk : (𝕋).keeps (14 * l + IM.nAt l + 5) s s') :
    K10Keeps s s' := by
  obtain ⟨p, hp, hK⟩ := k10_place_head hl
  exact hKp p s s' hK ((head_keeps h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').1 hk)

/-- **One rider.** -/
theorem ridesPastAtS_closing (hKp : ∀ p s s', p.kind = KindName.K10 → Kp p s s' → K10Keeps s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat} (hl : l < 25)
    (i : Item) (hi : riderK i = true) :
    RidesPastAtS (𝕋) Said (14 * l + IM.nAt l + 5) i := by
  have hK := k10Keeps_of_thread_keeps h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hKp hl
  cases i with
  | unmarked =>
    exact ridesPastAtS_of _ _ (ridesPastAt_unmarked h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (fun s s' k => (hK s s' k).2))
  | pinI =>
    exact ridesPastAtS_of _ _ (ridesPastAt_pinI_older h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (fun _ s _ _ s' _ k o q hq =>
        (rowAt₀_same ((keeps_st (hK s s' k).1.1).2.2.2.1 o)).trans hq))
  | pinW =>
    intro k s m E s' ps v _ _ h0
    exact pinW_on_k10 h (Sc.cells m.st.input) carryX s s' ((𝕋).strs E) ((𝕋).strs (E.add ps)) v h0
  | pile =>
    intro k s m E s' ps v _ hk h0
    exact pile_on_k10 h (Sc.cells m.st.input) carryX (hK s s' hk) ((𝕋).strs E) ((𝕋).strs (E.add ps)) v
      h0
  | wo n =>
    intro k s m E s' ps v hA hk h0
    obtain ⟨p, hp, hKd⟩ := k10_place_head hl
    exact wo_on_k10 h (Sc.cells m.st.input) carryX n (hK s s' hk)
      (k10_out_of_groups h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hp hKd hA.1)
      ((𝕋).strs E) ((𝕋).strs (E.add ps)) v h0
  | constr n p =>
    intro k s m E s' ps v _ hk h0
    have hp : p ≠ .lookDigits := by
      rintro rfl
      simp [riderK] at hi
    exact constr_on_k10 h (Sc.cells m.st.input) carryX n p hp (hK s s' hk) ((𝕋).strs E)
      ((𝕋).strs (E.add ps)) v h0
  | _ => simp [riderK] at hi

/-- **EVERY ITEM THAT RIDES PAST THE CLOSING OF A SEGMENT SAYS BEHIND WHAT IT SAYS IN FRONT.** -/
theorem ridesPastS_at_closing
    (hKp : ∀ p s s', p.kind = KindName.K10 → Kp p s s' → K10Keeps s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat} (hl : l < 25) :
    RidesPastS (𝕋) Said (14 * l + IM.nAt l + 5) :=
  ridesPastS_shares _ _ fun i ho hs hw =>
    ridesPastAtS_closing h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hKp Said hl i
      (riders_at_closing hl i ho hs hw)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.k10Keeps_of_thread_keeps
#print axioms ProofFile.Honest.K10.ridesPastAtS_closing
#print axioms ProofFile.Honest.K10.ridesPastS_at_closing
