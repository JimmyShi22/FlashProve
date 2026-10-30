-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/Behind.lean: at the first chain's thread of the honest side at the full size (`lettersHead`,
Honest/Thread/FirstHead.lean), behind the step of the closing of each of the 25 segments: what the rule for a sub-protocol asks
under the name `BehindS` (Honest/Thread/PaysS.lean), and the closing's share of four columns of the gathering lemma
`owesS_head` (Honest/Thread/GatherHead.lean), in that lemma's own forms.

  `closing_keeps`     (column hK) the block's place is of the kind K10, and its step gives `K10Keeps`
  `closing_form`      (column hF) behind the step: no mark; the six tests of the table's promise; the samples are held;
                     what the open public items say
  `closing_reply`     (column h₀) from the border b₀ on the state holds the reply that the instance asks about: the closing
                     leaves the reply; under b₀ ≠ b + 1 (the closing does not lay it)
  `closing_rider`     (column hR) = `ridesPastAtS_closing` with `riders_at_closing` (RidesPast.lean, RidesList.lean)
  **`behindS_at_closing_form`**, `behindS_at_closing`   `BehindS` at the border; in the first the premise on Kp may read the
                     form behind the step

Limits. Premises of `behindS_at_closing`, by name: hK: `K10Keeps` gives the letter Kp at a place of the kind K10; hb₀: b₀ is not
the border behind the closing; hRd: the letter Rd goes on over `K10Keeps`, from the border to the next. The head is a
hypothesis. That the thread holds of any run is not shown. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.RidesPast
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.K10.Honest.KeepsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Strs Place KindName step_iff)
open VerifiableInference.Desc.First (Item samplesHeld)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (K10Keeps keeps_six keeps_at_place)
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
/-- The head's letters. -/
local notation "𝕃" => lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w

set_option quotPrecheck false in
/-- The first chain's thread at the head's letters. -/
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **The closing's step gives `K10Keeps`**, and its place is of the kind K10. -/
theorem closing_keeps {l : Nat} (hl : l < 25) :
    ∀ blk, (𝕋).bs[14 * l + IM.nAt l + 5]? = some blk → ∀ k s m E ds y cols s',
      (𝕋).Stepped blk k s m E ds y cols s' →
      blk.place.kind = KindName.K10 ∧ K10Keeps s s' := by
  intro blk hblk k s m E ds y cols s' hS
  obtain ⟨p, hp, hK⟩ := k10_place_head hl
  obtain ⟨B, h1, h2, hk⟩ := keeps_at_place h _ p hp hK
  obtain rfl : B = blk := Option.some.inj (h1.symm.trans hblk)
  obtain ⟨_, hd, _⟩ := (step_iff _ _ _ _ _ _ _).1 hS.2
  exact ⟨by rw [h2]; exact hK, hk _ _ _ _ hd⟩

/-- **The form behind the closing's step**, in the gathering lemma's letters. -/
theorem closing_form {l : Nat} (hl : l < 25) :
    ∀ blk, (𝕋).bs[14 * l + IM.nAt l + 5]? = some blk → ∀ k s m E ds y cols s',
      Thr (𝕋) (14 * l + IM.nAt l + 5) k s m E → (𝕋).Stepped blk k s m E ds y cols s' →
      s'.failed = none ∧
      IM.XK (𝕃).N (𝕃).links (𝕃).ps (P1K2.EQ (𝕃).mgP (𝕃).links (𝕃).ps ((𝕃).pubOf m.st.input.x))
        (14 * l + IM.nAt l + 5 + 1) s' = true ∧
      samplesHeld (𝕃).N (𝕃).mgP (IM.openAt (𝕃).links (𝕃).ps (14 * l + IM.nAt l + 5 + 1))
        ((𝕃).pubOf m.st.input.x, s') = true ∧
      ∀ q ∈ P1K2.pubAt (𝕃).mgP (𝕃).links (𝕃).ps (14 * l + IM.nAt l + 5 + 1),
        (𝕃).mgP.pubP q ((𝕃).pubOf m.st.input.x, s') := by
  intro blk hblk k s m E ds y cols s' hT hS
  have hF := k10_form_behind h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hl blk hblk k s m E ds y
    cols s' hT hS
  obtain ⟨⟨st, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  rw [← ei]
  exact ⟨Option.isNone_iff_eq_none.1 hF.1, xk_of_form _ hF, held_of_form _ hF, pubP_of_form _ hF⟩

/-- **The reply behind the closing's step.** -/
theorem closing_reply {l : Nat} (hl : l < 25) (hb₀ : b₀ ≠ 14 * l + IM.nAt l + 5 + 1) :
    ∀ blk, (𝕋).bs[14 * l + IM.nAt l + 5]? = some blk → ∀ k s m E ds y cols s',
      Thr (𝕋) (14 * l + IM.nAt l + 5) k s m E → (𝕋).Stepped blk k s m E ds y cols s' →
      b₀ ≤ 14 * l + IM.nAt l + 5 + 1 → s'.out.reply = some m.st.input.x.asked := by
  intro blk hblk k s m E ds y cols s' hT hS hb
  have K := (closing_keeps h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hl blk hblk k s m E ds y
    cols s' hS).2
  rw [(keeps_six K).2.2.2.1]
  exact head_reply h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) hT.2.2.2.2.2.1

/-- **One rider**, in the gathering lemma's form. -/
theorem closing_rider (hKp : ∀ p s s', p.kind = KindName.K10 → Kp p s s' → K10Keeps s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat} (hl : l < 25) :
    ∀ i ∈ (𝕋).opened (14 * l + IM.nAt l + 5), i ∉ ((𝕋).row (14 * l + IM.nAt l + 5)).shuts →
      i ∉ ((𝕋).row (14 * l + IM.nAt l + 5)).owes →
      RidesPastAtS (𝕋) Said (14 * l + IM.nAt l + 5) i :=
  fun i ho hs hw => ridesPastAtS_closing h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hKp Said hl i
    (riders_at_closing hl i ho hs hw)

/-- **BEHIND THE CLOSING's STEP: THE FORM, WHAT RIDES, AND WHAT IS KEPT**, where the letter Kp may ask
the form behind too. -/
theorem behindS_at_closing_form {l : Nat} (hl : l < 25)
    (hK : ∀ p s s' k m', P5J.At.ps[14 * l + IM.nAt l + 5]? = some p → p.kind = KindName.K10 →
      K10Keeps s s' → (𝕋).Form (14 * l + IM.nAt l + 5 + 1) k s' m' → Kp p s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hb₀ : b₀ ≠ 14 * l + IM.nAt l + 5 + 1)
    (hRd : ∀ v s s', K10Keeps s s' → Rd (14 * l + IM.nAt l + 5) v s →
      Rd (14 * l + IM.nAt l + 5 + 1) v s') :
    BehindS (𝕋) Said (14 * l + IM.nAt l + 5) := by
  intro blk hblk k s m E ds y cols s' hA _ hS
  have K := (closing_keeps h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hl blk hblk k s m E ds y
    cols s' hS).2
  obtain ⟨p, hp, hKd⟩ := k10_place_head hl
  obtain ⟨⟨st, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have hF := k10_form_behind h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hl blk hblk k s m E ds y
    cols s' hA.1 hS
  refine ⟨hF, ?_, (head_keeps h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').2
      (hK p s s' k y.2 hp hKd K hF)⟩
  rw [ei]
  exact (head_rest h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).2
    ⟨closing_reply h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hb₀ blk hblk k s m E ds y cols s'
      hA.1 hS,
     hRd _ s s' K ((head_rest h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).1
       hA.1.2.2.2.2.2.1).2⟩

/-- The same, where `K10Keeps` alone gives the letter Kp. -/
theorem behindS_at_closing (hK : ∀ p s s', p.kind = KindName.K10 → K10Keeps s s' → Kp p s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat} (hl : l < 25)
    (hb₀ : b₀ ≠ 14 * l + IM.nAt l + 5 + 1)
    (hRd : ∀ v s s', K10Keeps s s' → Rd (14 * l + IM.nAt l + 5) v s →
      Rd (14 * l + IM.nAt l + 5 + 1) v s') :
    BehindS (𝕋) Said (14 * l + IM.nAt l + 5) :=
  behindS_at_closing_form h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hl
    (fun p s s' _ _ _ hk K _ => hK p s s' hk K) Said hb₀ hRd

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closing_keeps
#print axioms ProofFile.Honest.K10.closing_form
#print axioms ProofFile.Honest.K10.closing_reply
#print axioms ProofFile.Honest.K10.closing_rider
#print axioms ProofFile.Honest.K10.behindS_at_closing_form
#print axioms ProofFile.Honest.K10.behindS_at_closing
