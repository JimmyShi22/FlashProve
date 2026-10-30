-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/BehindCs.lean: the closing of a segment against the list of clauses meant for `rides` of the first chain's thread at the
full size (`csHead`, Honest/Thread/CsHead.lean): which of the 55 clauses a closing lays, which span it, and that these go on.

  `closing_lo_ne`       no clause begins at the border behind a closing: so the closing lays none (`closing_lays`: the
                       gathering lemma's column hl at the 25 borders holds for want of a clause)
  `closing_clause_on`   a clause that spans a closing goes on over `K10Keeps`. One does: "the head's merge has laid its claim"
                       (from border 347 to 352) spans the last segment's closing (350): `keeps_head`
                       (Johnson/Desc/K10/Honest/KeepsStep.lean)
  `closing_stays`       (column hst) `StaysBy` at the 25 borders
  `riders_on_closing`   the whole list, from the border to the next
  `closing_b0`          339 is not the border behind a closing
  **`behindS_closing_head_form`**, `behindS_closing_head`   `BehindS` at b₀ := 339 and Rd := `ridersOf (csHead ν st R)`, with ν, st, R letters

Limits. hK (or hKp) is a premise on the letter Kp. The head is a hypothesis. That the thread holds of any run is not shown.
The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.Behind
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.RidersStayH

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (K10Keeps keeps_head)
open P5J (AtMgA CellsM TS)

section
variable {W : Type} {ν : Nat} {st : Nat → TS → Prop}
  {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}

theorem nAt_cases (l : Nat) : (l ≠ 24 ∧ IM.nAt l = 7) ∨ (l = 24 ∧ IM.nAt l = 9) := by
  unfold IM.nAt
  by_cases c : l = 24
  · exact Or.inr ⟨c, if_pos c⟩
  · exact Or.inl ⟨c, if_neg c⟩

/-- **No clause begins at the border behind a closing.** -/
theorem closing_lo_ne (l : Nat) {c : RiderCl W TS} (hc : c ∈ csHead ν st R) :
    c.lo ≠ 14 * l + IM.nAt l + 5 + 1 := by
  intro e
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  all_goals
    dsimp only [riderHead, riderAtt] at e
    rcases nAt_cases l with ⟨_, h7⟩ | ⟨_, h9⟩ <;> omega

/-- **A clause that spans a closing goes on.** -/
theorem closing_clause_on {l : Nat} (_hl : l < 25) {c : RiderCl W TS} (hc : c ∈ csHead ν st R)
    (hlo : c.lo ≤ 14 * l + IM.nAt l + 5) (hhi : 14 * l + IM.nAt l + 5 + 1 ≤ c.hi) {s s' : TS}
    (K : K10Keeps s s') (v : W) (hp : c.prop (14 * l + IM.nAt l + 5) v s) :
    c.prop (14 * l + IM.nAt l + 5 + 1) v s' := by
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  case inl.inl.inl.inr.inr.inl =>
    obtain ⟨a, ha, hw⟩ := hp
    obtain ⟨a', e, -, -, ew⟩ := keeps_head K.1 a ha
    exact ⟨a', e, by
      show a'.wo.isSome = true
      rw [ew]
      exact hw⟩
  all_goals
    exfalso
    dsimp only [riderHead, riderAtt] at hlo hhi
    rcases nAt_cases l with ⟨_, h7⟩ | ⟨_, h9⟩ <;> omega

/-- **The whole list, from the border in front of a closing to the next.** -/
theorem riders_on_closing {l : Nat} (hl : l < 25) {s s' : TS} (K : K10Keeps s s') (v : W)
    (hr : ridersOf (csHead ν st R) (14 * l + IM.nAt l + 5) v s) :
    ridersOf (csHead ν st R) (14 * l + IM.nAt l + 5 + 1) v s' := by
  intro c hc hlo hhi
  have h1 : c.lo ≤ 14 * l + IM.nAt l + 5 := by
    have := closing_lo_ne l hc
    omega
  exact closing_clause_on hl hc h1 hhi K v (hr c hc h1 (by omega))

/-- 339 is not the border behind a closing. -/
theorem closing_b0 (l : Nat) : 339 ≠ 14 * l + IM.nAt l + 5 + 1 := by
  rcases nAt_cases l with ⟨_, h7⟩ | ⟨_, h9⟩ <;> omega

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
  (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

set_option quotPrecheck false in
/-- The first chain's thread at the head's letters, its riders the written list. -/
local notation "𝕋" =>
  (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread

/-- **The closing lays no clause** (the gathering lemma's column hl at the 25 borders). -/
theorem closing_lays (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat}
    (_hl : l < 25) : ∀ c ∈ csHead ν st R, c.lo = 14 * l + IM.nAt l + 5 + 1 →
      LaysAtS (𝕋) Said (14 * l + IM.nAt l + 5) c :=
  fun _ hc e => absurd e (closing_lo_ne l hc)

/-- **Every clause that spans a closing stays** (column hst at the 25 borders). -/
theorem closing_stays (hKp : ∀ p s s', p.kind = KindName.K10 → Kp p s s' → K10Keeps s s')
    {l : Nat} (hl : l < 25) : ∀ c ∈ csHead ν st R, c.lo ≤ 14 * l + IM.nAt l + 5 →
      14 * l + IM.nAt l + 5 + 1 ≤ c.hi → StaysBy (𝕋) (14 * l + IM.nAt l + 5) c :=
  fun _ hc hlo hhi v s s' hk hp => closing_clause_on hl hc hlo hhi
    (k10Keeps_of_thread_keeps h H Sc test carryX item n₁ n₂ b₀ Vd _ Kp w hKp hl s s' hk) v hp

/-- `BehindS` at the closings, at the written list of riders and b₀ := 339, where the letter Kp may ask
the form behind too. -/
theorem behindS_closing_head_form {l : Nat} (hl : l < 25)
    (hK : ∀ p s s' k m', P5J.At.ps[14 * l + IM.nAt l + 5]? = some p → p.kind = KindName.K10 →
      K10Keeps s s' →
      (lettersHead h H Sc test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) Kp w).thread.Form
        (14 * l + IM.nAt l + 5 + 1) k s' m' → Kp p s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    BehindS (lettersHead h H Sc test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) Kp
      w).thread Said (14 * l + IM.nAt l + 5) :=
  behindS_at_closing_form h H Sc test carryX item n₁ n₂ 339 Vd _ Kp w hl hK Said (closing_b0 l)
    fun v _ _ K hr => riders_on_closing hl K v hr

/-- **`BehindS` AT THE CLOSINGS, AT THE WRITTEN LIST OF RIDERS AND b₀ := 339.** -/
theorem behindS_closing_head
    (hK : ∀ p s s', p.kind = KindName.K10 → K10Keeps s s' → Kp p s s')
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat} (hl : l < 25) :
    BehindS (lettersHead h H Sc test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) Kp
      w).thread Said (14 * l + IM.nAt l + 5) :=
  behindS_at_closing h H Sc test carryX item n₁ n₂ 339 Vd _ Kp w hK Said hl (closing_b0 l)
    fun v _ _ K hr => riders_on_closing hl K v hr

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.nAt_cases
#print axioms ProofFile.Honest.K10.closing_lo_ne
#print axioms ProofFile.Honest.K10.closing_clause_on
#print axioms ProofFile.Honest.K10.riders_on_closing
#print axioms ProofFile.Honest.K10.closing_b0
#print axioms ProofFile.Honest.K10.closing_lays
#print axioms ProofFile.Honest.K10.closing_stays
#print axioms ProofFile.Honest.K10.behindS_closing_head_form
#print axioms ProofFile.Honest.K10.behindS_closing_head
