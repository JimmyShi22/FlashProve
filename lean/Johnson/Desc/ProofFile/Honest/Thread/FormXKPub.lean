-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FormXKPub.lean: THE SIXTH Bool, "IN ORDER", COSTS NOTHING AT
THE HEAD: SO THE LIBRARY's FENCED LAWS THAT END AT THE PUBLIC TEST ALONE SERVE. `form_of_xk`
(Honest/Thread/FormXK.lean) asks the promise's six Bools as `IM.XK` at `P1K2.EQ`: "in order" and
the public test. Found by two other groups of authors of this project: the library's fenced laws on
what one sub-protocol owes end at a test WITHOUT "in order" (the public test `ePubAt` alone): five
of the six. But over the closed meaning beneath, "in order" at the head's meaning reads the public
part alone, no state: the library's own `mgAll_inOrder_rides`
(Johnson/Desc/Sound/MgAt/InOrderBlind.lean): it rides from any state to any state; and the thread's
form in front has it. No definition. Three conditional lemmas.

  `xk_eq_of_pub`     XK at a test E that gives the public test, and "in order": XK at EQ (general)
  `head_inOrder`     at `lettersHead`: the form at one state gives "in order" at every state
  `head_xk_of_pub`   at `lettersHead`: the form in front and XK at such an E behind: XK at EQ behind

Limits. The full size and the format's second hash function alone. None is one of the library's goals. This
file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormXK
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.First.EPubAt
import Johnson.Desc.Sound.MgAt.InOrderBlind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning pubHeld ePubAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- **FIVE Bools AND "IN ORDER" ARE THE SIX.** E: a test that gives the promise's public test. -/
theorem xk_eq_of_pub {P W : Type} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
    {ps : List Place} {z : P} {k : Nat} {s : S} {E : Nat → S → Bool}
    (hx : IM.XK N links ps E k s = true)
    (hE : E k s = true → ePubAt Mg.pub Mg.more links ps k (z, s) = true)
    (hio : Mg.inOrder (z, s) = true) : IM.XK N links ps (P1K2.EQ Mg links ps z) k s = true := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := IM.xk_parts hx
  have hp : pubHeld Mg (IM.openAt links ps k) (P1K2.pubAt Mg links ps k) (z, s) = true := hE c5
  unfold IM.XK IM.BK P1K2.EQ
  rw [c1, c2, c3, c4, hio, hp]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT THE HEAD "IN ORDER" READS NO STATE**: the form at one state gives it at every state. -/
theorem head_inOrder (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form b k s m) (t : TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.inOrder
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).pubOf m.st.input.x, t) = true := by
  obtain ⟨-, -, -, -, c5⟩ := IM.xk_parts
    (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
  unfold P1K2.EQ at c5
  rw [Bool.and_eq_true] at c5
  exact VerifiableInference.Desc.Sound.mgAll_inOrder_rides (h.toAtMg.𝔇 h.𝔇) _ s t c5.1

/-- **THE SIX BEHIND, FROM THE FORM IN FRONT AND FIVE BEHIND.** -/
theorem head_xk_of_pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b c : Nat} {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Nat → TS → Bool}
    (hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form b k s m)
    (hx : IM.XK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps E c s' = true)
    (hE : E c s' = true → ePubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps c
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).pubOf m.st.input.x, s') = true) :
    IM.XK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps
      (P1K2.EQ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).pubOf m.st.input.x)) c s' =
      true :=
  xk_eq_of_pub hx hE (head_inOrder h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF s')

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.xk_eq_of_pub
#print axioms ProofFile.Honest.FirstThread.head_inOrder
#print axioms ProofFile.Honest.FirstThread.head_xk_of_pub
