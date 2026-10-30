-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FormXKFront.lean: WHAT THE FORM IN FRONT HANDS AN AUTHOR's
LEMMA, AND IN WHICH LETTERS. `form_of_xk` (Honest/Thread/FormXK.lean) says what the form at a
border is made of: no mark · `IM.XK` · `samplesHeld` · `pubP`. The way back: the form gives all
four: `xk_of_form` has the second; here the third and the fourth: so an author's lemma on the state
behind its member may take all of them at the state in front as named premises, and we pay them
from the thread. AND THE LETTERS: at `lettersHead` the promise's meaning is "honest" over the
library's own `P5J.mgAtAll h`; "honest" turns pin, noColl, shown, decodes and totalB, and no other
field: so pub, more, inOrder, pubP and held ARE the library's, by unfolding; the numbers, the
segments' sorts and the places are `P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps`; the public part
is the instance's. An author states its lemmas at these terms, or at letters. No definition.
Conditional lemmas and equations by unfolding.

  `held_of_form`, `pubP_of_form`   general in the first chain's letters
  `head_pub_is`, `head_more_is`, `head_inOrder_is`, `head_pubP_is`, `head_held_is`   the five fields
  `head_xk_is`, `head_samples_is`   XK at EQ and samplesHeld at `lettersHead` in the library's terms

Limits. The full size and the format's second hash function alone: as the library's head, which is a
premise. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormXK
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S onAt samplesHeld Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- The form gives "held". -/
theorem held_of_form (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) :
    samplesHeld L.N L.mgP (IM.openAt L.links L.ps b) (L.pubOf m.st.input.x, s) = true := by
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have ha : onAt L.N L.mgP L.links L.ps[b]? (IM.openAt L.links L.ps b)
      (P1K2.pubAt L.mgP L.links L.ps b) (L.pubOf m.st.input.x, s) noStrs := hF.2
  rcases ha.2 with hm | ⟨-, hh, -, -⟩
  · exact absurd h0 hm
  · exact hh

/-- The form gives what the open public items say beside their Bools. -/
theorem pubP_of_form (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) :
    ∀ q ∈ P1K2.pubAt L.mgP L.links L.ps b, L.mgP.pubP q (L.pubOf m.st.input.x, s) := by
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have ha : onAt L.N L.mgP L.links L.ps[b]? (IM.openAt L.links L.ps b)
      (P1K2.pubAt L.mgP L.links L.ps b) (L.pubOf m.st.input.x, s) noStrs := hF.2
  rcases ha.2 with hm | ⟨-, -, -, hp⟩
  · exact absurd h0 hm
  · exact hp

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

theorem head_pub_is :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub =
      (P5J.mgAtAll h).pub := rfl

theorem head_more_is :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more =
      (P5J.mgAtAll h).more := rfl

theorem head_inOrder_is :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.inOrder =
      (P5J.mgAtAll h).inOrder := rfl

theorem head_pubP_is :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP =
      (P5J.mgAtAll h).pubP := rfl

theorem head_held_is :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.held =
      (P5J.mgAtAll h).held := rfl

/-- **THE SIX Bools AT `lettersHead`, IN THE LIBRARY's OWN TERMS.** -/
theorem head_xk_is (z : ProofFile.InstPub) (c : Nat) (s : TS) :
    IM.XK (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps
      (P1K2.EQ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps z) c s =
      IM.XK (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
        (P1K2.EQ (P5J.mgAtAll h) P5J.At.links P5J.At.ps z) c s := rfl

/-- "Held", likewise. -/
theorem head_samples_is (O : List Item) (a : ProofFile.InstPub × TS) :
    samplesHeld (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP O a =
      samplesHeld (P5J.At.N Zp cF) (P5J.mgAtAll h) O a := rfl

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.held_of_form
#print axioms ProofFile.Honest.FirstThread.pubP_of_form
#print axioms ProofFile.Honest.FirstThread.head_pub_is
#print axioms ProofFile.Honest.FirstThread.head_more_is
#print axioms ProofFile.Honest.FirstThread.head_inOrder_is
#print axioms ProofFile.Honest.FirstThread.head_pubP_is
#print axioms ProofFile.Honest.FirstThread.head_held_is
#print axioms ProofFile.Honest.FirstThread.head_xk_is
#print axioms ProofFile.Honest.FirstThread.head_samples_is
