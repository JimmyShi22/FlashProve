-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/AtFirstThread.lean: `K7Five` (Honest/K7/Five.lean) at `firstThread`
(Honest/Thread/TheFirstThread.lean): the thread of the first chain at a return of the
maker.

  `k7_five_first`   the member's four and its test on values at that thread
  `asked_at_valid`   what a valid input gives of the asked reply
  `k7_five_of_token`   the same with one premise on the script: its token is the asked reply's number

Its premises: the base that the public part's seat makes, and on the honest prover the three of
`k7_five_at_head`. This file proves nothing about soundness, completeness, hiding or any other property of
the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.Five
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.AskedIsToken
import Johnson.P5J.VocabAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.FirstThread
open OnBytes.Desc.Reply (isToken)
open Johnson.AtFull.Shape
open P5J (TS)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **THE MEMBER's FIVE AT THE FIRST THREAD.** -/
theorem k7_five_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) {Vh : Nat}
    (hhalf : A.H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    (hq : ∀ v : Local W₀ Rc ProofFile.Inst Tr, (firstThread h parts w).valid v →
      parts.script.tok v = v.x.asked.c0.toNat ∧
        OnBytes.Model.ofNat v.x.asked.c0.toNat = v.x.asked)
    (hv : ∀ v : Local W₀ Rc ProofFile.Inst Tr, (firstThread h parts w).valid v →
      isToken Bs.G₀.W.hS.V v.x.asked = true)
    (J : Nat → TS → Prop) (g : Nat → ShA → Except String ShA)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    K7Five (firstThread h parts w) Said J (firstZA g (Tab.vals A.Z Bs.G₀)) fall := by
  have e : firstClauses h = fHeadJ A.Z h.firstChain Bs.G₀ P1L20.bearing (K11.parOf A.Z Bs.G₀)
      (H2U.p12OfMade A.Z.made) (VerifiableInference.Desc.K13.whereOf A.Z) h.head.𝔇.pubD := by
    unfold firstClauses
    rw [seatGround_of_base hB]
  revert hq hv
  unfold firstThread firstLetters
  rw [e]
  intro hq hv
  exact k7_five_at_head h.head A.H parts.script _ 0 _ _ _ w Said hB hhalf hq hv J g fall

/-- **What a valid input gives of the asked reply**: it is a token of the vocabulary, and the field's
element of its own number. By the test on the instance, which `ReadyInput` holds. -/
theorem asked_at_valid (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr) {v : Local W₀ Rc ProofFile.Inst Tr}
    (hv : (firstThread h parts w).valid v) :
    isToken A.Z.p.X.hS.V v.x.asked = true ∧
      OnBytes.Model.ofNat v.x.asked.c0.toNat = v.x.asked := by
  have hr : ReadyInput h.description A.H v := hv.2
  have hok := (Bool.and_eq_true_iff.1 hr.1).1
  obtain ⟨hP, hSV, -⟩ := P5J.vocab_at_head h.head.toAtMg
  have hV : A.Z.p.X.hS.V = A.Z.p.X.P.h.V := hSV.trans hP.symm
  have hp : A.Z.p.X.hS.V ≤ OnBytes.pW.toNat := by
    have e : A.Z.p.X.hS.V = Inst.Model.ppref.V := hSV
    rw [e]
    decide +kernel
  exact ⟨asked_is_token hok hV hp, asked_ofNat hok hV hp⟩

/-- **THE MEMBER's FIVE AT THE FIRST THREAD, from the look-up and the script's token.** -/
theorem k7_five_of_token (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) {Vh : Nat}
    (hhalf : A.H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    (htok : ∀ v : Local W₀ Rc ProofFile.Inst Tr, (firstThread h parts w).valid v →
      parts.script.tok v = v.x.asked.c0.toNat)
    (J : Nat → TS → Prop) (g : Nat → ShA → Except String ShA)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    K7Five (firstThread h parts w) Said J (firstZA g (Tab.vals A.Z Bs.G₀)) fall := by
  obtain ⟨Bs', base, O⟩ := h.head.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  have hW : Bs.G₀.W = A.Z.p.X := O.W
  refine k7_five_first h parts w Said hB hhalf (fun v hv => ⟨htok v hv, (asked_at_valid h parts w hv).2⟩)
    (fun v hv => ?_) J g fall
  rw [hW]
  exact (asked_at_valid h parts w hv).1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k7_five_first
#print axioms ProofFile.Honest.FirstThread.asked_at_valid
#print axioms ProofFile.Honest.FirstThread.k7_five_of_token
