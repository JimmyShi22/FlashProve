-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ConstrHeardRides.lean: the open item `constr m lookCallsHeard`
of the first chain's invariant passes over every sub-protocol that leaves the field `out` of the
verifier's state. No definition.

Of the state the item's statement reads the token of the heard reply alone, which lies in `out`
(`P5J.tokHOf`, Johnson/P5J/TokTerms.lean). The library shows that the statement of an item `constr`
passes between two states, in either direction, if four conditions on its parameters hold
(`K1.constr_back`, Johnson/Desc/K1/Law/GoAtLaterForms.lean), and that the output head's part of it
passes over every relation that keeps the reader of the request and the reader of the heard reply
(`headPartK6_goesBack`, Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean). The two calls are made as in
the library's `const_head` (Johnson/P1K8R/OwesAtConst.lean), with "the field `out` is the same" in
the place of the draw's relation, and from the state before the step to the state after it.

  `ridesPastAt_constr_heard`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item
     at `lettersHead`, at every number `b` and every `m`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * That `keeps b` leaves `out` is a hypothesis. This file shows it for no number.
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.K1.Law.GoAtLaterForms
import Johnson.Desc.Kinds.Law.HeadPartsGoBack
import Johnson.P5J.LettersAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT oneDec)
open VerifiableInference.OnPublicFiles (headLink)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open P5J.At (reqB d₀)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `constr m lookCallsHeard` passes over a sub-protocol whose `keeps` leaves `out`. -/
theorem ridesPastAt_constr_heard {b : Nat} (m : Nat)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.out = s.out) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.constr m .lookCallsHeard) := by
  intro k s mm E s' ps v _ hK h0
  have ho := hk s s' hK
  exact VerifiableInference.Desc.K1.constr_back (headLink (P5J.At.X Zp)) h.𝔇.put
    (oneDec (fun _ _ => some (Q.cells mm.st.input)) h.𝔇.H) h.𝔇.headPart h.𝔇.digitsPart m
    .lookCallsHeard (mm.st.input.x.pub, s') (mm.st.input.x.pub, s)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) v rfl rfl
    (fun i hp => VerifiableInference.Desc.Kinds.Head.Law.headPartK6_goesBack _ _ _ _ _ _ _ _ _ _ _ _
      (fun a _ c _ => a.1 = c.1 ∧ a.2.out = c.2.out)
      (fun a _ c _ hr => by
        show (Meaning.backReq (reqB a.1)).getD d₀ = (Meaning.backReq (reqB c.1)).getD d₀
        rw [hr.1])
      .lookCallsHeard
      (fun _ a _ c _ hr => by
        show P5J.tokVOf ((a.2.replyTok?).getD 0) = P5J.tokVOf ((c.2.replyTok?).getD 0)
        unfold VerifiableInference.Desc.First.S.replyTok?
        rw [hr.2])
      i (mm.st.input.x.pub, s')
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
      (mm.st.input.x.pub, s)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) v ⟨rfl, ho⟩ hp)
    (fun hd => hd) h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.ridesPastAt_constr_heard
