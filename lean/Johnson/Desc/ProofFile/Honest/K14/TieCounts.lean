-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/TieCounts.lean: kind K14: THE TWO TEXTS OF A SENDING COUNT THEIR
COINS ALIKE, MESSAGE BY MESSAGE, AT ANY NUMBER OF MESSAGES: where message number k's coins begin in
the shared sending's part (startR, Honest/K1/Coins.lean) is where they begin in this kind's own part
(offsetOf, Honest/K14/Sendings.lean), and all coins are of the extension field. Statements, each
with its proof. General in the job J, under the one public test on its shapes.

  msg_fits        what the test on a sending's shapes says of one message
  dueMsg_tie      one message's count in the two texts
  offset_succ     offsetOf at the next message
  start_tie       **startR J.Q (rideBySort J) k = ⟨0, offsetOf J.Q.codes J.Q.sent J.sort k⟩**, at
                  every k up to the number of messages
  due_tie         **dueR J.Q (rideBySort J) = (sendingPart J).takes**
  fits_tie        **sendFits J.Q (rideBySort J) = true**: the shared part's public test accepts

How it goes. By induction on k; one message by due_vec, due_mask and due_ride
(Honest/K14/SendingsViaCounts.lean), whose premises are read off the arm of msgShapeFits that
accepts. fits_tie clause by clause: what the shared part's test asks of a message, this kind's test
asks too.

What is assumed. sendShapeFits J = true (Honest/K14/SendingsShapes.lean).
What is not claimed. That any book has these counts. Nothing on what a coin is used for: that is the
rows' matter. Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.ExactDefs
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes
import Johnson.Desc.ProofFile.Honest.K14.SendingsViaCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (K1.Msg.of)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (dueR startR dueMsg sendFits rideFits)

/-- What the test on a sending's shapes says of message number k. -/
theorem msg_fits (J : SendJob) (hfit : sendShapeFits J = true) (k : Nat)
    (hk : k < J.Q.sent.size) : msgShapeFits J.Q.codes (shapeAt J.Q k) (J.sort k) = true := by
  unfold sendShapeFits at hfit
  rw [Bool.and_eq_true] at hfit
  exact List.all_eq_true.1 hfit.2 k (List.mem_range.2 hk)

/-- **One message's count in the two texts.** -/
theorem dueMsg_tie (J : SendJob) (hfit : sendShapeFits J = true) (k : Nat)
    (hk : k < J.Q.sent.size) :
    dueMsg J.Q.codes (shapeAt J.Q k) (rideBySort J k) =
      ⟨0, dueOf J.Q.codes (shapeAt J.Q k) (J.sort k)⟩ := by
  have h := msg_fits J hfit k hk
  unfold rideBySort
  cases hs : J.sort k with
  | plain high =>
    rw [hs] at h
    simp only [msgShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    rcases h.2 with ⟨⟨⟨⟨hz, -⟩, h3⟩, -⟩, ha⟩ | ⟨hm, hz⟩
    · exact due_vec _ _ high h3 hz (by omega)
    · exact due_mask _ _ high hm (Or.inl (by omega))
  | fresh k' h' =>
    rw [hs] at h
    simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨-, ha⟩, hm⟩, -⟩, -⟩, -⟩, -⟩ := h
    exact due_ride _ _ k' h' hm ha

/-- offsetOf at the next message. -/
theorem offset_succ (codes : Codes) (sent : Array OracleNotice) (sort : Nat → MsgSort) (k : Nat)
    (hk : k < sent.size) :
    offsetOf codes sent sort (k + 1) =
      offsetOf codes sent sort k + dueOf codes (sent.getD k default).shape (sort k) := by
  have hl : k < sent.toList.length := by
    rw [Array.length_toList]
    exact hk
  have hg : sent.toList[k]? = some (sent.getD k default) := by
    rw [Array.getElem?_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    rfl
  unfold offsetOf
  rw [List.take_add_one, hg, Option.toList_some, List.zipIdx_append, List.foldl_append,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt hl)]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, Nat.zero_add]

/-- **Where message number k's coins begin, in both texts: one number**; no coin of the base
field. -/
theorem start_tie (J : SendJob) (hfit : sendShapeFits J = true) (k : Nat)
    (hk : k ≤ J.Q.sent.size) :
    startR J.Q (rideBySort J) k = ⟨0, offsetOf J.Q.codes J.Q.sent J.sort k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < J.Q.sent.size := hk
    have e : startR J.Q (rideBySort J) (k + 1) =
        (startR J.Q (rideBySort J) k).plus
          (dueMsg J.Q.codes (shapeAt J.Q k) (rideBySort J k)) := by
      unfold startR
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e, ih (Nat.le_of_lt hk'), dueMsg_tie J hfit k hk', offset_succ _ _ _ k hk']
    rfl

/-- **The two parts take as many coins.** -/
theorem due_tie (J : SendJob) (hfit : sendShapeFits J = true) :
    dueR J.Q (rideBySort J) = (sendingPart J).takes :=
  start_tie J hfit J.Q.sent.size (Nat.le_refl _)

/-- **The shared part's public test accepts.** -/
theorem fits_tie (J : SendJob) (hfit : sendShapeFits J = true) :
    sendFits J.Q (rideBySort J) = true := by
  have h0 := hfit
  unfold sendShapeFits at h0
  rw [Bool.and_eq_true, Bool.and_eq_true] at h0
  unfold sendFits
  rw [Bool.and_eq_true]
  refine ⟨h0.1.1, List.all_eq_true.2 fun k hk => ?_⟩
  have h := msg_fits J hfit k (List.mem_range.1 hk)
  unfold rideBySort
  cases hs : J.sort k with
  | plain high =>
    rw [hs] at h
    simp only [msgShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    obtain ⟨⟨hA, hB⟩, -⟩ := h
    rcases hB with e | e
    · simp [hA, e]
    · simp [hA, e]
  | fresh k' h' =>
    rw [hs] at h
    simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hA, ha⟩, hm⟩, hr⟩, hhk⟩, h1k⟩, hl⟩ := h
    have hR : rideFits J.Q.codes (shapeAt J.Q k) { k := k', h := h' } = true := by
      simp only [rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨ha, hm⟩, hr⟩, hhk⟩, h1k⟩, hl⟩
    simp [hA, ha, hR]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.msg_fits
#print axioms ProofFile.Honest.K14.dueMsg_tie
#print axioms ProofFile.Honest.K14.offset_succ
#print axioms ProofFile.Honest.K14.start_tie
#print axioms ProofFile.Honest.K14.due_tie
#print axioms ProofFile.Honest.K14.fits_tie
