-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K9SilentAt.lean: `playsS_k9_silent` (K9Silent.lean) place by
place. At one of the 75 sub-protocols of the kind K9 of the first chain at the full size, `PlaysS`
(Honest/Thread/PaysS.lean) holds at the invariant of `lettersHead` for a prover that has no side at
that sub-protocol's place. Sides at other places, of the kind K9 too, do no harm. No definition.

  1  `k9_block_at`   which sub-protocol stands at the number 14 l + nAt l + j, for j = 2, 4, 6: one
     without a round, or one whose only round is the library's `k9Decl`. From the library's
     `LPFK9.k09_sits` (Johnson/LPFK9R/Sits.lean)
  2  `k9_place_in_range`   the library's written list of places has an entry at that number: the
     place of the sub-protocol there. So the hypothesis `hno` of 3 is not met for lack of an entry
  3  `playsS_k9_silent_at`   **`PlaysS` at that number**, under `hno`: no side of the prover's list
     stands at the place that the written list has at that number
  4  `playsS_k9_silent_of_at`   a control: the statement of `playsS_k9_silent`, by one call of 3. So
     3 is the stronger lemma

Limits.
  * "It plays" is not "it is accepted". `PlaysS` does not say that a side stands at a place, nor
    that the sub-protocol's step accepts what was played. A prover that sends nothing plays here.
  * Nothing is said on `ExchangeS` at these numbers.
  * At j = 4 and j = 6 the sub-protocol has no round. There `hno` may be more than is needed: this
    file does not try it without.
  * Nothing here shows that the invariant holds at any state of a run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K9Silent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The sub-protocol at the number -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

include h in
/-- At the number stands a sub-protocol without a round, or with the one round `k9Decl`. -/
theorem k9_block_at {l : Nat} (hl : l < 25) {j : Nat} (hj : j = 2 ∨ j = 4 ∨ j = 6) :
    ∃ blk, cF.blocksInOrder[14 * l + IM.nAt l + j]? = some blk ∧
      (blk.rounds = [] ∨ ∃ p, blk.rounds = [VerifiableInference.Desc.K9L.k9Decl p]) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, p, Qc, -, -, St⟩ := LPFK9.k09_sits h.scope h.reads O l hl
  have hlen : Lk.hear.length = IM.nAt l := St.hear.trans (IM.hear_len_at l)
  rcases hj with rfl | rfl | rfl
  · exact ⟨Lk.batchB, by rw [← hlen]; exact St.flat, Or.inr ⟨p, St.rounds⟩⟩
  · obtain ⟨b₃, -, hf, hr, -⟩ := St.equation
    exact ⟨b₃, by rw [← hlen]; exact hf, Or.inl hr⟩
  · obtain ⟨b₅, -, hf, hr, -⟩ := St.shut
    exact ⟨b₅, by rw [← hlen]; exact hf, Or.inl hr⟩

/-- The written list of places has an entry at the number: the place of the sub-protocol there. -/
theorem k9_place_in_range {l : Nat} (hl : l < 25) {j : Nat} (hj : j = 2 ∨ j = 4 ∨ j = 6) :
    ∃ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[
        14 * l + IM.nAt l + j]? = some blk ∧
      P5J.At.ps[14 * l + IM.nAt l + j]? = some blk.place := by
  obtain ⟨blk, hb, -⟩ := k9_block_at h hl hj
  exact ⟨blk, hb, head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb⟩

/-! ## 2 At the invariant -/

/-- **At one sub-protocol of the kind K9 a prover without a side at its place plays.** -/
theorem playsS_k9_silent_at {l : Nat} (hl : l < 25) {j : Nat} (hj : j = 2 ∨ j = 4 ∨ j = 6)
    (hno : ∀ p, P5J.At.ps[14 * l + IM.nAt l + j]? = some p → ∀ g ∈ H.first, g.place ≠ p) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + j) := by
  obtain ⟨blk, hb, hr⟩ := k9_block_at h hl hj
  have hn : (H.first.find? fun g => g.place == blk.place) = none :=
    List.find?_eq_none.2 fun g hg hp =>
      hno _ (head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb) g hg (eq_of_beq hp)
  have hsh : blk.shaped = true :=
    ((planOk_all (head_planOk h)).1 blk (List.mem_of_getElem? hb)).2
  rcases hr with hr | ⟨p, hr⟩
  · exact playsS_bare (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said hb
      (bare_of_quiet hr (shaped_parts hsh).1 hn)
  · exact playsS_bare (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said hb
      (bare_one_plain hr ⟨rfl, rfl, rfl⟩ hsh hn)

/-- A control: the statement of `playsS_k9_silent`, by one call. -/
theorem playsS_k9_silent_of_at (hno : ∀ g ∈ H.first, g.place.kind ≠ KindName.K9)
    {l : Nat} (hl : l < 25) {j : Nat} (hj : j = 2 ∨ j = 4 ∨ j = 6) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + IM.nAt l + j) :=
  playsS_k9_silent_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hl hj
    fun p hp g hg e => hno g hg (by rw [e]; exact k9_kind_at hl hj hp)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k9_block_at
#print axioms ProofFile.Honest.FirstThread.k9_place_in_range
#print axioms ProofFile.Honest.FirstThread.playsS_k9_silent_at
#print axioms ProofFile.Honest.FirstThread.playsS_k9_silent_of_at
