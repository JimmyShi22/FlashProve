-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/AtHead.lean: the closing of a segment (K10): four of the tops of
Wipe/SeatWipe.lean under the library's head (`P5J.AtMg` at the older hash, Johnson/P5J/AtMg.lean) in place of the scope
and `IM.Open`; `Tied` stays a premise of these four, and a fifth lemma has it under the head. Lemmas; no definition.

  `tied_at_head`      under the head, at each link l < 25: a place's numbers Q and a block b of the head's own chain cF
                     with `Tied cF Zp l p Q b` (Honest/K10/SimLot.lean): the head's fields scope and reads, `IM.Open`
                     out of its field laid (`LaidAt.opened`, Johnson/P5J/LaidOpens.lean), then `tied_at_scope`
  `keeps_at_head`, `front_at_head`   `keeps_at_closing` and `front_is_take` there
  **`stAtZero_at_head`**   `stAtZero_of_fold` there: where the description's fold over cF's first 14 l + 12 members (14
                     l + 14 at the last link) returns y at the rounds seen and at some columns, `stAtZero` at cF's flat
                     list returns the statement of y's state, wiped, and that state's live group's number
  **`closeAsk_at_head`**   `closeAsk_at_closing` there, from the same premise on the fold

Each is stated at any Q and b that `Tied` names at the link; `tied_at_head` has such a pair.

Limits. start, x and J are letters, and J's own place is not tied to Q. That the fold returns is a premise. Whether the
head can be had at any files is no theorem here. Nothing on whether `closeAsk` returns. No property of the protocol is
claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.SeatWipe
import Johnson.P5J.AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl}

/-- **Under the head the closing's block stands in the head's own chain**, at each link. -/
theorem tied_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied cF Zp l p Q b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact tied_at_scope h.scope h.reads O l hl

/-- Under the head every member of the chain in front of a link's closing keeps the wiping. -/
theorem keeps_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b) :
    ∀ b' ∈ cF.blocksInOrder.takeWhile (·.place != closePlace Q), Keeps wipeS 0 b' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact keeps_at_closing h.scope h.reads O hl T

/-- Under the head the members in front of a link's closing are the chain's first 14 l + 12 (14 l + 14 at the last
link).
-/
theorem front_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat}
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b) :
    cF.blocksInOrder.takeWhile (·.place != closePlace Q) = cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact front_is_take h.scope h.reads O T

/-- **The filler's value under the head**, from the fold over the chain's first members. -/
theorem stAtZero_at_head {Xi : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b)
    (start : Xi → S) (x : Xi) (seen : Seen) (front : List Fmt.Drawn) {cols : List OpenedColumn}
    {y : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start x) seen.rounds cols = .ok y) :
    stAtZero cF.blocksInOrder start x Q seen front = .ok (wipeSt y.1.st, y.1.live.frame.group) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact stAtZero_of_fold h.scope h.reads O hl T start x seen front hf

/-- **What the closing hands to the fold, under the head**, from the same premise. -/
theorem closeAsk_at_head {W Xi : Type} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied cF Zp l p Q b)
    (J : CloseJob W) (start : Xi → S) (xi : W → Xi) (w : W) (seen : Seen) (front : List Fmt.Drawn) (d : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → OnBytes.E) (ca : CsAll (closeCarries J.pub)) {cols : List OpenedColumn}
    {y : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start (xi w)) seen.rounds cols =
      .ok y) :
    closeAsk { J with stAt := fun w' s f => stAtZero cF.blocksInOrder start (xi w') Q s f } w seen front d u ca =
      closeAsk { J with stAt := fun _ _ _ => .ok (y.1.st, y.1.live.frame.group) } w seen front d u ca := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine closeAsk_at_closing h.scope h.reads O hl T J start xi w seen front d u ca (cols := cols) ?_
  have ha : cF.blocksInOrder.any (·.place == closePlace Q) = true := by
    obtain ⟨-, -, hb, -, -, hp, -⟩ := T
    refine List.any_eq_true.2 ⟨b, List.mem_of_getElem? hb, ?_⟩
    rw [hp]
    exact beq_self_eq_true _
  unfold frontState
  rw [ha, front_is_take h.scope h.reads O T, hf]
  rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.tied_at_head
#print axioms ProofFile.Honest.K10.keeps_at_head
#print axioms ProofFile.Honest.K10.front_at_head
#print axioms ProofFile.Honest.K10.stAtZero_at_head
#print axioms ProofFile.Honest.K10.closeAsk_at_head
