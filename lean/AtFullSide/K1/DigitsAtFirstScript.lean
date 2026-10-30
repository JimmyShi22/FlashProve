-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/DigitsAtFirstScript.lean: the closed Script of the first chain (firstScriptAt,
AtFullSide/K1/FirstScript.lean) lays the digits' filling at every link: the lookups' sentence
ScriptLaysTheFillingAtTheLink (Honest/K3/Term/DigitArraysFromTheDigitsFilling.lean) at the filling digitsFill
and the seats of the array "BZ", THROUGH THE TOTAL CALL RowData.at_.

  1  bzSeatsOkW   a closed fact at the written seats of "BZ", by evaluation in Lean's kernel: each stands at the
     address of K1's job "digits" of its link, and its message is of moment 2
  2  digitsSentence_first   THE END, at every l below 25, every Vd and N

By digitsSentenceFromOwnMessagesAtTheDigitsJob (Honest/K3/Term/LaterJobSendsTheFillingAtEveryList.lean), whose
hypotheses are paid here: the codes' lengths (lengthsW) · the book covers the job (joinFit_first's field
coins) · the seats stand at the job (bzSeatsOkW, seatsBZ_at_head) · the Script holds the job's text under the
plan's number (ownMsgs_later_num).

ONE HYPOTHESIS IS NOT PAID: hFront, on public data: the digits' filling reads no challenge from the rounds in
front of the job on: heardAt at a seat's address is at most roundsTo cF.blocksInOrder (K1.noL l true).

Limits. The head h and the return hA are hypotheses. Where the filling's test "ready" refuses, the total call's
answer means nothing: the Script holds it all the same. This file proves nothing about completeness, soundness
or hiding.
-/
import AtFullSide.K1.LaterAtPlanNumbers
import Johnson.Desc.ProofFile.Honest.K3.Term.LaterJobSendsTheFillingAtEveryList
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsLightAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (inSending pairOf)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2.Law (seatsBZW)

set_option maxRecDepth 1000000 in
/-- **Each written seat of "BZ" stands at the address of K1's job "digits" of its link, and its message is
of moment 2.** Two controls: there are 25 seats; none is of moment 1. -/
theorem bzSeatsOkW :
    (seatsBZW.all fun s =>
      decide (s.addr.sender = ⟨⟨1, some s.seg, IM.k1Ix s.seg true + 1, .K1⟩, 0⟩) &&
        momentIs s 2) = true ∧
      seatsBZW.length = 25 ∧ (seatsBZW.any fun s => momentIs s 1) = false := by
  decide +kernel

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- What a seat of "BZ" at an address says, under the head. -/
theorem bzSeat_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {address : MsgAddr} {l message : Nat}
    (hp : pairOf (OnBytes.HonestTrace.seatsOf A.Z A.G "BZ") address = some (l, message)) :
    ∃ s, OnBytes.HonestTrace.seatAt (OnBytes.HonestTrace.seatsOf A.Z A.G "BZ") address = some s ∧
      address.sender = ⟨⟨1, some l, IM.k1Ix l true + 1, .K1⟩, 0⟩ ∧ momentIs s 2 = true ∧
      inSending (A.G.first.shape.link.getD l default) message = some (2, address.msg) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hB : OnBytes.HonestTrace.seatsOf A.Z A.G "BZ" = seatsBZW := by
    rw [eG]; exact K2.Law.seatsBZ_at_head h O
  unfold pairOf at hp
  obtain ⟨s, hs, e⟩ := Option.map_eq_some_iff.1 hp
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  have hs' := hs
  unfold OnBytes.HonestTrace.seatAt at hs'
  have hmem := List.mem_of_find?_eq_some hs'
  have hadr : s.addr = address := by
    have q := List.find?_some hs'
    exact beq_iff_eq.1 q
  have hok := List.all_eq_true.1 bzSeatsOkW.1 s (hB ▸ hmem)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨sps, seg, hso⟩ := seats_text hmem
  obtain ⟨M, f1, -, -, -, f5, f6, -⟩ := seat_text hso
  have hM : M.moment = 2 := by
    have q := hok.2
    unfold momentIs at q
    rw [f6] at q
    exact beq_iff_eq.1 q
  refine ⟨s, hs, ?_, hok.2, ?_⟩
  · rw [← hadr, hok.1, e1]
  · rw [← e1, f1, ← f5, ← e2, f6, hM, hadr]

/-- hFront IS A HYPOTHESIS, PAID NOWHERE. **THE CLOSED SCRIPT LAYS THE DIGITS' FILLING AT EVERY LINK, THROUGH
THE TOTAL CALL.** At every Vd and N. -/
theorem digitsSentence_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) {l : Nat} (hl : l < 25)
    (hFront : ∀ address message,
      pairOf (OnBytes.HonestTrace.seatsOf A.Z A.G "BZ") address = some (l, message) →
      (digitsFill A.Z A.G (K3.matsOwn A.G.W)).heardAt address ≤ 0 + roundsTo cF.blocksInOrder (K1.noL l true)) :
    K3.Term.ScriptLaysTheFillingAtTheLink A.Z (firstScriptAt I S Op A cF) Vd N (readersB I A.Z)
      (digitsFill A.Z A.G (K3.matsOwn A.G.W)) (pairOf (OnBytes.HonestTrace.seatsOf A.Z A.G "BZ")) l := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hlen : A.G.first.codes.lengthsOk = true := by
    have cG : A.G.first.codes = proofSizedFull.codes := by
      rw [eG, O.first]
      exact (H2K5.Door.made_row_gives (H2K5.Door.pins_at_head h.toAtMg).1).1.1
    rw [cG]; exact lengthsW
  have hC := (joinFit_first h hA).coins (K1.noL l true, jobLaterAt S A.Z A.G l true)
    (mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inr ⟨l, hl, true, rfl⟩))))
  have hne : (⟨⟨1, some l, IM.k1Ix l true + 1, .K1⟩, 0⟩ : Addr) ≠ firstAddr := by
    intro e
    have e' : IM.k1Ix l true + 1 = 1 := congrArg (fun a : Addr => a.place.piece) e
    have e3 : 3 ≤ IM.k1Ix l true := by
      unfold IM.k1Ix
      exact Nat.le_trans (by decide) (Nat.le_add_right _ _)
    omega
  refine K3.Term.digitsSentenceFromOwnMessagesAtTheDigitsJob A.Z A.G (firstScriptAt I S Op A cF) Vd N
    (readersB I A.Z) l (IM.k1Ix l true + 1)
    (lotNo OnBytes.secondHashFunction A.Z ⟨1, some l, IM.k1Ix l true + 1, .K1⟩)
    (0 + roundsTo cF.blocksInOrder (K1.noL l true)) S () hlen ?_ ?_ hFront ?_
  · unfold bookCovers
    have hC' : dueAt (A.B.rowsOf 0) ⟨⟨1, some l, IM.k1Ix l true + 1, .K1⟩, 0⟩ =
        dueR (jobLaterAt S A.Z A.G l true).P (jobLaterAt S A.Z A.G l true).ride := hC
    rw [hC']
    exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
  · intro address message hp
    obtain ⟨s, hs, g1, g2, -⟩ := bzSeat_at_base h hA hp
    refine ⟨g1, by rw [g1]; exact hne, fun s' hs' => ?_⟩
    rw [← Option.some.inj (hs.symm.trans hs')]
    exact g2
  · intro address message hp
    obtain ⟨s, -, -, -, g3⟩ := bzSeat_at_base h hA hp
    exact ownMsgs_later_num h hA Vd N hl true g3

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.bzSeatsOkW
#print axioms ProofFile.Honest.K1.bzSeat_at_base
#print axioms ProofFile.Honest.K1.digitsSentence_first
