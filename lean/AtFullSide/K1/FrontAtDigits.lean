-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FrontAtDigits.lean: under the head the digits' filling reads no challenge from the rounds in front of
K1's job "digits" on; so the closed Script of the first chain lays the digits' filling at every link WITH NO
HYPOTHESIS LEFT BUT THE HEAD AND THE MAKER's RETURN.

  1  frontOkW   a closed fact, by evaluation in Lean's kernel: at each written seat of "BZ": the rounds that the
     seat counts in front of its sending, and the number of its link's round "RNG" plus one, are at most the
     written rows' rounds in front of member K1.noL l true
  2  front_at_digits   digitsSentence_first's hypothesis hFront
  3  digitsSentence_paid   THE END: ScriptLaysTheFillingAtTheLink at firstScriptAt, the filling digitsFill and the
     seats of "BZ", at every l below 25, every Vd and N

By: roundsTo_at_head (Johnson/HonestTrace/U3Fit/Slice.lean) · seatsBZ_at_head
(Honest/K2/Law/DigitsLightAtHead.lean) · entries_at_head, roundNumbers_entries
(Honest/K2/Law/PlacesWritten.lean).

Limits. The head h and the return hA are hypotheses. All limits of DigitsAtFirstScript.lean but hFront stand.
This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.DigitsAtFirstScript
import Johnson.HonestTrace.U3Fit.Slice

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (pairOf heardOf)
open OnBytes.HonestTrace.U3.Fit (rowsBeforeW roundsTo_at_head)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2.Law (seatsBZW entryNumbers)

/-- The written numbers of the rounds "RNG". -/
def rngW : List Nat := entryNumbers P5T.esFull.1 "RNG"

set_option maxRecDepth 1000000 in
/-- **At each written seat of "BZ" the two counts reach no further than the rounds in front of the job.** Two
controls: each of the 25 links has its round "RNG"; that round's number plus one IS the count in front, so
one round less would not do. -/
theorem frontOkW :
    (seatsBZW.all fun s =>
      decide (s.heard ≤ rowsBeforeW (K1.noL s.seg true)) &&
        (rngW[s.seg]?).all fun n => decide (n + 1 ≤ rowsBeforeW (K1.noL s.seg true))) = true ∧
      (seatsBZW.all fun s => (rngW[s.seg]?).any fun n =>
        decide (n + 1 = rowsBeforeW (K1.noL s.seg true))) = true := by
  decide +kernel

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD THE DIGITS' FILLING READS NO CHALLENGE FROM THE ROUNDS IN FRONT OF THE JOB ON.** -/
theorem front_at_digits (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {l : Nat} (address : MsgAddr) (message : Nat)
    (hp : pairOf (OnBytes.HonestTrace.seatsOf A.Z A.G "BZ") address = some (l, message)) :
    (digitsFill A.Z A.G (K3.matsOwn A.G.W)).heardAt address ≤ 0 + roundsTo cF.blocksInOrder (K1.noL l true) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hB : OnBytes.HonestTrace.seatsOf A.Z A.G "BZ" = seatsBZW := by
    rw [eG]; exact K2.Law.seatsBZ_at_head h O
  have hR : K2.roundNumbers A.Z.D.1 "RNG" = rngW := by
    rw [K2.Law.roundNumbers_entries, K2.Law.entries_at_head h.toAtMg O]
    rfl
  have hp' := hp
  unfold pairOf at hp'
  obtain ⟨s, hs, e⟩ := Option.map_eq_some_iff.1 hp'
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  have hmem : s ∈ OnBytes.HonestTrace.seatsOf A.Z A.G "BZ" := by
    have hs' := hs
    unfold OnBytes.HonestTrace.seatAt at hs'
    exact List.mem_of_find?_eq_some hs'
  have hok := List.all_eq_true.1 frontOkW.1 s (hB ▸ hmem)
  rw [Bool.and_eq_true, decide_eq_true_eq, e1] at hok
  rw [Nat.zero_add, roundsTo_at_head h]
  show max (heardOf (OnBytes.HonestTrace.seatsOf A.Z A.G "BZ") address)
    (match (K8.bearsZz A.G.first.layout (pairOf (OnBytes.HonestTrace.seatsOf A.Z A.G "BZ"))
        address).bind fun y => (K2.roundNumbers A.Z.D.1 "RNG")[y.1]? with
      | some n => n + 1
      | none => 0) ≤ _
  refine Nat.max_le.2 ⟨?_, ?_⟩
  · unfold heardOf
    rw [hs]
    exact hok.1
  · unfold K8.bearsZz
    rw [hp, hR]
    by_cases hz : ((A.G.first.layout.link.getD (l, message).1 []).any fun y =>
        y.name == "ZZ" && y.message == (l, message).2) = true
    · rw [Option.filter_some, if_pos hz, Option.bind_some]
      have q := hok.2
      revert q
      dsimp only
      generalize rngW[l]? = o
      intro q
      cases o with
      | none => exact Nat.zero_le _
      | some n => exact of_decide_eq_true q
    · rw [Option.filter_some, if_neg hz]
      exact Nat.zero_le _

/-- **THE CLOSED SCRIPT LAYS THE DIGITS' FILLING AT EVERY LINK, THROUGH THE TOTAL CALL.** Under the head and the
maker's return alone; at every Vd and N. -/
theorem digitsSentence_paid (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) {l : Nat} (hl : l < 25) :
    K3.Term.ScriptLaysTheFillingAtTheLink A.Z (firstScriptAt I S Op A cF) Vd N (readersB I A.Z)
      (digitsFill A.Z A.G (K3.matsOwn A.G.W)) (pairOf (OnBytes.HonestTrace.seatsOf A.Z A.G "BZ")) l :=
  digitsSentence_first h hA Vd N hl fun address message hp => front_at_digits h hA address message hp

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.frontOkW
#print axioms ProofFile.Honest.K1.front_at_digits
#print axioms ProofFile.Honest.K1.digitsSentence_paid
