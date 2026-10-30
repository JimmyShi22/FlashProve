-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/LaysAtSwitchesPaid.lean: the first chain's Script firstScriptAt at the base prover: the form LaysFilling
(Honest/K5/Law/LaysFilling.lean) at the segments 1 to 24, with the three hypotheses of laysFilling_switches
(LaysAtSwitches.lean) paid.

  1  lent_at_return      at the maker's own book each code switch's part is lent its coins, at every coin
  2  closing_at_return   the public test closingOk passes at each code switch's place
  3  public_at_return    the lot's public test publicOk passes at each place, at an instance that passes okStart
  4  laysFilling_switches_paid   LaysFilling at l = 1..24, at every N, at inputs that meet ReadyInput

All by calls. lent_at_return: handed_at_book (AtFullSide/K2/HandedAtTheBook.lean), atPure_book_at_head
(Honest/K14/AtPureBookAtHead.lean), sends_in_scope (Johnson/Goal/Numbers/MadeInScope.lean). closing_at_return:
closing_at_head (Honest/K2/Law/ClosingAtHead.lean). public_at_return: publicOk_of_reads
(Honest/K2/Law/PublicOkOfReads.lean), readsLight_of_att (Johnson/HonestTrace/U3Fit/ReadsDebt3.lean),
att_returns_at_open (Honest/K5/Law/AttValsAtHead.lean).

Limits.
  * The head h and the return hA are hypotheses. At Sz.ref alone. The full size; the format's second hash function.
  * lent_at_return says that coins are lent, not which, nor whose (HandedAtTheBook.lean's own limit).
  * LaysFilling speaks of the Script's messages at inputs that meet Vd. Here Vd is ReadyInput, or any condition
    that gives okStart at the input's instance.
  * closing_at_head is Honest/K2/Law/ClosingAtHead.lean's. Another file of that name lies under Honest/K12/AtFile.
  * Closed facts by Lean's kernel lie beneath.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.LaysAtSwitches
import AtFullSide.K1.LaysAtEveryList
import AtFullSide.K2.HandedAtTheBook
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicOkOfReads
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.HonestTrace.U3Fit.ReadsDebt3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At the maker's own book each code switch's part is lent its coins.** General in the filling. -/
theorem lent_at_return {Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hB := K14.atPure_book_at_head h hA
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1] at hB
  intro p hp k
  rw [eG] at hp
  exact AtFullSide.K2.handed_at_book h O hB hp k

/-- **The public test closingOk passes at each code switch's place.** General in the filling. -/
theorem closing_at_return {Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [eG]
  exact K2.Law.closing_at_head h.toAtMg O

/-- **The lot's public test passes at each place, at an instance that passes okStart.** -/
theorem public_at_return {Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction A.Z Np cF).okStart ξ = true) :
    ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout p
        ((K2.segmentsOf A.Z A.G).take p.link) ξ = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [eG]
  exact K2.Law.publicOk_of_reads h O (OnBytes.HonestTrace.U3.Fit.readsLight_of_att h O hx
    (OnBytes.HonestTrace.U3.Att.att_returns_at_open h O))

/-- **LaysFilling at the segments 1 to 24, with nothing left but the head and the return.** hV: the condition on
inputs gives okStart at the input's instance; ReadyInput does. -/
theorem laysFilling_switches_paid (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (Vd : LocB W₀ → Prop)
    (hV : ∀ w, Vd w → (F0T OnBytes.secondHashFunction A.Z Np cF).okStart w.x = true) (N : Nat)
    {l : Nat} (h1 : 1 ≤ l) (h25 : l < 25) :
    K5.LaysFilling h (firstScriptAt I Sz.ref Op A cF) Vd N (readersB I A.Z) (K2.switchSeat A.Z A.G)
      (fun _ => 0) l :=
  laysFilling_switches h hA Vd N (lent_at_return h hA) (closing_at_return h hA)
    (fun p hp w hw => public_at_return h hA (hV w hw) p hp) h1 h25

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lent_at_return
#print axioms ProofFile.Honest.K1.closing_at_return
#print axioms ProofFile.Honest.K1.public_at_return
#print axioms ProofFile.Honest.K1.laysFilling_switches_paid
