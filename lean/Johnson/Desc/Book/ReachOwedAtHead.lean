--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Book/ReachOwedAtHead.lean: the five facts on every reached last state of the first
chain, in the sentence in which the shared table's constant owes them (`Sh.ReachOwed`,
Johnson/Desc/K14/Law/SharedConstReachOwed.lean), FROM THE ONE HEAD (`P5J.AtMg`,
Johnson/P5J/AtMg.lean) at the concrete older hash, with no test on written values in front of the
statement. Three theorems. Joinings.

  `codes_at_head`: off the head: the first chain's codes as read back are the codes as sized
    (`P2R0.codes_sized`, `P2R0.front2_at_planOk`, Johnson/P2R0R/SizedIsRead.lean).
  `reachOwed_at_head`: from h : `AtMg OnBytes.secondHashFunction Z D r Zp Np cF` and two premises:
    `Sh.ReachOwed OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF L`.
    OFF THE HEAD: the scope (h.scope) · an opening (h.laid.opened) · the test on the list of rounds
    (h.laid.planOk) · the codes (`codes_at_head`).
    THE TWO THAT STAY, BY NAME:
      hB: `K12.Door.sendsAreB`, a closed test on the list of rounds, at every opening
      hL: the list of places and shapes can be laid at the first chain's codes: it names L
  `reachOwed_at_listed`: hL in the composed meaning's constant's letters:
    `P5J.At.laid? Zp = some L`.
    (At `P5J.AtMgR` that is the field listed.)
By `Meaning.K2.five_at_end_planOk` (Johnson/IMR/EndFivePaid.lean) and `Sh.reachOwed_of_five`
(Johnson/Desc/K14/Law/SharedConstReachAt.lean).

Limits. The premises that stay are shown nowhere here. hB speaks of every opening: it can be met
only by a lemma of that form. WHERE hB IS MET BY A LEMMA UNDER A TEST ON WRITTEN VALUES, THAT
TEST STANDS IN FRONT AGAIN: it has then moved into hB. At `OnBytes.secondHashFunction` alone. No example.
Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K14.Law.SharedConstReachAt
import Johnson.IMR.EndFivePaid
import Johnson.P5J.AtMg
import Johnson.P5J.LettersAt2
import Johnson.P2R0R.SizedIsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open _root_.Desc.K14.Law (secondAt)
open _root_.Desc.K14.Law.Sh (ReachOwed reachOwed_of_five)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl}

/-- Off the head: the first chain's codes as read back are the codes as sized. -/
theorem codes_at_head {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF) :
    Zp.p.chains.proof.first.codes = Zp.p.chains.made.sized.proof.codes :=
  P2R0.codes_sized h.laid.pub
    (P2R0.front2_at_planOk o ProofFile.pureRoad.links Zp Zp.p.chains (_root_.Desc.K14.beforePointOf Np)
      (fun _ => K12.Seat.tests Np) [] K12.Seat.last
      (VerifiableInference.OnPublicFiles.OkD.AtC.beside Zp.p.X Zp.p.chains) (secondAt Zp Np) (fun s => s)
      (ProofFile.startS Zp) cF h.laid.planOk)

/-- **The five facts, in the constant's sentence, from the one head.** -/
theorem reachOwed_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true)
    {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    ReachOwed OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF L := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact reachOwed_of_five _ Zp Np _ cF L
    (Meaning.K2.five_at_end_planOk h.scope O h.laid.planOk (hB Bs base _ _ O) hL)
    (codes_at_head h).symm

/-- **The list in the composed meaning's constant's letters.** -/
theorem reachOwed_at_listed (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true)
    {L : K12.Door.Laid} (hL : P5J.At.laid? Zp = some L) :
    ReachOwed OnBytes.secondHashFunction Zp Np (secondAt Zp Np) cF L :=
  reachOwed_at_head h hB hL

end VerifiableInference.Desc.Book

#print axioms VerifiableInference.Desc.Book.codes_at_head
#print axioms VerifiableInference.Desc.Book.reachOwed_at_head
#print axioms VerifiableInference.Desc.Book.reachOwed_at_listed
