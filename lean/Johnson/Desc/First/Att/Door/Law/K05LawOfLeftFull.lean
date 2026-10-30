-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K05LawOfLeftFull.lean: kind K5: **THE JOIN, WITH THE TESTS ON THE WRITTEN LISTS PAID**: K05LawR from K5LeftFull's 20 fields (Door/Law/K5LeftFull.lean) at the composed meaning's closed constant.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Main names:
  K5LeftAllFull h L g q: there is a pick ℓ (K5Pick) at which K5LeftFull's fields hold, at the letters of K5LeftAll (Door/Law/K05LawOfLeft.lean). K5LeftAllFull.toAll: it gives K5LeftAll, g < 12.
  K05LeftFull: the list as one sentence, under all that K05LawR's own premises hold. k05Left_of_full: K05LeftFull → K05Left. **k05LawR_of_leftFull**: K05LeftFull → K05LawR.
IS IT EMPTY HERE? AN IMPLICATION. K05LawR IS NOT PROVED. NO MEMBER OF K5LeftAllFull IS SHOWN. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05LawOfLeft
import Johnson.Desc.First.Att.Door.Law.K5LeftFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub rchPub_hand)
open P5J (AtMg AtMgA AtMgR mgAtAll F0T TS Free fullLinks)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **WHAT IS LEFT OF THE KIND's LAW AT THE CLOSED CONSTANT, THE TESTS ON THE LISTS PAID.** -/
def K5LeftAllFull (L : Laid) (g : ℕ)
    (q : Piece (ckP .two) (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (ProofFile.InstPub × TS) ProofFile.Cl
      (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)) : Prop :=
  ∃ ℓ : K5Pick ProofFile.InstPub (P5J.CellsM numsFull) P5J.At.Tok numsFull.rows
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.𝔇.sent,
    K5LeftFull (mgAtAll h) mgBase h.𝔇.pubD h.𝔇.sent h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT L (P5J.At.d12 Zp L).M q (P5J.At.X Zp) g ℓ

variable {h}

theorem K5LeftAllFull.toAll {L : Laid} {g : ℕ}
    {q : Piece (ckP .two) (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (ProofFile.InstPub × TS) ProofFile.Cl
      (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)} (hg : g < 12) (H : K5LeftAllFull h L g q) : K5LeftAll h L g q := by
  obtain ⟨ℓ, Hl⟩ := H
  exact ⟨ℓ, Hl.toAt hg⟩

end

/-- **WHAT IS LEFT OF THE KIND's LAW, THE TESTS ON THE LISTS PAID, AS ONE SENTENCE.** -/
def K05LeftFull : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (_ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (_ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (_ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (L : Laid) (_ : P5J.At.laid? Zp = some L)
    (_ : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) L
      (P5J.At.d12 Zp L).M h.𝔇.sent),
    ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q → K5LeftAllFull h L g q

theorem k05Left_of_full (H : K05LeftFull) : K05Left :=
  fun Z D r Zp Np cF x h 𝔏 q₁ q₂ q₃ L hL A g hg q hq => K5LeftAllFull.toAll hg (H Z D r Zp Np cF x h 𝔏 q₁ q₂ q₃ L hL A g hg q hq)

/-- **THE JOIN, THE TESTS ON THE LISTS PAID.** -/
theorem k05LawR_of_leftFull (H : K05LeftFull) : K05LawR := k05LawR_of_left (k05Left_of_full H)

end H2K5.Door

#print axioms H2K5.Door.K5LeftAllFull.toAll
#print axioms H2K5.Door.k05Left_of_full
#print axioms H2K5.Door.k05LawR_of_leftFull
