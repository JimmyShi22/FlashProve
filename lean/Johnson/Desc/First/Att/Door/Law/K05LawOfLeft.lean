-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K05LawOfLeft.lean: kind K5: **THE JOIN: THE KIND's LAW IN THE COUNTED FORM (K05LawR, Door/Law/K05LawR.lean) FROM WHAT IS LEFT.** The three pieces of the road, called together for the first time:
(i) the law's end is twelve ties (k05_of_places) · (ii) the tie at one place from K5Owes and its fellows · (iii) what the bridge spends of "reached" from K5Along's seven ((ii) and (iii): k5_tiedAtR_left, Door/Law/K5LeftAt.lean);
HandsOn by hands_R1, the idle extractor by ex_k5.


Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Main names:
  K5LeftAll h L g q: **THE LIST OF WHAT IS LEFT, AT THE COMPOSED MEANING's CLOSED CONSTANT**: there is a pick ℓ of the 28 letters (K5Pick) at which K5LeftAt's 27 fields hold, at Mg := mgAtAll h · Mg0 := mgBase · D := h.𝔇.pubD ·
    Dn := h.𝔇.sent · G0 | arr | smp | ms | decT := h.𝔇's own · Ld := L · Ms := (At.d12 Zp L).M · Wv := At.X Zp. THE PICK STANDS UNDER ∃: IT IS THE PAYER's: a letter closed here at a wrong term would empty the list.
  k05_kindTiedR_of_left: at ANY condition Rch beside the promise: K5LeftAll at the twelve pieces, K5Along at Rch and HandsOn at the twelve numbers give the kind's share KindTiedR … Rch … .K5.
  K05Left: the list as ONE SENTENCE: under ALL that K05LawR's own premises hold (the head · the three flat lists' heads · the listed seats are L · K5Along at the picked condition): ∀ g < 12, ∀ q, the row's piece at
    14 (2 g + 1) + 4 is q → K5LeftAll h L g q. (A first typing left the three flat lists' heads out: at an 𝔏 whose sub-protocols are not the description's the six fields on the piece have no payer: it would have been hollow.)
  **k05LawR_of_left**: K05Left → K05LawR.
IS IT EMPTY HERE? AN IMPLICATION. K05LawR IS NOT PROVED. NO MEMBER OF K5LeftAll IS SHOWN; A MEMBER OF THE HEAD AtMgA IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). Where the head has no member the premise is free and the end says nothing.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05LawR
import Johnson.Desc.First.Att.Door.Law.K5LeftAt

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

/-- **WHAT IS LEFT OF THE KIND's LAW AT THE CLOSED CONSTANT**, at the listed seats L, group g and the description's piece q. -/
def K5LeftAll (L : Laid) (g : ℕ)
    (q : Piece (ckP .two) (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (ProofFile.InstPub × TS) ProofFile.Cl
      (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)) : Prop :=
  ∃ ℓ : K5Pick ProofFile.InstPub (P5J.CellsM numsFull) P5J.At.Tok numsFull.rows
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.𝔇.sent,
    K5LeftAt (mgAtAll h) mgBase h.𝔇.pubD h.𝔇.sent h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT L (P5J.At.d12 Zp L).M q (P5J.At.X Zp) g ℓ

variable (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (Rch : ℕ → (ProofFile.InstPub × TS) × (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str → Prop)

/-- **The kind's share at any condition beside the promise, from what is left.** -/
theorem k05_kindTiedR_of_left (L : Laid) (A : K5Along Rch L (P5J.At.d12 Zp L).M h.𝔇.sent)
    (hs : ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q → HandsOn Rch (14 * (2 * g + 1) + 4) q)
    (H : ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q → K5LeftAll h L g q) :
    KindTiedR (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps Rch (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏) KindName.K5 := by
  haveI : Nonempty ProofFile.InstPub := ⟨⟨ByteArray.empty, default⟩⟩
  refine k05_of_places h 𝔏 Rch fun g hg q hq => ?_
  obtain ⟨ℓ, Hl⟩ := H g hg q hq
  exact k5_tiedAtR_left Hl hg Rch A (h.toAtMg.ex 𝔏 (14 * (2 * g + 1) + 4)) (ex_k5 h 𝔏 hg) (hs g hg q hq)

end

/-- **WHAT IS LEFT OF THE KIND's LAW, AS ONE SENTENCE**: under ALL that K05LawR's own premises hold (the head; the three flat lists' heads; the listed seats; K5Along at the picked condition), at each of the
twelve pieces of the kind. -/
def K05Left : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (_ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (_ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (_ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (L : Laid) (_ : P5J.At.laid? Zp = some L)
    (_ : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) L
      (P5J.At.d12 Zp L).M h.𝔇.sent),
    ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q → K5LeftAll h L g q

/-- **THE JOIN: THE KIND's LAW IN THE COUNTED FORM, FROM WHAT IS LEFT.** -/
theorem k05LawR_of_left (H : K05Left) : K05LawR :=
  fun Z D r Zp Np cF x h 𝔏 q₁ q₂ q₃ L hL A =>
    k05_kindTiedR_of_left h 𝔏 _ L A (fun _ _ q hq => hands_R1 h 𝔏 q₁ q₂ q₃ _ q hq) (H Z D r Zp Np cF x h 𝔏 q₁ q₂ q₃ L hL A)

end H2K5.Door

#print axioms H2K5.Door.k05_kindTiedR_of_left
#print axioms H2K5.Door.k05LawR_of_left
