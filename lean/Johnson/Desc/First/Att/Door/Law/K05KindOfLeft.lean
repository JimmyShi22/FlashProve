-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K05KindOfLeft.lean: kind K5: **THE KIND's SHARE AT THE CLOSED CONSTANT, IN ANOTHER FILE's OWN NAME (P5J.AtMgA.Kind, Johnson/P5J/RowsAtAll.lean), AT ONE HEAD, UNDER TWO NAMED CONDITIONS**: what is left
of the kind's law (K5LeftAll | K5LeftAllFull, Door/Law/K05LawOfLeft.lean | K05LawOfLeftFull.lean) and K5Along's seven facts along "reached" (Door/Law/K5Along.lean), at the condition beside the promise, h.toAtMg.rch (P5J.AtMg.rch, Johnson/P5J/FourAtMg.lean).
The forms …Laid: the listed seats L are no letter in front: the head's own test says that they are there (AtMgA.opts.laid with At.laid_some): THESE STAND OVER A Johnson/P5J/MgAtAll.lean WHOSE HEAD HAS THE FIELD opts ·
the forms with the tests on the written lists paid.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)

Typed by reading Johnson/P5J/MgAtAll.lean · OptsOk.lean · LettersAt2.lean · RowsAtAll.lean · RowsAtMg.lean.

Main names:
  **k05_kind_of_leftAt**: AT ONE HEAD h AND ONE 𝔏: the three flat lists' heads · K5Along h.toAtMg.rch L … · (∀ g < 12, ∀ q, the row's piece at 14 (2 g + 1) + 4 is q → K5LeftAll h L g q) → h.Kind 𝔏 .K5.
  k05_kind_of_leftFullAt: the like from K5LeftAllFull. k05_kind_of_leftLaid | k05_kind_of_leftFullLaid: the like with both conditions asked at whichever L the listed seats are.
  k05_kind_of_left: the like from the one sentence K05Left (over all heads).
THE CONDITIONS' SIZE [counted by a program over the sources]: K5LeftAll: a pick of 28 letters under ∃, and 27 fields; opened to their leaves 105: equations on the filling and the data 28 · on the description's piece 5 · on the plan
12 · on the table's numbers 2 · tests on the written lists 13 + 4 · at the composed meaning's closed data 9 · by the make 16 · on public data 8 · from an opening of the description 6 · over witnesses 1 · mathematics 1. K5LeftAllFull: 20
fields, 90 leaves (the seventeen on the lists paid; two equations more). K5Along: 7.
IS IT EMPTY HERE? IMPLICATIONS. NO MEMBER OF K5LeftAll OR OF K5Along AT h.toAtMg.rch IS SHOWN. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). THE KIND's LAW IS NOT PROVED.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05Kind
import Johnson.Desc.First.Att.Door.Law.K05LawOfLeftFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub)
open P5J (AtMg AtMgA mgAtAll F0T TS Free fullLinks)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **The kind's share AtMgA.Kind (RowsAtAll.lean), at one head, under two named conditions.** -/
theorem k05_kind_of_leftAt (L : Laid)
    (A : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent)
    (H : ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q → K5LeftAll h L g q) : h.Kind 𝔏 KindName.K5 :=
  (k05_kind_iff h 𝔏).1
    (k05_kindTiedR_of_left h 𝔏 (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) L A (fun _ _ q hq => hands_R1 h 𝔏 q₁ q₂ q₃ _ q hq) H)

/-- The like, the tests on the written lists paid. -/
theorem k05_kind_of_leftFullAt (L : Laid)
    (A : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent)
    (H : ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q → K5LeftAllFull h L g q) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_of_leftAt h 𝔏 q₁ q₂ q₃ L A fun g hg q hq => K5LeftAllFull.toAll hg (H g hg q hq)

/-- **With no letter for the listed seats in front**: the head's own test says that they are there. -/
theorem k05_kind_of_leftLaid
    (A : ∀ L, P5J.At.laid? Zp = some L →
      K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent)
    (H : ∀ L, P5J.At.laid? Zp = some L → ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q → K5LeftAll h L g q) :
    h.Kind 𝔏 KindName.K5 := by
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  exact k05_kind_of_leftAt h 𝔏 q₁ q₂ q₃ L (A L hL) (H L hL)

/-- The like, the tests on the written lists paid. -/
theorem k05_kind_of_leftFullLaid
    (A : ∀ L, P5J.At.laid? Zp = some L →
      K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent)
    (H : ∀ L, P5J.At.laid? Zp = some L → ∀ g, g < 12 → ∀ q, (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q → K5LeftAllFull h L g q) :
    h.Kind 𝔏 KindName.K5 := by
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  exact k05_kind_of_leftFullAt h 𝔏 q₁ q₂ q₃ L (A L hL) (H L hL)

/-- The like from the one sentence over all heads. -/
theorem k05_kind_of_left (H : K05Left)
    (A : ∀ L, P5J.At.laid? Zp = some L →
      K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent) :
    h.Kind 𝔏 KindName.K5 := by
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  exact k05_kind h 𝔏 (k05LawR_of_left H) q₁ q₂ q₃ L hL (A L hL)

end

end H2K5.Door

#print axioms H2K5.Door.k05_kind_of_leftAt
#print axioms H2K5.Door.k05_kind_of_leftFullAt
#print axioms H2K5.Door.k05_kind_of_leftLaid
#print axioms H2K5.Door.k05_kind_of_leftFullLaid
#print axioms H2K5.Door.k05_kind_of_left
