-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/FrontTiesReached.lean: THE PUBLIC TIES AT A CODE SWITCH's FRONT, AT A
REACHED STATE, IN THE GOALS' SCOPE: AT THE FRONT THAT THE SWITCH's BLOCK ITSELF TAKES OFF THE STATE
(`K2.frontAt p s = some fx`, Johnson/Top/H0/K2Hears/Long.lean), at all three sorts of the kind's
places. One bundle of public clauses; statements with their proofs: calls.

  `LayIs.of_oracles` `LayIs` (Returns/LayoutReached.lean) reads of the statement its oracle messages
                    alone
  `FrontTies Z fx` THE BUNDLE: there is a group G with `LayIs fx.st G fx.f.rows` · the carried rows'
                    main code's message length is a power of two · the front's codes are the public
                    part's · the carried rows' two codes' numbers are the public shape's
  `link_frontTies` at a state reached in front of the switch into a later group (the places 14 (m +
                    1) + 2, m < 23), where the place stands at a segment's first place
  `head_frontTies` with `fin_frontTies`: the like at the output head's place (339) and behind the
                    last segment (353, behind its quiet step in front)

What it is for. The sentence `carryExact` (Johnson/Desc/K2/Honest/Carry/Exact.lean) speaks at this
very front. The first clause is, field by field, the seven public premises of the law that leads
from the claim at `leftAt` of the words to the claim at what an honest fold leaves of rows in full
(`claimTrue_of_foldEnd`, Carry/LayoutSame.lean). The second is the one premise of a law that the
claim is the same at what a fold left and at that, kept in arrays (in a file that is not in this
library). This file imports none of the three. The last three are one side of the ties between the
front and an honest prover's public letters.

By: `layout_of_close`, `head_layout_reached`, `fin_layout_reached` (Returns/LayoutReached.lean) ·
`pow_of_close` (Returns/PowOfClose.lean) · the library's `link_closed_reached`
(Returns/ClosedReached.lean), `head_closed_reached`, `fin_closed_reached` (Returns/ClosedArms.lean)
· `front_pin_link`, `front_pin_head` (Johnson/IMR/FrontPin.lean), `front_pin_fin`
(Johnson/IMR/FinPin.lean): the last three clauses are theirs · `frontOf_iff`
(Johnson/Top/H0/Tw/K2C/DebtsState.lean) · `front_of_link`, `link_front`
(Johnson/Goal/Meaning/K2Share/FrontPlan.lean) · `pub_lengthsOk`
(Johnson/Second/K08/BlocksInOfLayout.lean) · `reach_raw`, `Reach.fold`
(Johnson/Top/H0/Walk/Reach.lean). NEAR, NOT CALLED: `FrontCore` (Returns/SentFront.lean): thirteen
clauses at a front, for the law that the kind's own decision says yes: no clause is shared to the
sign; the power of two follows from its `lengths` and `check`; at reached fronts the library pays it
under named tests on the public part, and here none is asked · `AtSwitch` with `atSwitch_reached`
(Johnson/AtFull/Shape/AtSwitchReached.lean): twelve clauses on THE STATE reached at 14 l + 2, l <
25, among them the matter of the last three here (the codes; the carried rows' two codes' numbers):
under the head's premise and no mark, over the chain's own sub-protocols, at the links' places
alone; nothing on a layout or a length · `noticesW_link`, `noticesW_head`, `noticesW_fin`
(Johnson/P1K2R/TieTwoPays.lean): the front's codes at the same states, with what the front
announces. A HOMONYM AVOIDED: `link_ties_reached` (Johnson/AtFull/Shape/LinkPlanNums.lean) is
another matter.

Limits. WHICH GROUP G IS, is not said. "Reached" is `Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z,
s)`: by the chain's sub-protocols in their wrapped form. NO PUBLIC FILES, OPENING AND STATE ARE
GIVEN HERE AT WHICH THE PREMISES OF THE THREE LAWS (in scope · the files read · the description
opened · the state reached · the front returned) HOLD TOGETHER: as far as this file goes, they could
hold of nothing. Nothing here speaks of a prover: that its letters are the public part's is not
treated; nor the challenges; nor the members; nor any entry of a row. The imports are heavy. Nothing
on any property.
-/
import Johnson.Desc.K2.Honest.Returns.LayoutReached
import Johnson.Desc.K2.Honest.Returns.PowOfClose
import Johnson.IMR.FrontPin
import Johnson.IMR.FinPin
import Johnson.Top.H0.Tw.K2C.DebtsState
import Johnson.Second.K08.BlocksInOfLayout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription Grows)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile (Cl)

/-- `LayIs` reads of the statement its oracle messages alone. -/
theorem LayIs.of_oracles {T T' : Statement} {G : Group} {old : SingleRows} (H : LayIs T G old)
    (h : T'.oracles = T.oracles) : LayIs T' G old := by
  have b : ∀ part : OnBytes.Part, Own.blockBits T' G part = Own.blockBits T G part := fun part => by
    unfold Own.blockBits Own.tableThere Statement.rowBits
    rw [h]
  have e : (Own.layoutOf T' G).k = (Own.layoutOf T G).k ∧
      (Own.layoutOf T' G).h = (Own.layoutOf T G).h ∧
      (Own.layoutOf T' G).mainFirst = (Own.layoutOf T G).mainFirst ∧
      (Own.layoutOf T' G).maskFirst = (Own.layoutOf T G).maskFirst := by
    unfold Own.layoutOf
    dsimp only
    rw [b .main, b .mask]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨H.members, H.kept, H.sizes, by rw [e.1]; exact H.k, by rw [e.2.1]; exact H.h,
    by rw [e.2.2.1]; exact H.mainFirst, by rw [e.2.2.2]; exact H.maskFirst⟩

/-- **The public ties at a switch's front.** Z: the public part. -/
structure FrontTies (Z : ProofFile.Pub) (fx : _root_.Tw.K2.Front) : Prop where
  lay : ∃ G : Group, LayIs fx.st G fx.f.rows
  pow : 2 ^ (fx.st.codes.base.getD fx.f.rows.code default).logEll =
    (fx.st.codes.base.getD fx.f.rows.code default).ell
  codes : fx.st.codes = Z.first.codes
  code : fx.f.rows.code = Z.first.shape.code
  maskCode : fx.f.rows.maskCode = Z.first.shape.maskCode

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **At a state reached in front of the switch into a later group.** -/
theorem link_frontTies (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) {p : K2.P2}
    (hq : p.stands = .link) {fx : _root_.Tw.K2.Front} (h : K2.frontAt p s = some fx) :
    FrontTies Z fx := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨a1, a2, -, -, -, a6, a7, a8, -, -⟩ :=
    Meaning.K2.front_pin_link hS hR O (l := m + 1) (by omega) (by omega) f hq h
  obtain ⟨-, c1, -, -⟩ := K2.link_front (K2.front_of_link hq h)
  obtain ⟨owed, f', S₀, es, rs, x, hx, hf, hg⟩ := link_closed_reached hS hR O h23 hr
  obtain ⟨G, H⟩ := layout_of_close hx hg
  have hrows : fx.f.rows = x.1.rows := by rw [a6, hf]
  refine ⟨⟨G, by rw [hrows]; exact H.of_oracles a2⟩, ?_, a1, a7, a8⟩
  rw [c1, hrows]
  exact pow_of_close hx hg (by rw [← c1, a1]; exact Second.K08.pub_lengthsOk O.pub)

/-- **At the output head's front.** -/
theorem head_frontTies (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {p : K2.P2}
    (hq : p.stands = .head) {fx : _root_.Tw.K2.Front} (h : K2.frontAt p s = some fx) :
    FrontTies Z fx := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨a1, -, -, -, -, a7, a8, -, -⟩ := Meaning.K2.front_pin_head hS hR O f hq h
  rcases K2.frontOf_iff.2 h with ⟨hp, -⟩ | ⟨-, a, G₀, here, -, rfl⟩ | ⟨hp, -⟩
  · rw [hq] at hp
    cases hp
  · obtain ⟨owed, f', S₀, es, rs, x, hx, hf, hg⟩ := head_closed_reached hS hR O hr here
    refine ⟨head_layout_reached hS hR O hr here G₀.target, ?_, a1, a7, a8⟩
    show 2 ^ (s.st.codes.base.getD a.fr.rows.code default).logEll =
      (s.st.codes.base.getD a.fr.rows.code default).ell
    rw [hf]
    exact pow_of_close hx hg
      (by rw [show s.st.codes = Z.first.codes from a1]; exact Second.K08.pub_lengthsOk O.pub)
  · rw [hq] at hp
    cases hp

/-- **At the front behind the last segment, behind its quiet step in front.** -/
theorem fin_frontTies (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : K2.finishFrontQ s = .ok t) {p : K2.P2} (hq : p.stands = .finish)
    {fx : _root_.Tw.K2.Front} (h : K2.frontAt p t = some fx) : FrontTies Z fx := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨a1, -, -, -, -, a7, a8, -⟩ := Meaning.K2.front_pin_fin hS hR O f he hq h
  rcases K2.frontOf_iff.2 h with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨-, a, G₀, here, -, rfl⟩
  · rw [hq] at hp
    cases hp
  · rw [hq] at hp
    cases hp
  · obtain ⟨owed, f', S₀, es, rs, x, hx, hf, hg⟩ := fin_closed_reached hS hR O hr he here
    refine ⟨fin_layout_reached hS hR O hr he here G₀, ?_, a1, a7, a8⟩
    show 2 ^ (t.st.codes.base.getD a.fr.rows.code default).logEll =
      (t.st.codes.base.getD a.fr.rows.code default).ell
    rw [hf]
    exact pow_of_close hx hg
      (by rw [show t.st.codes = Z.first.codes from a1]; exact Second.K08.pub_lengthsOk O.pub)

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.LayIs.of_oracles
#print axioms VerifiableInference.Desc.K2.Honest.Returns.FrontTies
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_frontTies
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_frontTies
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_frontTies
