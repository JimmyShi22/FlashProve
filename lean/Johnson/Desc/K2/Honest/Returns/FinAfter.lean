-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FinAfter.lean: BEHIND THE LAST SEGMENT (the number 353 of the first
chain's flat list) THE DESCRIPTION's WAY OUT RETURNS BEHIND EVERY YES OF THE CODE SWITCH's OWN
DECISION: "F.0.quiet" (`finishBehindQ`), then the seat's two guards: wherever the state at which the
kind's decision stands bears no mark. So at a state reached at 353, where the quiet front returns,
the seated sub-protocol's decision says yes wherever the kind's own does. Statements with their
proofs: calls.

  `fin_leave_returns` a yes of the kind's own decision in the finish's dress at s₁, no mark at s₁ ⊢
                    ∃ t, (finishBehindQ u).bind (guards s₁) = ok t: the one test of "F.0.quiet",
                    that the fresh mask's number is among what the switch returned, holds by what
                    the switch returns
  `fin_after_reached` s reached at 353 · the quiet front returns s₁ at s · such a yes at s₁ ⊢ the
                    same
  `fin_seat_reached` THE TOP: at `fin_seat_decides`' own letters, its clauses beside: for every s
                    reached at 353 and every s₁ that the quiet front returns at s: at two rounds and
                    as many groups as the place reads trees: a yes of the kind's own at s₁ ⊢ ∃ t,
                    b.decide s rs gs = ok t

By, this folder's: `fin_seat_decides` (Returns/SeatAtArms.lean) · `guards_iff`
(Returns/SeatIff.lean). The library's: `finish_inv`, `FinIs`, `finFrontOf`
(Johnson/Top/H0/Tw/K2C/Closed.lean) · `switch_numbers`, `sentIds`
(Johnson/Top/H0/Tw/K2C/LinkNumbers.lean): what a yes of the switch itself returns · `others_get`
(Johnson/IMR/MaskNamed.lean): entry k of a sending's numbers, cut from a on · `switchNotices`
(Johnson/Top/H0/Tw/K2/Switch.lean) · `finishBehindQ_iff` (Johnson/Top/H0/Tw/K2C/Asks.lean) ·
`finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean) · `noMark_switch`
(Johnson/P1K2R/BookTight.lean) · `Except.bind_eq_ok` (Johnson/Top/H0/StepLaws/StepLaws.lean). NEAR
RELATIVES, NOT CALLED: `finishBehind_returns` (Returns/BehindOwn.lean): from the very premise that
is paid here · `door_finish` (Johnson/P1K2R/SitsMark.lean), `out_finish`
(Johnson/P1K2R/SitsDoor.lean), `finish_shape` (Johnson/P1K2R/HandsEnds.lean): laws on this way out,
each from its yes · `did_mask` (Johnson/Desc/K12/Law/SwTies.lean): the like of the mask's number at
another kind's text.

Limits. THAT THE QUIET FRONT RETURNS AT A REACHED STATE IS A PREMISE HERE (another house has typed
it: Johnson/AtFull/Shape/FinFrontReached.lean, in no sealed library: not imported, so that this file
stands over the sealed library and this folder alone). That the kind's own decision says yes is a
premise. At the decision, not at the step. 353 alone. "Reached" is: over the list of the wrapped
sub-protocols; that a state is reached is not said. The plan's own test is a premise of the top. At
the format's second hash function alone. This file's imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.SeatAtArms
import Johnson.Top.H0.Tw.K2C.LinkNumbers
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.IMR.MaskNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith finish_inv finFrontOf switch_numbers sentIds
  finishFrontQ finishBehindQ finishBehindQ_iff finishFrontQ_rest)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf guards)
open IM (k2P k2PlaceF)
open _root_.Tw.K2 (sendByL8 switchNotices)
open ProofFile (Cl)

/-- **"F.0.quiet" and the guards return behind every yes.** -/
theorem fin_leave_returns {p : P2} {s₁ u : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .finish)
    (hy : decideWith sendByL8 p s₁ rs gs = .ok u) (hu : s₁.failed = none) :
    ∃ t, (finishBehindQ u).bind (guards s₁) = .ok t := by
  obtain ⟨r₁, r₂, a, G, w, roots, -, k⟩ := finish_inv hp hy
  obtain ⟨-, -, -, -, ho⟩ := switch_numbers k.hSwitch
  have hN : (switchNotices (finFrontOf s₁ a G).T (finFrontOf s₁ a G).others).size =
      1 + (finFrontOf s₁ a G).T.kept.size + 1 := by
    unfold switchNotices finFrontOf
    simp
    omega
  have hm := Meaning.K2.others_get (finFrontOf s₁ a G).st.oracles.size
    (switchNotices (finFrontOf s₁ a G).T (finFrontOf s₁ a G).others).size
    (1 + (finFrontOf s₁ a G).T.kept.size) 0 (by omega)
  rw [← ho] at hm
  have hh : u.here = .fin { a with sw := w.out } := by rw [k.hOut]
  have hb := (finishBehindQ_iff u _).2 ⟨_, _, hh, hm, rfl⟩
  refine ⟨_, (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).2 ⟨_, hb,
    (guards_iff _ _ _).2 ⟨rfl, ?_, ?_⟩⟩⟩
  · show u.failed = none
    rw [k.hOut]
    exact hu
  · show (s₁.out.reply == u.out.reply) = true
    rw [k.hOut]
    exact beq_self_eq_true _

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **At a reached state, behind the quiet front's return.** -/
theorem fin_after_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) {s s₁ : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (hq : finishFrontQ s = .ok s₁)
    {p : P2} (hp : p.stands = .finish) {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {u : S}
    (hy : decideWith sendByL8 p s₁ rs gs = .ok u) :
    ∃ t, (finishBehindQ u).bind (guards s₁) = .ok t :=
  fin_leave_returns hp hy (((finishFrontQ_rest hq).2.2.2.1).trans
    (P1K2.noMark_switch hS hR O (Or.inr (Or.inr rfl)) hr))

/-- **So there the seated decision says yes wherever the kind's own does**: at the letters of
`fin_seat_decides`, with its clauses beside. -/
theorem fin_seat_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true) :
    ∃ (b : Block S Cl) (nm : String) (Pp : Prep) (n : Nums),
      c.blocksInOrder[353]? = some b ∧ prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp none = some n ∧
      (∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), rs.length = 2 →
        gs.length = n.read.length →
        (b.decide s rs gs = .ok t ↔ ∃ s₁ u, finishFrontQ s = .ok s₁ ∧
          decideWith sendByL8 (k2P Z k2PlaceF nm .finish n) s₁ rs gs = .ok u ∧
            (finishBehindQ u).bind (guards s₁) = .ok t)) ∧
      ∀ (z : ProofFile.InstPub) (s s₁ : S), Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s) →
        finishFrontQ s = .ok s₁ →
        ∀ (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (u : S), rs.length = 2 →
          gs.length = n.read.length →
          decideWith sendByL8 (k2P Z k2PlaceF nm .finish n) s₁ rs gs = .ok u →
          ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨b, nm, Pp, n, hb, hP, hn, hd⟩ := fin_seat_decides hS hR O hpl
  refine ⟨b, nm, Pp, n, hb, hP, hn, hd, fun z s s₁ hr hq rs gs u h2 hg hy => ?_⟩
  obtain ⟨t, ht⟩ := fin_after_reached hS hR O hr hq rfl hy
  exact ⟨t, (hd s t rs gs h2 hg).2 ⟨s₁, u, hq, hy, ht⟩⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_leave_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_after_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_seat_reached
