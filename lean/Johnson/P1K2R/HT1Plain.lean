-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HT1Plain.lean: code switching (K2): THE BINDER hT1 OF K2AllOwes AT EACH OF THE
25 PLACES (Johnson/P1K2R/HT1Tight.lean) WITH NO FIELD OF FoldFacts IN FRONT: the field msgShapes is
paid by msgShapes_field (Johnson/IMR/SeatsField.lean).
  msgShapes_reached  the field msgShapes at «reached» itself, over any second component: from the
               head and the accept of the test sendsAreB
  hT1_link_plain · hT1_head_plain · hT1_fin_plain  the ends of hT1_link | hT1_head | hT1_fin, to the
               letter
WHAT STANDS IN FRONT, BY NAME. THE HEAD: hS · hR · O (at the public files' own layout file) · hF ·
hpl. THREE NAMED TESTS OR EQUATIONS ON THE PLAN: hy: madePinnedAt accepts · hcut: the chain's
sub-protocols have the written cut (the verifier's entry tests ask both, as madeRow and cutRow:
Johnson/Desc/Laid/ProofAsks.lean, tests 9 and 10) · hB: sendsAreB accepts at 358, at the sendings of
the written list of places (no entry test; from madeRow, F.planOk: Johnson/IMR/EndFiveMade.lean).
hRch: WHAT Rch HOLDS IS REACHED: ONE DIRECTION: the field is read at Reach itself, so nothing
need be led back into Rch. The place (hq · hrw · h0f) and the way in (hent) as in HT1Tight.lean.
WHAT msgShapes_field's OWN PREMISES ASK AT THESE LETTERS. Its hRch («what is reached is
the end of a fold over the first k sub-protocols from the start at the statement's own
public part»): paid here, by reach_raw and Reach.fold (Johnson/Top/H0/Walk/Reach.lean) ·
its hF: hpl · its hB: hB · hLd is asked by seatsCarried_field alone, not by this field.
LIMITS. Joins. No premise is shown met at a real value: no example. That hy, hcut and hB can be met
together with the head is shown by nobody. The full size alone. No probability; no soundness is
claimed.
-/
import Johnson.P1K2R.HT1Tight
import Johnson.IMR.SeatsField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.First.K2Hands (frontB2 placeFrame Tied)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.G (fxAt storedB)
open _root_.Tw.K2 (switchNotices)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Str : Type}

/-- **The field msgShapes at «reached» itself.** -/
theorem msgShapes_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true) :
    ∀ k (x : (ProofFile.InstPub × S) × Str), Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1 →
      x.1.2.failed = none →
      K12.Door.atFirstShapes (K12.Door.msgsOfChain Z.made.proof.1) x.1.2 = true :=
  IM.msgShapes_field hS hR O
    (fun k (x : (ProofFile.InstPub × S) × Str) => Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (fun x => x.1)
    (fun _ _ h => by
      obtain ⟨-, rs, cols, f⟩ := (reach_raw h).fold
      exact ⟨rs, cols, [], [], f⟩) hpl hB

variable {Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop}

/-- **hT1 AT THE SWITCH INTO GROUP m + 1, m < 23.** -/
theorem hT1_link_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {m : ℕ} (h23 : m < 23)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) {q : K2.P2}
    (hq : q.stands = .link) {r : SwRow} (hrw : tableFullLit[m]? = some r) {W : SwitchFrame}
    (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Str, Rch (14 * (m + 1) + 2) ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      frontB2 (fxAt r) W (m + 1) 0 (K2.n0At (m + 1)) (K2.oldsAt (m + 1)) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W (K2.n0At (m + 1)) (K2.oldsAt (m + 1))) fx = true ∧
        a.1.st.oracles = fx.st.oracles :=
  fun z a ha => hT1_link hS hR O hF hpl hy hcut (fun _ _ => Iff.rfl)
    (msgShapes_reached hS hR O hpl hB) h23 hent hq hrw h0f z a (hRch _ _ ha)

/-- **hT1 AT THE OUTPUT HEAD's SWITCH, INTO GROUP 24.** -/
theorem hT1_head_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) {q : K2.P2}
    (hq : q.stands = .head) {r : SwRow} (hrw : tableFullLit[23]? = some r) {W : SwitchFrame}
    (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Str, Rch 339 ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      frontB2 (fxAt r) W 24 0 (K2.n0At 24) (K2.oldsAt 24) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W (K2.n0At 24) (K2.oldsAt 24)) fx = true ∧
        a.1.st.oracles = fx.st.oracles :=
  fun z a ha => hT1_head hS hR O hF hpl hy hcut (fun _ _ => Iff.rfl)
    (msgShapes_reached hS hR O hpl hB) hent hq hrw h0f z a (hRch _ _ ha)

/-- **hT1 AT THE FINISH's SWITCH, INTO GROUP 25.** -/
theorem hT1_fin_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t)
    {q : K2.P2} (hq : q.stands = .finish) {r : SwRow} (hrw : tableFullLit[24]? = some r)
    {W : SwitchFrame} (h0f : K2.frameAt (fxAt r) = some W) :
    ∀ z, ∀ a : S × Str, Rch 353 ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ fx, K2.frontAt q t = some fx →
      frontB2 (fxAt r) W 25 0 (K2.n0At 25) (K2.oldsAt 25) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W (K2.n0At 25) (K2.oldsAt 25)) fx = true ∧
        a.1.st.oracles = fx.st.oracles :=
  fun z a ha => hT1_fin hS hR O hF hpl hy hcut (fun _ _ => Iff.rfl)
    (msgShapes_reached hS hR O hpl hB) hent hq hrw h0f z a (hRch _ _ ha)

end

end P1K2

#print axioms P1K2.msgShapes_reached
#print axioms P1K2.hT1_link_plain
#print axioms P1K2.hT1_head_plain
#print axioms P1K2.hT1_fin_plain
