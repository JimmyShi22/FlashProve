-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/FoldSideR.lean (over FoldSide.lean and the
  law file Johnson/Top/H0/Walk/ReachCut.lean): THE FOLD's SIDE OF THE CODE SWITCH's FIRST AND
  FOURTH TIE, IN SCOPE, AT ALL 25 SWITCHES, WITH EVERY PREMISE ON A STATE ASKED AT «REACHED»
  STATES ALONE. FoldSide.lean asks the counts and the shapes at every return of the raw fold,
  which is wider than «reached» (what the wrapped sub-protocols reach, the raw ones reach; not
  back): so only a theorem in the fold's own form could pay them. Here a lemma along the one
  «reached» pays.

Main names (namespace `P1K2`).
  `foldSideR_one` · `foldSideR_link` · `foldSideR_head` · `foldSideR_fin`: the ends of
    `foldSide_one` … `foldSide_fin`, to the letter. The count and the shapes at the switch's own
    number are asked AT THE STATE s ITSELF (Hn2, He); the count at the switch before (Hn) and the
    shapes in front of the last closing at the kept old numbers (He0) at every state that `Reach`
    has at that one earlier number. By `reach_cuts_below`: one run, every earlier number, each
    with its wrapped `Reach`.
Limits. Those of FoldSide.lean. A join; no premise is shown met here. Nothing on soundness or on
  hiding.

-/
import Johnson.P1K2R.FoldSide
import Johnson.Top.H0.Walk.ReachCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model OnBytes.Slice Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.First.K2Hands (frontB2 placeFrame Tied csW MW tied_at)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit frontSide_of keptTyped_at)
open Johnson.Desc.First.Walk.Tied (Reach reach_cuts_below)
open Johnson.G (fxAt storedB)
open Meaning.K2
open _root_.Tw.K2 (switchNotices)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE SWITCH INTO GROUP l + 1, 1 ≤ l < 23.** -/
theorem foldSideR_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) {l : ℕ}
    (h1 : 1 ≤ l) (h23 : l < 23) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (l + 1) + 2) (p, s))
    (Hn : ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 2) (p, t) → t.st.oracles.size =
        K2.n0At l)
    (Hn2 : s.st.oracles.size = K2.n0At (l + 1))
    (He : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = MW[o]?)
    (He0 : ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * l + 12) (p, t) →
      ∀ o ∈ K2.oldsAt (l + 1), (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[l]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ (l + 1) 0 (K2.n0At (l + 1)) (K2.oldsAt (l + 1)) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At (l + 1)) (K2.oldsAt (l + 1))) fx = true ∧
        s.st.oracles = fx.st.oracles) := by
  obtain ⟨R, C, f₂, cuts⟩ := reach_cuts_below hr
  obtain ⟨t₀, R₀, C₀, r₀, f₀⟩ := cuts (14 * l + 2) (by omega)
  obtain ⟨s₃, R₃, C₃, r₃, g3⟩ := cuts (14 * l + 12) (by omega)
  obtain ⟨W₀, hW, hB⟩ := front_link_in_scope hS hR O h1 h23 hcs hsh f₀ (Hn _ r₀) g3 f₂ Hn2 He
    (He0 _ r₃) hq h hrw
  obtain ⟨-, -, a3, a4, -⟩ := front_pin_link hS hR O (l := l + 1) (by omega) (by omega) f₂ hq h
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [front_len hS hR O]; omega) hr
  obtain ⟨k1, k2⟩ := closed_at hrw hW
  refine ⟨W₀, hW, frontSide_of h hB hG hA (Or.inl ⟨(by rw [hq]; exact fun e => (by cases e)), rfl⟩)
    k1 k2 (keptTyped_at hrw) (K2Hands.sentW (l + 1)) ?_ (tied_at (by omega) hrw)⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_neg (by omega)]

/-- **AT THE SWITCH INTO GROUP 1.** -/
theorem foldSideR_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 16 (p, s))
    (Hn2 : s.st.oracles.size = K2.n0At 1)
    (He : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = MW[o]?)
    (He0 : ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 12 (p, t) →
      ∀ o ∈ K2.oldsAt 1, (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[0]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 1 0 (K2.n0At 1) (K2.oldsAt 1) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 1) (K2.oldsAt 1)) fx = true ∧
        s.st.oracles = fx.st.oracles) := by
  obtain ⟨R, C, f₂, cuts⟩ := reach_cuts_below hr
  obtain ⟨s₃, R₃, C₃, r₃, g3⟩ := cuts 12 (by omega)
  obtain ⟨W₀, hW, hB⟩ := front_one_in_scope hS hR O hcs hsh g3 f₂ Hn2 He (He0 _ r₃) hq h hrw
  obtain ⟨-, -, a3, a4, -⟩ := front_pin_link hS hR O (l := 1) (by omega) (by omega) f₂ hq h
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [front_len hS hR O]; omega) hr
  obtain ⟨k1, k2⟩ := closed_at hrw hW
  refine ⟨W₀, hW, frontSide_of h hB hG hA (Or.inl ⟨(by rw [hq]; exact fun e => (by cases e)), rfl⟩)
    k1 k2 (keptTyped_at hrw) (K2Hands.sentW 1) ?_ (tied_at (by omega) hrw)⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_neg (by omega)]

/-- **AT THE OUTPUT HEAD's SWITCH, INTO GROUP 24.** -/
theorem foldSideR_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (p, s))
    (Hn : ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 324 (p, t) → t.st.oracles.size = K2.n0At
        23)
    (Hn2 : s.st.oracles.size = K2.n0At 24)
    (He : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = MW[o]?)
    (He0 : ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 334 (p, t) →
      ∀ o ∈ K2.oldsAt 24, (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[23]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 24 0 (K2.n0At 24) (K2.oldsAt 24) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 24) (K2.oldsAt 24)) fx = true ∧
        s.st.oracles = fx.st.oracles) := by
  obtain ⟨R, C, f₀, cuts⟩ := reach_cuts_below hr
  obtain ⟨t₃, R₃, C₃, r₃, f₃⟩ := cuts 324 (by omega)
  obtain ⟨s₃, R₄, C₄, r₄, g3⟩ := cuts 334 (by omega)
  obtain ⟨tm, Rm, Cm, -, fm⟩ := cuts 338 (by omega)
  obtain ⟨W₀, hW, hB⟩ := front_head_in_scope hS hR O hcs hsh f₃ (Hn _ r₃) g3 fm f₀ Hn2 He
    (He0 _ r₄) hq h hrw
  obtain ⟨-, -, a3, a4, -⟩ := front_pin_head hS hR O f₀ hq h
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [front_len hS hR O]; omega) hr
  obtain ⟨k1, k2⟩ := closed_at hrw hW
  refine ⟨W₀, hW, frontSide_of h hB hG hA (Or.inl ⟨(by rw [hq]; exact fun e => (by cases e)), rfl⟩)
    k1 k2 (keptTyped_at hrw) (K2Hands.sentW 24) ?_ (tied_at (by omega) hrw)⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_neg (by omega)]

/-- **AT THE FINISH, INTO GROUP 25.** t: the state behind the quiet step in front of the switch,
    whose
acceptance is a premise. -/
theorem foldSideR_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) {p : ProofFile.InstPub} {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (p, s))
    (Hn2 : s.st.oracles.size = K2.n0At 25)
    (He : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = MW[o]?)
    (hQ : K2.finishFrontQ s = .ok t) {q : K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (h : K2.frontAt q t = some fx) {r : SwRow}
    (hrw : tableFullLit[24]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 25 0 (K2.n0At 25) (K2.oldsAt 25) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 25) (K2.oldsAt 25)) fx = true ∧
        s.st.oracles = fx.st.oracles) := by
  obtain ⟨R, C, f₂, cuts⟩ := reach_cuts_below hr
  obtain ⟨s₃, R₃, C₃, -, g3⟩ := cuts 350 (by omega)
  obtain ⟨W₀, hW, hB⟩ := front_fin_in_scope hS hR O hcs hsh g3 f₂ Hn2 He hQ hq h hrw
  obtain ⟨-, -, a3, a4, -⟩ := front_pin_fin hS hR O f₂ hQ hq h
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [front_len hS hR O]) hr
  obtain ⟨k1, k2⟩ := closed_at hrw hW
  refine ⟨W₀, hW, frontSide_of h hB hG hA (Or.inr ⟨hq, hQ⟩) k1 k2 (keptTyped_at hrw)
    (K2Hands.sentW 25) ?_ (tied_at (by omega) hrw)⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_pos rfl]

end

#print axioms foldSideR_link
#print axioms foldSideR_one
#print axioms foldSideR_head
#print axioms foldSideR_fin

end P1K2
