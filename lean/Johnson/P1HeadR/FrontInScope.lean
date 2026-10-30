-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1HeadR/FrontInScope.lean: «THE TEST ON THE CODE SWITCH's FRONT ACCEPTS», IN SCOPE, FROM THE
FOLD's RETURNS, AT THE PROOF FILE's SEAT, AT THE FULL SIZE: AT ALL 25 SWITCHES: into group 1
(front_one_in_scope) · into group l + 1, 1 ≤ l < 23 (front_link_in_scope) · the head's, into group
24 (front_head_in_scope) · the finish's, into group 25 (front_fin_in_scope: at the state behind the
quiet step «F.0.front», whose accept is a premise).
EVERY PREMISE OF K2Hands.frontB2_at_closing (Johnson/Top/H0/K2Hands/FrontJoinAtClosing.lean) IS PAID HERE BY A CALL OF ANOTHER FILE's THEOREM (under Johnson/IMR/: front_pin_link | _head | _fin · olds_at_one | _link | _head | _fin · front_nums_link | _head | _fin · tail_frame | tail_frame_head · open_recAll · front_len · olds_fin; link_frame: Johnson/Goal/Meaning/RecK9.lean; K2.n0_values | olds_values: Johnson/Top/H0/K2Hears/PlaceNums.lean), BUT THESE, WHICH STAY NAMED PREMISES:
  hcs hsh   the public part's codes and shape are the written ones (first_written_in_scope, Johnson/Goal/Numbers/MadeInScope.lean, under the verifier's test on the plan)
  hn hn2    the counts of messages in front of this switch and of the one before (n0_at_link | n0_at_head, Johnson/IMR/N0AtCut.lean, which have premises of their own: K1Told · K2Told · the chain's blocks have the written cut · their tests on the plan)
  e         «msgShapes» at the border state t₂ in front of the switch (shapes_start, Johnson/IMR/ShapesJoin.lean, with msgShape_at, under shapes_start's debts; with sends_in_scope, Johnson/Goal/Numbers/MadeInScope.lean, for MW). NEVER from the switch's own law at this place.
  e0        «msgShapes» at the border state s in front of link l's closing (the cut 14 l + 12), at the kept old messages' numbers. AT THE FINISH IT FALLS: the finish keeps no old message (olds_fin).
The premises f₀ g3 f₂ are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.FrontPin
import Johnson.IMR.KeptJoin
import Johnson.IMR.HeadFront
import Johnson.IMR.GroupCount
import Johnson.IMR.TailFrame
import Johnson.IMR.FinKept
import Johnson.IMR.FinPin
import Johnson.Top.H0.K2Hands.FrontJoinAtClosing

set_option autoImplicit false

namespace Meaning.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2Hands (frontB2 frontB2_at_closing csW shW MW n0Full oldsFull)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open Johnson.G (fxAt)
open ProofFile (Cl)

/-- The values of `K2.n0_values`, place by place. -/
theorem n0Full_at {k : Nat} (hk : k < 26) : n0Full[k]? = some (K2.n0At k) := by
  have e : (List.range 26).map K2.n0At = n0Full := K2.n0_values
  rw [← e]
  simp [hk]

theorem oldsFull_at {i : Nat} (hi : i < 25) : oldsFull[i]? = some (K2.oldsAt (i + 1)) := by
  have e : (List.range' 1 25).map K2.oldsAt = oldsFull := K2.olds_values
  rw [← e]
  simp [hi, Nat.add_comm]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE CODE SWITCHING INTO GROUP l + 1, 1 ≤ l < 23.** -/
theorem front_link_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h23 : l < 23) (hcs : Z.first.codes = csW) (hsh : Z.first.shape = shW) {p : ProofFile.InstPub}
    {R R₀ R₃ R₂ : List Fmt.RoundView} {C C₀ C₃ C₂ : List VerifiableInference.Desc.OpenedColumn} {t₀ s t₂ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (hn : t₀.st.oracles.size = K2.n0At l)
    (g3 : foldBlocks 0 (c.blocksInOrder.take (14 * l + 12)) (ProofFile.startS Z p) R C = .ok (s, R₃, C₃))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (hn2 : t₂.st.oracles.size = K2.n0At (l + 1))
    (e : ∀ o, o < t₂.st.oracles.size → (t₂.st.oracles[o]?).map (·.shape) = MW[o]?)
    (e0 : ∀ o ∈ K2.oldsAt (l + 1), (s.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₂ = some fx) {r : SwRow} (hr : tableFullLit[l]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      frontB2 (fxAt r) W₀ (l + 1) 0 (K2.n0At (l + 1)) (K2.oldsAt (l + 1)) fx = true := by
  obtain ⟨a1, a2, a3, -, -, a6, a7, a8, a9, -⟩ :=
    front_pin_link hS hR O (l := l + 1) (by omega) (by omega) f₂ hq h
  have b := olds_at_link hS hR O h1 h23 hsh f₀ hn f₂ hq h
  obtain ⟨c1, -, G₀, hG₀, hr0, -, -⟩ := front_nums_link hS hR O (l := l + 1) (by omega) f₂ hq h
  obtain ⟨L, Q, rs, y, hL, -, hc, ey⟩ := tail_frame hS hR O (l := l) (by omega) g3 f₂
  have hlen : 14 * l + 12 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := l + 1) (i := 0) (by omega) (by decide)
    omega
  have Rr : RecAll Z.first.codes Z.first.shape s := open_recAll hS hR O (by omega) hlen g3
  exact frontB2_at_closing hr (n0Full_at (by omega)) (oldsFull_at (by omega)) a1 a3 a7 a8 a9 b c1
    ⟨G₀, hG₀, hr0⟩ (by rw [a2]; exact hn2) hc (by rw [a6, ey]) (link_frame Rr hL).shape Rr.codes
    hcs hsh (by rw [a2]; exact e) e0

/-- **AT THE CODE SWITCHING INTO GROUP 1.** -/
theorem front_one_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = shW) {p : ProofFile.InstPub}
    {R R₃ R₂ : List Fmt.RoundView} {C C₃ C₂ : List VerifiableInference.Desc.OpenedColumn} {s t₂ : S}
    (g3 : foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 12)) (ProofFile.startS Z p) R C = .ok (s, R₃, C₃))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (0 + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (hn2 : t₂.st.oracles.size = K2.n0At 1)
    (e : ∀ o, o < t₂.st.oracles.size → (t₂.st.oracles[o]?).map (·.shape) = MW[o]?)
    (e0 : ∀ o ∈ K2.oldsAt 1, (s.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₂ = some fx) {r : SwRow} (hr : tableFullLit[0]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      frontB2 (fxAt r) W₀ (0 + 1) 0 (K2.n0At 1) (K2.oldsAt 1) fx = true := by
  obtain ⟨a1, a2, a3, -, -, a6, a7, a8, a9, -⟩ :=
    front_pin_link hS hR O (l := 0 + 1) (by omega) (by omega) f₂ hq h
  have b := olds_at_one hS hR O hsh f₂ hq h
  obtain ⟨c1, -, G₀, hG₀, hr0, -, -⟩ := front_nums_link hS hR O (l := 0 + 1) (by omega) f₂ hq h
  obtain ⟨L, Q, rs, y, hL, -, hc, ey⟩ := tail_frame hS hR O (l := 0) (by omega) g3 f₂
  have hlen : 14 * 0 + 12 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := 0 + 1) (i := 0) (by omega) (by decide)
    omega
  have Rr : RecAll Z.first.codes Z.first.shape s := open_recAll hS hR O (by omega) hlen g3
  exact frontB2_at_closing hr (n0Full_at (by omega)) (oldsFull_at (by omega)) a1 a3 a7 a8 a9 b c1
    ⟨G₀, hG₀, hr0⟩ (by rw [a2]; exact hn2) hc (by rw [a6, ey]) (link_frame Rr hL).shape Rr.codes
    hcs hsh (by rw [a2]; exact e) e0

/-- **AT THE HEAD's CODE SWITCHING, INTO GROUP 24.** -/
theorem front_head_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = shW) {p : ProofFile.InstPub}
    {R R₃ R₄ Rm R₀ : List Fmt.RoundView} {C C₃ C₄ Cm C₀ : List VerifiableInference.Desc.OpenedColumn}
    {t₃ s tm t₀ : S}
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * 23 + 2)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (hn : t₃.st.oracles.size = K2.n0At 23)
    (g3 : foldBlocks 0 (c.blocksInOrder.take (14 * 23 + 12)) (ProofFile.startS Z p) R C = .ok (s, R₄, C₄))
    (fm : foldBlocks 0 (c.blocksInOrder.take 338) (ProofFile.startS Z p) R C = .ok (tm, Rm, Cm))
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (hn2 : t₀.st.oracles.size = K2.n0At 24)
    (e : ∀ o, o < t₀.st.oracles.size → (t₀.st.oracles[o]?).map (·.shape) = MW[o]?)
    (e0 : ∀ o ∈ K2.oldsAt 24, (s.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₀ = some fx) {r : SwRow} (hr : tableFullLit[23]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      frontB2 (fxAt r) W₀ (23 + 1) 0 (K2.n0At 24) (K2.oldsAt 24) fx = true := by
  obtain ⟨a1, a2, a3, -, -, a7, a8, a9, -⟩ := front_pin_head hS hR O f₀ hq h
  have b := olds_at_head hS hR O hsh f₃ hn f₀ hq h
  obtain ⟨c1, -, c3, G₀, hG₀, hr0, -, -⟩ := front_nums_head hS hR O fm f₀ hq h
  have fm' : foldBlocks 0 (c.blocksInOrder.take (14 * (23 + 1) + 2)) (ProofFile.startS Z p) R C =
      .ok (tm, Rm, Cm) := fm
  obtain ⟨L, Q, rs, y, hL, -, hc, ey⟩ := tail_frame hS hR O (l := 23) (by omega) g3 fm'
  have hlen : 14 * 23 + 12 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := 24) (i := 0) (by decide) (by decide)
    omega
  have Rr : RecAll Z.first.codes Z.first.shape s := open_recAll hS hR O (by omega) hlen g3
  exact frontB2_at_closing hr (n0Full_at (by omega)) (oldsFull_at (by omega)) a1 a3 a7 a8 a9 b c1
    ⟨G₀, hG₀, hr0⟩ (by rw [a2]; exact hn2) hc (by rw [c3, ey]) (link_frame Rr hL).shape Rr.codes
    hcs hsh (by rw [a2]; exact e) e0

/-- **AT THE FINISH's CODE SWITCHING, INTO GROUP 25.** t': the state behind the quiet step
"F.0.front". -/
theorem front_fin_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = shW) {p : ProofFile.InstPub}
    {R R₃ R₂ : List Fmt.RoundView} {C C₃ C₂ : List VerifiableInference.Desc.OpenedColumn} {s t₂ t' : S}
    (g3 : foldBlocks 0 (c.blocksInOrder.take 350) (ProofFile.startS Z p) R C = .ok (s, R₃, C₃))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (hn2 : t₂.st.oracles.size = K2.n0At 25)
    (e : ∀ o, o < t₂.st.oracles.size → (t₂.st.oracles[o]?).map (·.shape) = MW[o]?)
    (hQ : K2.finishFrontQ t₂ = .ok t') {q : K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (h : K2.frontAt q t' = some fx) {r : SwRow}
    (hr : tableFullLit[24]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      frontB2 (fxAt r) W₀ (24 + 1) 0 (K2.n0At 25) (K2.oldsAt 25) fx = true := by
  obtain ⟨a1, a2, a3, -, -, a7, a8, a9⟩ := front_pin_fin hS hR O f₂ hQ hq h
  have b := olds_at_fin hS hR O hsh f₂ hQ hq h
  obtain ⟨c1, -, c3, -, G₀, hG₀, hr0, -, -⟩ := front_nums_fin hS hR O f₂ hQ hq h
  obtain ⟨L, Q, rs, y, hL, -, hc, ey⟩ := tail_frame_head hS hR O g3 f₂
  have hlen : 350 ≤ (frontOf c).length := by
    rw [front_len hS hR O]
    omega
  have Rr : RecAll Z.first.codes Z.first.shape s := open_recAll hS hR O (by omega) hlen g3
  exact frontB2_at_closing hr (n0Full_at (by omega)) (oldsFull_at (by omega)) a1 a3 a7 a8 a9 b c1
    ⟨G₀, hG₀, hr0⟩ (by rw [a2]; exact hn2) hc (by rw [c3, ey]) (link_frame Rr hL).shape Rr.codes
    hcs hsh (by rw [a2]; exact e) (by rw [olds_fin]; intro o ho; cases ho)

end

end Meaning.K2

#print axioms Meaning.K2.front_link_in_scope
#print axioms Meaning.K2.front_one_in_scope
#print axioms Meaning.K2.front_head_in_scope
#print axioms Meaning.K2.front_fin_in_scope
