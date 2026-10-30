-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FrontLayB.lean: helpers for AtFullSide/K2/FrontLay.lean: at a reached state, at each
of the three sorts of a code switch's places: the carried rows have two mask rows, and their number of
kept rows is the sum of the kept members' main rows at the front's own statement. Calls of
front_pin_link, front_pin_head (Johnson/IMR/FrontPin.lean), front_pin_fin (Johnson/IMR/FinPin.lean),
link_closed_reached (Johnson/Desc/K2/Honest/Returns/ClosedReached.lean), rows_of_close
(Returns/MembersReached.lean), head_members_reached, fin_members_reached (Returns/ClosedArms.lean).
No definition. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K2.Honest.Returns.FrontTiesReached
import Johnson.Desc.K2.Honest.Returns.MembersReached
import Johnson.Desc.K2.Honest.Returns.ClosedArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription Grows)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.K2.Honest.Returns
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **At a state reached in front of the switch into a later group.** -/
theorem link_frontRows (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) {p : K2.P2}
    (hq : p.stands = .link) {fx : _root_.Tw.K2.Front} (h : K2.frontAt p s = some fx) :
    fx.f.rows.masks = 2 ∧ fx.f.rows.keptRows = (List.map
      (fun o => (fx.st.oracles.getD o default).shape.mainRows)
      (switchKept fx.f.rows).toList).sum := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨-, a2, -, -, -, a6, -, -, a9, -⟩ :=
    Meaning.K2.front_pin_link hS hR O (l := m + 1) (by omega) (by omega) f hq h
  obtain ⟨owed, f', S₀, es, rs, x, hx, hf, hg⟩ := link_closed_reached hS hR O h23 hr
  refine ⟨a9, ?_⟩
  rw [a6, a2, hf]
  exact rows_of_close hx hg

/-- **At the output head's front.** -/
theorem head_frontRows (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {p : K2.P2}
    (hq : p.stands = .head) {fx : _root_.Tw.K2.Front} (h : K2.frontAt p s = some fx) :
    fx.f.rows.masks = 2 ∧ fx.f.rows.keptRows = (List.map
      (fun o => (fx.st.oracles.getD o default).shape.mainRows)
      (switchKept fx.f.rows).toList).sum := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨-, -, -, -, -, -, -, a9, -⟩ := Meaning.K2.front_pin_head hS hR O f hq h
  refine ⟨a9, ?_⟩
  rcases K2.frontOf_iff.2 h with ⟨hp, -⟩ | ⟨-, a, G₀, here, -, rfl⟩ | ⟨hp, -⟩
  · rw [hq] at hp
    cases hp
  · exact (head_members_reached hS hR O hr here G₀.target).1
  · rw [hq] at hp
    cases hp

/-- **At the front behind the last segment, behind its quiet step in front.** -/
theorem fin_frontRows (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : K2.finishFrontQ s = .ok t) {p : K2.P2} (hq : p.stands = .finish)
    {fx : _root_.Tw.K2.Front} (h : K2.frontAt p t = some fx) :
    fx.f.rows.masks = 2 ∧ fx.f.rows.keptRows = (List.map
      (fun o => (fx.st.oracles.getD o default).shape.mainRows)
      (switchKept fx.f.rows).toList).sum := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨-, -, -, -, -, -, -, a9⟩ := Meaning.K2.front_pin_fin hS hR O f he hq h
  refine ⟨a9, ?_⟩
  rcases K2.frontOf_iff.2 h with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨-, a, G₀, here, -, rfl⟩
  · rw [hq] at hp
    cases hp
  · rw [hq] at hp
    cases hp
  · exact (fin_members_reached hS hR O hr he here G₀).1

end AtFullSide.K2

#print axioms AtFullSide.K2.link_frontRows
#print axioms AtFullSide.K2.head_frontRows
#print axioms AtFullSide.K2.fin_frontRows
