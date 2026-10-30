-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/UnitsAtBatchAll.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE CHAIN's OWN BLOCKS
REACH IN FRONT OF AN ATTENTION SEGMENT's BATCHING, AND OF THE HEAD's, THE PUBLIC TEST `unitsLaid`
(Johnson/Desc/K8/Honest/FallCount.lean) SAYS YES; SO THE COUNT THERE. Lemmas; none of the library's
goals. No prover stands in them; nothing on completeness, soundness or hiding.

The like of Johnson/P1K8R/UnitsAtBatch.lean (feed-forward segments). The letters are those of an
opening of the description (IM.Open). IT STANDS ON THE LIBRARY's `planned_at_batch`
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean), as that file does.
  **`units_at_batch_att`**, **`units_at_batch_head`**   in the goals' scope, at every state reached
      at number 14 l + 9 (an attention segment l), at number 347 (the head's): the state holds data
      that pass `unitsLaid` at the plan's lengths ProofFile.k8NU Bs.G₀ X and array number 0
  **`fall_at_reached_att`**, **`fall_at_reached_head`**   so the count of
      Johnson/P1K8R/FallAtSeatAtt.lean and FallAtSeatHead.lean at every such state, for every d that
      bounds the exponents at whatever it holds
By: `planned_at_batch` with `planned_view`, `units_of_view` (UnitsAtBatch.lean) · IM.ground_named,
IM.ground_tails (Johnson/IMR/PureJoin.lean, K8Seat.lean) · `public_A_units`, `public_H_units`
(Johnson/P1K8R/UnitsAtPlans.lean).
Limits: those of UnitsAtBatch.lean. That any state is reached there is not said.

-/
import Johnson.P1K8R.UnitsAtBatch
import Johnson.P1K8R.UnitsAtPlans
import Johnson.P1K8R.FallAtSeatAtt
import Johnson.P1K8R.FallAtSeatHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Tie.Pv.Tail.Port (topOf)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At every state reached in front of an attention segment's batching the test says yes.** -/
theorem units_at_batch_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (hsub : IM.subAt l = .attention) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) :
    ∃ (X : LinkH) (tl : HTailF2), Bs.G₀.built.toList[l]? = some X ∧ s.tl? = some tl ∧
      unitsLaid (ProofFile.k8NU Bs.G₀ X) tl 0 = true := by
  obtain ⟨g, hg, rfl⟩ : ∃ g, g < 12 ∧ l = 2 * g + 1 := by
    unfold IM.subAt at hsub
    split at hsub
    · cases hsub
    · split at hsub
      · cases hsub
      · exact ⟨l / 2, by omega, by omega⟩
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X, -, -, -, -, e3, hk, hXg, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_view hS hR O (x := (2 * g + 1, 4, 2))
    (List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 hl, by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩)
    e3 (z, s) h
  rw [htl] at hv
  have hnU : ProofFile.k8NU Bs.G₀ X = q.seam.nU := by
    unfold ProofFile.k8NU
    simp [hk, hXg, eq]
  obtain ⟨tl, hts, hU⟩ := units_of_view hv (public_A_units O.public g q eq)
  exact ⟨X, tl, by rw [Array.getElem?_toList]; exact e3, hts, by rw [hnU]; exact hU⟩

/-- **At every state reached in front of the head's segment's batching the test says yes.** -/
theorem units_at_batch_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s)) :
    ∃ (X : LinkH) (tl : HTailF2), Bs.G₀.built.toList[24]? = some X ∧ s.tl? = some tl ∧
      unitsLaid (ProofFile.k8NU Bs.G₀ X) tl 0 = true := by
  obtain ⟨-, X, e3, hk, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X', e3', htl, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_view hS hR O (x := (24, 5, 3))
    (List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩) e3 (z, s) h
  rw [htl] at hv
  have hnU : ProofFile.k8NU Bs.G₀ X = Bs.G₀.W.H.nU := by
    unfold ProofFile.k8NU
    simp [hk]
  obtain ⟨tl, hts, hU⟩ := units_of_view hv (public_H_units O.public)
  exact ⟨X, tl, by rw [Array.getElem?_toList]; exact e3, hts, by rw [hnU]; exact hU⟩

/-- **The count at every state reached in front of an attention segment's batching.** -/
theorem fall_at_reached_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (hsub : IM.subAt l = .attention) :
    ∃ (Lk : Link S Claim) (p : K9.Where) (X : LinkH),
      c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      c.blocksInOrder[14 * l + 9]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      ∀ (z : ProofFile.InstPub) (s : S) (d : Nat), Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E =>
          askBehind (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs [])
            (zeroUnitAt (ProofFile.k8NU Bs.G₀ X)) s [chiAt x] = true) ≤
          (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d := by
  obtain ⟨Lk, p, X, e1, e2, hX, hflat, -, h7, hcount, -⟩ := fall_at_seat_att hS hR O l hl hsub
  rw [h7] at hflat
  refine ⟨Lk, p, X, e1, e2, hX, hflat, fun z s d hr hd => ?_⟩
  obtain ⟨X', tl, hX', hts, hU⟩ := units_at_batch_att hS hR O hl hsub hr
  obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
  refine hcount s 0 d (fun tl' ht' => ?_) hd
  obtain rfl : tl = tl' := Option.some.inj (hts.symm.trans ht')
  exact hU

/-- **The count at every state reached in front of the head's segment's batching.** -/
theorem fall_at_reached_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Claim) (p : K9.Where) (X : LinkH),
      c.links[24]? = some Lk ∧ IM.k9At Z 24 = some p ∧ Bs.G₀.built.toList[24]? = some X ∧
      c.blocksInOrder[347]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      ∀ (z : ProofFile.InstPub) (s : S) (d : Nat), Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E =>
          askBehind (fun t rs => (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide t rs [])
            (zeroUnitAt (ProofFile.k8NU Bs.G₀ X)) s [chiAt x] = true) ≤
          (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d := by
  obtain ⟨Lk, p, X, e1, e2, hX, hflat, -, h9, hcount, -⟩ := fall_at_seat_head hS hR O
  rw [h9] at hflat
  refine ⟨Lk, p, X, e1, e2, hX, hflat, fun z s d hr hd => ?_⟩
  obtain ⟨X', tl, hX', hts, hU⟩ := units_at_batch_head hS hR O hr
  obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
  refine hcount s 0 d (fun tl' ht' => ?_) hd
  obtain rfl : tl = tl' := Option.some.inj (hts.symm.trans ht')
  exact hU

end

end P1K8

#print axioms P1K8.units_at_batch_att
#print axioms P1K8.units_at_batch_head
#print axioms P1K8.fall_at_reached_att
#print axioms P1K8.fall_at_reached_head
