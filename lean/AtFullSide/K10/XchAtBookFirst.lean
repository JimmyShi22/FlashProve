-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/XchAtBookFirst.lean: the closing of a segment (K10): the fields on the book of the records on the senders and what the
fields `stand` ask of the book, at the real values: the return's public part and ground, the head's chain, the lot's own places of
the code switch and the shared kind's jobs as the base prover lays them. No premise is left but the head at the return, and the
closing's tie.

  `first_params`, `segments_first`, `places_first`   the return's ground has the written shape, codes, segments and places
  `place_of_link`   at each of the segments 1 to 24 the lot has its place of the code switch
  **`fresh_switch_first`**, **`tie_switch_first`**, **`front_switch_first`**   at segments 1 to 24, at a place of the lot
  **`tie_moment_first`**, **`tie_moment_zero`**   the later moments' jobs, at the numbers of `threeLeft_at_switch` and `threeLeft_at_first`
  **`tie_two_first`**, **`fresh_two_first`**   the opening's job at the first segment
  **`handed_first`**, **`later_cut_first`**, **`two_cut_first`**   the senders' coins

Limits. The head at the return is a premise. Owners, starts and counts alone. The full size alone.
-/
import AtFullSide.K10.XchAtBookCoins
import AtFullSide.K1.RecordAtBase
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.AtBaseGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 ProofFile.Honest.FirstThread AtFullSide.K14
open ProofFile.Honest.K2 (SwitchPlace dueBefore messageDue fromE switchSent switchFresh segmentsOf switchPlaces)
open ProofFile.Honest.K2.Law (segsW placesW)
open ProofFile.Honest.K1 (jobTwoAt jobLaterAt)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.HonestTrace (Sz)
open Johnson.G (codesFull2)
open P5J (TS)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The written places hold each of the segments 1 to 24. -/
theorem places_links : ((List.range 24).all fun i => placesW.any fun p => p.link == i + 1) = true := by decide +kernel

variable {files : VerifierAndGoals.PublicFiles} {W₀ Rc Tr X₀ X : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (head : HeadAtReturn files A)

include head in
/-- The return's ground has the written shape and codes. -/
theorem first_params : A.G.first.shape = shapeFull ∧ A.G.first.codes = codesFull2 := by
  obtain ⟨_, hP⟩ := head.returned
  obtain ⟨Bs, base, O⟩ := head.head.toAtMg.laid.opened
  have eG : Bs.G₀ = A.G := base_ground_atPure O.made hP rfl
  rw [← eG, O.first]
  exact ⟨head.head.toAtMg.shape_full, head.head.toAtMg.codes_full⟩

include head in
/-- The return's ground has the written segments. -/
theorem segments_first : segmentsOf A.Z A.G = segsW := by
  obtain ⟨_, hP⟩ := head.returned
  obtain ⟨Bs, base, O⟩ := head.head.toAtMg.laid.opened
  have eG : Bs.G₀ = A.G := base_ground_atPure O.made hP rfl
  rw [← eG]
  exact K2.Law.segments_at_head head.head.toAtMg O

include head in
/-- The return's ground has the written places of the code switch. -/
theorem places_first : switchPlaces A.Z A.G = placesW := by
  obtain ⟨_, hP⟩ := head.returned
  obtain ⟨Bs, base, O⟩ := head.head.toAtMg.laid.opened
  have eG : Bs.G₀ = A.G := base_ground_atPure O.made hP rfl
  rw [← eG]
  exact K2.Law.places_at_head head.head.toAtMg O

include head in
/-- **At each of the segments 1 to 24 the lot has its place of the code switch.** -/
theorem place_of_link {l : Nat} (h1 : 1 ≤ l) (h2 : l < 25) : ∃ p ∈ switchPlaces A.Z A.G, p.link = l := by
  have t := List.all_eq_true.1 places_links (l - 1) (List.mem_range.2 (by omega))
  obtain ⟨p, hp, e⟩ := List.any_eq_true.1 t
  refine ⟨p, by rw [places_first head]; exact hp, ?_⟩
  have e' : p.link = l - 1 + 1 := beq_iff_eq.1 e
  omega

variable {l : Nat} {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
  (Td : Tied head.firstChain A.Z l pw Qc blk)

include Td in
/-- **The field book of `FreshBySwitch`.** -/
theorem fresh_switch_first {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) (hl : p.link = l) :
    ∀ e ∈ A.B.ahead, (e.spender == ⟨blk.place, 0⟩) = true → e.once = true → e.owner = ⟨p.place, 0⟩ ∧
      e.start.e = (dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)
          ((switchSent p.sizes p.others).size - 1)).e +
        fromE p.sizes.codes
          ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape := by
  obtain ⟨_, hP⟩ := head.returned
  exact fresh_switch_field head.head hP Td (places_first head ▸ hp) hl

include Td in
/-- **The field book of `TieBySwitch`.** -/
theorem tie_switch_first {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) (hl : p.link = l) :
    ∀ n, n + 1 < (switchSent p.sizes p.others).size → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum + (0 + n)]? = some e ∧
      e.owner = ⟨p.place, 0⟩ ∧
      e.start = dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n ∧
      e.count = messageDue p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape
        (K2.foldAt (switchFresh p.sizes p.others p.foldVars) n) := by
  obtain ⟨_, hP⟩ := head.returned
  exact tie_switch_field head.head hP Td (segments_first head) (places_first head ▸ hp) hl

include Td in
/-- **The field bookFront of `TieBySwitch`.** -/
theorem front_switch_first {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) (hl : p.link = l) :
    ∀ n, n < 0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum →
      ∃ e e', (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[n]? = some e ∧
        (K12.Light.carriedOf A.B ⟨p.place, 0⟩)[n]? = some e' ∧
        e.owner = e'.owner ∧ e.start = e'.start ∧ e.count = e'.count := by
  obtain ⟨_, hP⟩ := head.returned
  exact front_switch_field head.head hP Td (segments_first head) (places_first head ▸ hp) hl

include Td in
/-- The field book of `TieByShared` at a later moment, at its number lo, where the closed test accepts there. -/
theorem tie_moment_at (S : Sz) (d : Bool) (lo : Nat) (ht : laterB 0 lo l d = true) :
    ∀ n, n < 1 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum + (lo + n)]? = some e ∧
      e.owner = ⟨(jobLaterAt S A.Z A.G l d).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (jobLaterAt S A.Z A.G l d).P (jobLaterAt S A.Z A.G l d).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G l d).P (jobLaterAt S A.Z A.G l d).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G l d).P (jobLaterAt S A.Z A.G l d).ride).e := by
  obtain ⟨_, hP⟩ := head.returned
  obtain ⟨hs, hc⟩ := first_params head
  exact tie_later_field head.head hP Td (segments_first head) hs hc _ _ _ d lo ht

include Td in
/-- **The field book of `TieByShared` at the two later moments of a segment 1 to 24**, at the numbers of
`threeLeft_at_switch`: the first moment's message stands behind the switch's, the second's behind that. -/
theorem tie_moment_first (S : Sz) {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) (hl : p.link = l) (h25 : l < 25) :
    (∀ n, n < 1 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum +
          (0 + ((switchSent p.sizes p.others).size - 1) + n)]? = some e ∧
      e.owner = ⟨(jobLaterAt S A.Z A.G l false).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (jobLaterAt S A.Z A.G l false).P (jobLaterAt S A.Z A.G l false).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G l false).P (jobLaterAt S A.Z A.G l false).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G l false).P (jobLaterAt S A.Z A.G l false).ride).e) ∧
    (∀ n, n < 1 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum +
          (0 + ((switchSent p.sizes p.others).size - 1 + 1) + n)]? = some e ∧
      e.owner = ⟨(jobLaterAt S A.Z A.G l true).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (jobLaterAt S A.Z A.G l true).P (jobLaterAt S A.Z A.G l true).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G l true).P (jobLaterAt S A.Z A.G l true).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G l true).P (jobLaterAt S A.Z A.G l true).ride).e) := by
  have hW : p ∈ placesW := places_first head ▸ hp
  have t := at_seg (List.all_eq_true.1 later_at_places p hW) (hl ▸ h25)
  rw [Bool.and_eq_true, hl] at t
  exact ⟨tie_moment_at head Td S false _ t.1, tie_moment_at head Td S true _ t.2⟩

include Td in
/-- **The same at the first segment**, at the numbers of `threeLeft_at_first`. -/
theorem tie_moment_zero (S : Sz) (h0 : l = 0) :
    (∀ n, n < 1 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum + (0 + 3 + n)]? = some e ∧
      e.owner = ⟨(jobLaterAt S A.Z A.G 0 false).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (jobLaterAt S A.Z A.G 0 false).P (jobLaterAt S A.Z A.G 0 false).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G 0 false).P (jobLaterAt S A.Z A.G 0 false).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G 0 false).P (jobLaterAt S A.Z A.G 0 false).ride).e) ∧
    (∀ n, n < 1 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum + (0 + (3 + 1) + n)]? = some e ∧
      e.owner = ⟨(jobLaterAt S A.Z A.G 0 true).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (jobLaterAt S A.Z A.G 0 true).P (jobLaterAt S A.Z A.G 0 true).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G 0 true).P (jobLaterAt S A.Z A.G 0 true).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G 0 true).P (jobLaterAt S A.Z A.G 0 true).ride).e) := by
  subst h0
  have t := later_at_zero
  rw [Bool.and_eq_true] at t
  exact ⟨tie_moment_at head Td S false _ t.1, tie_moment_at head Td S true _ t.2⟩

include Td in
/-- **The field book of `TieByShared` at the opening's job, at the first segment.** -/
theorem tie_two_first (S : Sz) (h0 : l = 0) :
    ∀ n, n < 3 → ∃ e, (K12.Light.carriedOf A.B ⟨blk.place, 0⟩)[
        0 + ((lotSegs A.Z A.G Qc).dropLast.map (·.messages)).sum + (0 + n)]? = some e ∧
      e.owner = ⟨(jobTwoAt S A.Z A.G).P.place, 0⟩ ∧
      e.start = ProofFile.Honest.K1.startR (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride n ∧
      e.start.f + e.count.f ≤ (ProofFile.Honest.K1.dueR (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride).f ∧
      e.start.e + e.count.e ≤ (ProofFile.Honest.K1.dueR (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride).e := by
  obtain ⟨_, hP⟩ := head.returned
  obtain ⟨hs, hc⟩ := first_params head
  exact tie_open_field head.head hP Td (segments_first head) h0 hs hc _ _ _

include Td in
/-- **The field book of `FreshByShared` at the opening's job, at its message number 3.** -/
theorem fresh_two_first (S : Sz) (h0 : l = 0) :
    ∀ e ∈ A.B.ahead, (e.spender == ⟨blk.place, 0⟩) = true → e.once = true →
      e.owner = ⟨(jobTwoAt S A.Z A.G).P.place, 0⟩ ∧
      e.start.e = ProofFile.Honest.K1.maskStart (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride 3 := by
  obtain ⟨_, hP⟩ := head.returned
  obtain ⟨hs, hc⟩ := first_params head
  exact fresh_open_field head.head hP Td h0 hs hc _ _ _

include head in
/-- **The code switch is handed its coins**, at every run's coins. -/
theorem handed_first {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) (k : Coins A.B) : ∃ c, K2.handed 0 p k = some c := by
  obtain ⟨_, hP⟩ := head.returned
  exact handed_field head.head hP (places_first head ▸ hp) k

include head in
/-- **A later moment's sender has its cut**, at every run's coins. -/
theorem later_cut_first (S : Sz) (hl : l < 25) (d : Bool) (k : Coins A.B) :
    ∃ c, ProofFile.Honest.K1.lentCut k 0 ⟨(jobLaterAt S A.Z A.G l d).P.place, 0⟩
      (ProofFile.Honest.K1.dueR (jobLaterAt S A.Z A.G l d).P (jobLaterAt S A.Z A.G l d).ride) = some c := by
  obtain ⟨_, hP⟩ := head.returned
  obtain ⟨hs, hc⟩ := first_params head
  exact later_cut_field head.head hP hs hc _ hl d _ _ k

include head in
/-- **The opening's sender has its cut**, at every run's coins. -/
theorem two_cut_first (S : Sz) (k : Coins A.B) :
    ∃ c, ProofFile.Honest.K1.lentCut k 0 ⟨(jobTwoAt S A.Z A.G).P.place, 0⟩
      (ProofFile.Honest.K1.dueR (jobTwoAt S A.Z A.G).P (jobTwoAt S A.Z A.G).ride) = some c := by
  obtain ⟨_, hP⟩ := head.returned
  obtain ⟨hs, hc⟩ := first_params head
  exact open_cut_field head.head hP hs hc _ _ _ k

end AtFullSide.K10

#print axioms AtFullSide.K10.places_links
#print axioms AtFullSide.K10.first_params
#print axioms AtFullSide.K10.segments_first
#print axioms AtFullSide.K10.places_first
#print axioms AtFullSide.K10.place_of_link
#print axioms AtFullSide.K10.fresh_switch_first
#print axioms AtFullSide.K10.tie_switch_first
#print axioms AtFullSide.K10.front_switch_first
#print axioms AtFullSide.K10.tie_moment_at
#print axioms AtFullSide.K10.tie_moment_first
#print axioms AtFullSide.K10.tie_moment_zero
#print axioms AtFullSide.K10.tie_two_first
#print axioms AtFullSide.K10.fresh_two_first
#print axioms AtFullSide.K10.handed_first
#print axioms AtFullSide.K10.later_cut_first
#print axioms AtFullSide.K10.two_cut_first
