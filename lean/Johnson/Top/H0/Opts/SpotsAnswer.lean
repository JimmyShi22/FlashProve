-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SpotsAnswer.lean: FOR THE NAMED TEST spotsB
(Johnson/P5J/OptsOk.lean), ITS SECOND HALF: IN THE GOALS' SCOPE, WHERE THE DESCRIPTION IS MADE AND
ITS OWN TEST ON THE LIST OF ROUNDS ACCEPTS, ProofFile.pAtK2? Z m (Johnson/Desc/ProofFile/CarryAt.lean)
ANSWERS AT EVERY m BELOW 25. NO SUB-PROTOCOL IMPORTS THIS FILE.
HOW. pAtK2? Z m is «the first place of the lot's list whose switch opens group m + 1»: it answers
as soon as SOME member of the list opens that group. In scope a member of the lot's table stands at
each of the 25 places of the kind; the description's test makes it live; a live member is made of a
member of the list (table_live · spot_is, K2Caller/PAtSeated.lean); its group is its link's number.
NO NAMED TEST IS SPENT: that the member is the only one is not asked here.
  pAt_some_of_mem   a member of the list that opens group m + 1: pAtK2? Z m answers
  live_answers      a live member x of the lot's table: pAtK2? Z (n.grp - 1) answers, n the numbers
                    at x's link
  pAt_answers_low   in scope, at an opening whose description's test accepts: at every m below 24
  pAt_answers       the same at every m below 25, WITH ONE PREMISE MORE: the sized request has 25
                    links (at the finish the group's number is the number of links)
LIMITS. «25 links» is a theorem UNDER A PIN (request_links_in_scope,
Johnson/Goal/Numbers/RequestLinks.lean); with no pin it is pub_links (PlannerRequestHas25Links.lean): at m = 24
this file takes it as a premise. The test's first half (the typed table is made; its length) is not
here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.SitsAtP
import Johnson.P1K2R.SitsDoor

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.First.K2Caller (table_live spot_is pureAt_is numsAt_pos)
open ProofFile (Cl)
open IM (Open)

theorem pAt_some_of_mem {Z : ProofFile.Pub} {m : Nat} {y : ProofFile.Spot × P2} (hy : y ∈ ProofFile.k2SpotsAt Z)
    (hg : y.2.grp = m + 1) : (ProofFile.pAtK2? Z m).isSome = true := by
  unfold ProofFile.pAtK2?
  rw [Option.isSome_map]
  exact List.find?_isSome.2 ⟨y, hy, by simp [hg]⟩

theorem live_answers {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {x : Block S Unit}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hx : x ∈ pureTable (fun _ _ => some none) Z G₀) (hp : x.planOk = true) :
    ∃ Q n, prepOf Z G₀ = some Q ∧ numsAt Q x.place.link = some n ∧
      (ProofFile.pAtK2? Z (n.grp - 1)).isSome = true := by
  obtain ⟨y, hy, hq⟩ := table_live hx hp
  obtain ⟨Q, n, hQ, hn, e⟩ := spot_is hy
  obtain ⟨e1, -, -⟩ := pureAt_is hq
  have hy' : y ∈ ProofFile.k2SpotsAt Z := by
    unfold ProofFile.k2SpotsAt
    rw [hG]
    exact hy
  have hg0 := numsAt_pos hn
  have hgy : y.2.grp = n.grp := by rw [e]; rfl
  exact ⟨Q, n, hQ, by rw [e1]; exact hn, pAt_some_of_mem hy' (by rw [hgy]; omega)⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At every switch into a segment.** -/
theorem pAt_answers_low (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true) :
    ∀ m, m < 24 → (ProofFile.pAtK2? Z m).isSome = true := by
  intro m hm
  by_cases h23 : m < 23
  · obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_link_sits hS hR O (m + 1) (by omega) (by omega)
    have hb := flat_planOk O hp b (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.framed.laid hb)).1
    obtain ⟨Q, n, -, hn, ha⟩ := live_answers O.blank hx hxp
    rw [place_of_is hi hxp] at hn
    have hg : n.grp = m + 1 := numsAt_grp hn
    rw [hg] at ha
    exact ha
  · obtain rfl : m = 23 := by omega
    obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of hS hR O
    have hb := flat_planOk O hp b (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
    obtain ⟨Q, n, -, hn, ha⟩ := live_answers O.blank hx hxp
    rw [place_of_is hi hxp] at hn
    have hg : n.grp = 24 := numsAt_grp hn
    rw [hg] at ha
    exact ha

/-- **At all 25**, where the sized request has 25 links. -/
theorem pAt_answers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true)
    (hL : Z.p.chains.made.sized.proof.request.link.length = 25) :
    ∀ m, m < 25 → (ProofFile.pAtK2? Z m).isSome = true := by
  intro m hm
  by_cases h24 : m < 24
  · exact pAt_answers_low hS hR O hp m h24
  · obtain rfl : m = 24 := by omega
    obtain ⟨b, x, e1, hx, ep, hl, _⟩ := IM.k2_finish_of O
    have hb := back_planOk O hp (List.mem_of_getElem? e1)
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
    obtain ⟨Q, n, hQ, hn, ha⟩ := live_answers O.blank hx hxp
    rw [ep] at hn
    have hg : n.grp = 25 := by
      rw [numsAt_grp hn]
      show Q.z.request.link.length = 25
      rw [prepOf_z hQ, hL]
    rw [hg] at ha
    exact ha

end

end P1K2

#print axioms P1K2.pAt_some_of_mem
#print axioms P1K2.live_answers
#print axioms P1K2.pAt_answers_low
#print axioms P1K2.pAt_answers
