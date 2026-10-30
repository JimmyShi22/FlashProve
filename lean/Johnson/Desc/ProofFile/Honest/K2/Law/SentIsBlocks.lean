-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SentIsBlocks.lean: the kind "the code switch" (K2): AT A PLACE
OF THE KIND, WHERE THE LOT's `numsAt` RETURNS, THE HONEST SIDE's LIST OF THE SWITCH's MESSAGES
(`switchSent`, Honest/K2/Part.lean) IS THE BLOCK's OWN: the field `sent` of the place's numbers
(`P1K2.numsAt`, Johnson/Desc/ProofFile/Lot/K2OfPlan.lean), of which the block's roots, seeds,
answers and oracles are made. Statements with their proofs. A law on texts.

The ground is the library's `notices_sent` (Johnson/Top/H0/K2Hands/NoticesSent.lean): what a switch
into a later group announces is what the planner's record of that group says is sent.

  `prep_frames`     the lot's records are the planner's (`Plan.framesOf`) at the lot's sizes
  `framesFrom_some`, `framesOf_some`   a tool: the planner's record number i is there only if i is
                    at most the number of links and the shape has a group number i
  `place_link`      the place's link is the number that the lot hands `numsAt` at that place
  `place_block`     at a place of the kind whose link's number is not 0 (links are counted from 0)
                    and not beyond the last test's, where the plan's shape has a group of that
                    number: the planner's record of that group is there, and its field `sent` is
                    `switchSent`, as a list
  `place_nums`      so, where `numsAt` returns at the place's own link: its field `sent` is
                    `switchSent`; beside that the lot's preparation returns and that the place is
                    the lot's there is no other premise

Limits. That `numsAt` returns is a premise, public; it is shown here at no plan. Nothing in this
file ties either list to the function of the public files or to the written lists of all sendings
(Johnson/G/). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SentIsNotices
import Johnson.Top.H0.K2Hands.NoticesSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes (ReqFrame OracleNotice foldMaskNotice)

/-- The lot's records are the planner's at the lot's sizes. -/
theorem prep_frames {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (h : P1K2.prepOf Z G = some P) :
    P.frames = OnBytes.Plan.framesOf P.z
      (OnBytes.Model.Verify.subproofsWith G.W G.first.shape.link) := by
  unfold P1K2.prepOf P1K2.prepareAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨trees, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rfl

/-- A tool: the planner's record number i is there only if i is at most the number of links and the
list of groups has a member number i. -/
theorem framesFrom_some (z : OnBytes.Params.ProofSized) : ∀ (i l : Nat)
    (gs : List OnBytes.ReqGroup) (links : List OnBytes.Params.ReqLink) (open_ : List Nat)
    (before : OnBytes.Params.GroupSize) (n : OnBytes.Plan.FrameN),
    (OnBytes.Plan.framesFrom z l gs links open_ before)[i]? = some n →
    i ≤ links.length ∧ ∃ g, gs[i]? = some g
  | 0, _, [], _, _, _, _, h => by simp [OnBytes.Plan.framesFrom] at h
  | 0, _, g₀ :: _, _, _, _, _, _ => ⟨Nat.zero_le _, g₀, rfl⟩
  | _ + 1, _, [], _, _, _, _, h => by simp [OnBytes.Plan.framesFrom] at h
  | i + 1, l, g₀ :: gs, links, open_, before, n, h => by
    unfold OnBytes.Plan.framesFrom at h
    rw [List.getElem?_cons_succ] at h
    cases links with
    | nil => simp at h
    | cons v ls =>
      simp only [List.head?_cons] at h
      obtain ⟨h₁, g, hg⟩ := framesFrom_some z i (l + 1) gs ((v :: ls).drop 1) (open_.drop 1) _ n h
      refine ⟨?_, g, by simpa using hg⟩
      simp only [List.drop_succ_cons, List.drop_zero] at h₁
      simp only [List.length_cons]
      omega

/-- The same of `Plan.framesOf`, at the request's links and groups. -/
theorem framesOf_some {z : OnBytes.Params.ProofSized} {sub : OnBytes.Params.Subproofs} {i : Nat}
    {n : OnBytes.Plan.FrameN} (h : (OnBytes.Plan.framesOf z sub)[i]? = some n) :
    i ≤ z.request.link.length ∧ ∃ g, (OnBytes.reqGroups z.request)[i]? = some g := by
  obtain ⟨h₁, g, hg⟩ := framesFrom_some z i 0 _ _ _ _ n h
  exact ⟨h₁, g, by simpa using hg⟩

/-- The place's link is the number that the lot hands `numsAt` at that place. -/
theorem place_link {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G) :
    p.place.link.getD P.z.request.link.length = p.link := by
  cases hs : spotsOf Z.cuts with
  | none =>
    simp only [switchPlaces, hP, hs] at hp
    cases hp
  | some sps =>
    simp only [switchPlaces, hP, hs] at hp
    obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hp
    rfl

/-- **The honest side's list is the field `sent` of the planner's record of that group.** -/
theorem place_block {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    (h₀ : 0 < p.link) (hl : p.link ≤ P.z.request.link.length) {g : OnBytes.ReqGroup}
    (hG : (OnBytes.reqGroups P.z.request)[p.link]? = some g) :
    ∃ n, P.frames[p.link]? = some n ∧ (switchSent p.sizes p.others).toList = n.sent := by
  obtain ⟨h₁, h₂⟩ := place_data hP hp
  obtain ⟨n, hn, he⟩ := VerifiableInference.Desc.First.K2Hands.notices_sent P.z
    (OnBytes.Model.Verify.subproofsWith G.W G.first.shape.link)
    { frameOfPrep P with link := p.link } rfl rfl h₀ hl g hG
  refine ⟨n, by rw [prep_frames hP]; exact hn, ?_⟩
  have ht : p.sizes.target = g.target := by
    rw [h₁]
    show ((OnBytes.reqGroups P.z.request).getD p.link {}).target = _
    rw [Array.getD_eq_getD_getElem?, hG]
    rfl
  show (Tw.K2.switchNotices p.sizes.target p.others).toList = n.sent
  rw [ht, h₂]
  exact he

/-- **So the block's own list is the honest side's.** -/
theorem place_nums {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    {N : P1K2.Nums} (hN : P1K2.numsAt P p.place.link = some N) :
    N.sent = switchSent p.sizes p.others := by
  unfold P1K2.numsAt at hN
  simp only [Option.bind_eq_bind, Option.pure_def, place_link hP hp] at hN
  split at hN
  · cases hN
  · rename_i ht
    obtain ⟨_, _, hN⟩ := Option.bind_eq_some_iff.1 hN
    obtain ⟨f, hf, hN⟩ := Option.bind_eq_some_iff.1 hN
    obtain ⟨lay, _, hN⟩ := Option.bind_eq_some_iff.1 hN
    obtain ⟨read, _, hN⟩ := Option.bind_eq_some_iff.1 hN
    obtain rfl := Option.some.inj hN
    have h₀ : 0 < p.link := Nat.pos_of_ne_zero (by simpa using ht)
    have hf' := hf
    rw [prep_frames hP] at hf'
    obtain ⟨hl, g, hG⟩ := framesOf_some hf'
    obtain ⟨n, hn, he⟩ := place_block hP hp h₀ hl hG
    obtain rfl : f = n := Option.some.inj (hf.symm.trans hn)
    show f.sent.toArray = _
    rw [← he]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.prep_frames
#print axioms ProofFile.Honest.K2.Law.framesFrom_some
#print axioms ProofFile.Honest.K2.Law.framesOf_some
#print axioms ProofFile.Honest.K2.Law.place_link
#print axioms ProofFile.Honest.K2.Law.place_block
#print axioms ProofFile.Honest.K2.Law.place_nums
