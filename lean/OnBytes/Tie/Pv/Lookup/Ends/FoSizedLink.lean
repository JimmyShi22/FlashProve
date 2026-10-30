-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoSizedLink.lean.
The links of the sized request of a proof's first chain: how many there are, and what each is.

The planner sizes a proof's chains by proofSized (OnBytes/Params/DeriveReq.lean), which lays into
the request's shape the sub-proofs' links with the numbers of two codes filled in (fillLinks). The
model's sub-proofs hand over the frame's links, with the last link's number of plain scalars put to
1 (withReply, OnBytes/Model/VerifySubproofs.lean). Both keep the number of the links and the moment
of every oracle message. shapesWith tests that the frame's links are as many as the model has
sub-proofs. This file keeps these facts.

What they serve: that the sized request has a link v at number i is a premise of plan_at0_link and
plan_at2_link (OnBytes/Tie/Pv/Lookup/Peel/FoPlanAtFrames.lean) and of framesOf_link
(OnBytes/Tie/Pv/Lookup/Peel/FoPlanAtSome.lean); that v has two later moments is a premise of
plan_at2_link alone. No statement here draws a lookup's place.

* proofSized_link: what proofSized returns has request.link = fillLinks sub.links.
* withReply_length, withReply_at, fillLinks_at: the two maps, link by link.
* laterOf_moments_eq: two links whose messages have the same moments have the same later moments.
* shapesWith_length: from a yes of shapesWith: the frame's links are (2 or 1) * NGr + 1.
* request_links: from the yes of shapesWith and of configure: made.sized.proof.request.link is
  fillLinks (withReply reqLinks), and reqLinks has that length.
* request_link_at: for every i below that length there are a link v of the sized request and a link
  v0 of the frame's links at number i, with the same later moments.
* momentsB reqLinks: every link of the frame has three moments or more, as a Bool.
* request_link_some: where the frame's links pass momentsB, the link v at number i has two later
  moments or more.
Not shown here: that the frame's links pass momentsB. It is a fact of the layout file and of the
arrays that the sub-proofs' plans declare (Plan.reqFrame, OnBytes/Plan/ReqFrame.lean; declareOwn,
OnBytes/Model/StagesLinks.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Peel.FoPlanAtSome

set_option autoImplicit false

namespace TwLaw
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model.Verify

theorem proofSized_link {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) : z.request.link = fillLinks sub.links := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, _, h⟩ := opt_bind h
  obtain ⟨stages, _, h⟩ := opt_bind h
  obtain ⟨T, _, h⟩ := opt_bind h
  split at h
  replace h := opt_guard h
  obtain ⟨⟨batch, codes2⟩, _, h⟩ := opt_bind h
  cases h
  rfl

theorem withReply_length : ∀ L : List ReqLink, (withReply L).length = L.length
  | [] => rfl
  | [_] => rfl
  | _ :: b :: L => by
    show (withReply (b :: L)).length + 1 = (b :: L).length + 1
    rw [withReply_length (b :: L)]

theorem withReply_at : ∀ (L : List ReqLink) (i : Nat) (v0 : ReqLink), L[i]? = some v0 →
    ∃ v1, (withReply L)[i]? = some v1 ∧ v1.messages = v0.messages
  | [], _, _, h => by cases h
  | [a], 0, v0, h => by
    obtain rfl : a = v0 := Option.some.inj h
    exact ⟨_, rfl, rfl⟩
  | [_], _ + 1, _, h => by cases h
  | a :: b :: L, 0, v0, h => by
    obtain rfl : a = v0 := Option.some.inj h
    exact ⟨_, rfl, rfl⟩
  | _ :: b :: L, i + 1, v0, h => withReply_at (b :: L) i v0 h

theorem fillLinks_at (L : List ReqLink) (i : Nat) (v1 : ReqLink) (h : L[i]? = some v1) :
    ∃ v, (fillLinks L)[i]? = some v ∧
      v.messages.map (·.moment) = v1.messages.map (·.moment) := by
  unfold fillLinks
  rw [List.getElem?_map, h]
  refine ⟨_, rfl, ?_⟩
  simp [Function.comp_def]

theorem laterOf_moments_eq {v v' : ReqLink}
    (h : v.messages.map (·.moment) = v'.messages.map (·.moment)) :
    laterOf (some v) = laterOf (some v') := by
  have e : ∀ w : ReqLink, laterOf (some w) =
      (((w.messages.map (·.moment)).getLast?).map (· + 1)).getD 0 - 1 := by
    intro w
    unfold laterOf
    rw [List.getLast?_map, Option.map_map]
    rfl
  rw [e, e, h]

theorem shapesWith_length {X : Public} {links : List ReqLink} {lay : ReqLayout}
    {ids : List Nat} {x : Shapes} (h : shapesWith X links lay ids = .ok x) :
    links.length = (if X.p4 then 2 else 1) * X.NGr + 1 := by
  unfold shapesWith at h
  extract_lets at h
  obtain ⟨rc, _, h⟩ := exc_bind h
  have hn := exc_guard_not h
  simpa using hn

section
variable {X : Public} {reqLinks : List ReqLink} {lay : ReqLayout} {ids : List Nat} {x : Shapes}
  {l : Lines} {cfg : ByteArray} {bits : Nat} {made : Configured}

/-- The links of the sized request. -/
theorem request_links (hx : shapesWith X reqLinks lay ids = .ok x)
    (hc : configure l x cfg bits = .ok made) :
    made.sized.proof.request.link = fillLinks (withReply reqLinks) ∧
      reqLinks.length = (if X.p4 then 2 else 1) * X.NGr + 1 := by
  refine ⟨?_, shapesWith_length hx⟩
  rw [proofSized_link (configure_proof_sizes hc).1, shapesWith_sub hx]
  rfl

/-- The link at a number below the number of the model's sub-proofs. -/
theorem request_link_at (hx : shapesWith X reqLinks lay ids = .ok x)
    (hc : configure l x cfg bits = .ok made) (i : Nat)
    (hi : i < (if X.p4 then 2 else 1) * X.NGr + 1) :
    ∃ v v0, made.sized.proof.request.link[i]? = some v ∧ reqLinks[i]? = some v0 ∧
      laterOf (some v) = laterOf (some v0) := by
  obtain ⟨e, hl⟩ := request_links hx hc
  have h0 : reqLinks[i]? = some reqLinks[i] := List.getElem?_eq_getElem (by omega)
  obtain ⟨v1, a1, a2⟩ := withReply_at reqLinks i _ h0
  obtain ⟨v, b1, b2⟩ := fillLinks_at _ i v1 a1
  exact ⟨v, _, by rw [e]; exact b1, h0, laterOf_moments_eq (by rw [b2, a2])⟩

/-- Every link of the frame has three moments or more, as a test that can be run. -/
def momentsB (reqLinks : List ReqLink) : Bool :=
  reqLinks.all fun v => decide (3 ≤ OnBytes.reqMoments v)

/-- The link at a number, with two later moments, where the frame's links pass momentsB. -/
theorem request_link_some (hx : shapesWith X reqLinks lay ids = .ok x)
    (hc : configure l x cfg bits = .ok made) (hB : momentsB reqLinks = true) (i : Nat)
    (hi : i < (if X.p4 then 2 else 1) * X.NGr + 1) :
    ∃ v, made.sized.proof.request.link[i]? = some v ∧ 2 ≤ laterOf (some v) := by
  obtain ⟨v, v0, a1, a2, a3⟩ := request_link_at hx hc i hi
  refine ⟨v, a1, ?_⟩
  have hm : 3 ≤ OnBytes.reqMoments v0 :=
    of_decide_eq_true (List.all_eq_true.1 hB v0 (List.mem_of_getElem? a2))
  rw [a3, laterOf_moments]
  omega

end
end TwLaw
