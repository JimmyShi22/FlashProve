-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPlanAtFrames.lean.
The records of a proof's first chain, by their number.

OnBytes/Tie/Pv/Lookup/Peel/FoPlanAt.lean speaks of the record n at place i of the list of a chain's
records (framesOf,
OnBytes/Plan/ReqFrames.lean), and of n's own number n.l, its link and the number of its later
moments. This file says what these are: the number is i, the link is link number i of the chain's
links, and the later moments are counted off that link's last message.

* laterOf link: the later moments of a link, or of none.
* framesFrom_at: the record at place i of the records from group number l on.
* framesOf_at: the record at place i of a chain's records has n.l = i, n.link = z.request.link[i]?,
  n.moments = laterOf n.link.
* plan_at0_link, plan_at2_link: plan_at0 and plan_at2 with the link's number in place of n.l.
* framesFrom_some: there is a record at place i, if there is a group of that number and every link
  before it is there.
* configure_at0_link, configure_at2_link: the same from a yes of configure at the shapes that the
  verifier's own plans hand over.
Not shown here: how many groups and links a chain has; that a link of the model has two later
moments; what OnBytes/Tie/Pv/Lookup/Peel/FoPlanAt.lean names as not shown.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Peel.FoPlanAt

set_option autoImplicit false

namespace TwLaw
open OnBytes OnBytes.Params OnBytes.Plan TwPlan TwErr TwRound Cb.Fo

/-- The later moments of a link: one less than the moments that its last message names. -/
def laterOf (link : Option ReqLink) : Nat :=
  (((link.map (·.messages)).getD []).getLast?.map (·.moment + 1)).getD 0 - 1

theorem framesFrom_at (z : ProofSized) : ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink)
    (open_ : List Nat) (before : GroupSize) (i : Nat) (n : FrameN),
    (framesFrom z l gs links open_ before)[i]? = some n →
    n.l = l + i ∧ n.link = links[i]? ∧ n.moments = laterOf n.link
  | [], _, _, _, _, _, _, h => by
    unfold framesFrom at h
    cases h
  | g :: gs, l, links, open_, before, 0, n, h => by
    unfold framesFrom at h
    obtain rfl : frameAt z l g gs links open_ before = n := Option.some.inj h
    refine ⟨rfl, ?_, rfl⟩
    show links.head? = links[0]?
    cases links <;> rfl
  | g :: gs, l, links, open_, before, i + 1, n, h => by
    unfold framesFrom at h
    rw [List.getElem?_cons_succ] at h
    cases hl : links.head? with
    | none =>
      rw [hl] at h
      cases h
    | some v =>
      rw [hl] at h
      obtain ⟨a1, a2, a3⟩ := framesFrom_at z gs (l + 1) (links.drop 1) (open_.drop 1)
        (closedGroup z g gs) i n h
      refine ⟨by omega, ?_, a3⟩
      rw [a2, List.getElem?_drop, Nat.add_comm]

/-- The record at place i of a chain's records. -/
theorem framesOf_at (z : ProofSized) (sub : Subproofs) (i : Nat) (n : FrameN)
    (h : (framesOf z sub)[i]? = some n) :
    n.l = i ∧ n.link = z.request.link[i]? ∧ n.moments = laterOf n.link := by
  obtain ⟨a1, a2, a3⟩ := framesFrom_at z _ 0 _ _ _ i n h
  exact ⟨by omega, a2, a3⟩

section
variable {P : Planned} {s : Setting} {z : ProofSized} {sub : Subproofs}
  {L : Nat → Nat → List RoundSpec} {after : List RoundSpec}

/-- plan_at0 by the link's number. -/
theorem plan_at0_link (hP : PlanIs P s .request (firstChainList z sub L after)) (i : Nat)
    (n : FrameN) (v : ReqLink) (hi : (framesOf z sub)[i]? = some n)
    (hv : z.request.link[i]? = some v) (h : FoNums.Sh) (H : FoNums.ok h = true)
    (rest : List RoundSpec) (hL : L i 0 = forestList s (OnBytes.Model.forestSize h) ++ rest) :
    LookAt P s h (preZero z sub L i n).length := by
  obtain ⟨a1, a2, _⟩ := framesOf_at z sub i n hi
  exact plan_at0 hP i n v hi (a2.trans hv) h H rest (by rw [a1]; exact hL)

/-- plan_at2 by the link's number. -/
theorem plan_at2_link (hP : PlanIs P s .request (firstChainList z sub L after)) (i : Nat)
    (n : FrameN) (v : ReqLink) (hi : (framesOf z sub)[i]? = some n)
    (hv : z.request.link[i]? = some v) (hm : 2 ≤ laterOf (some v)) (h : FoNums.Sh)
    (H : FoNums.ok h = true) (rest : List RoundSpec)
    (hL : L i 2 = forestList s (OnBytes.Model.forestSize h) ++ rest) :
    LookAt P s h (preTwo z sub L i n).length := by
  obtain ⟨a1, a2, a3⟩ := framesOf_at z sub i n hi
  exact plan_at2 hP i n v hi (a2.trans hv) (by rw [a3, a2, hv]; exact hm) h H rest
    (by rw [a1]; exact hL)

end

/-- There is a record at place i, if there is a group of that number and every link before it is
there. -/
theorem framesFrom_some (z : ProofSized) : ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink)
    (open_ : List Nat) (before : GroupSize) (i : Nat), i < gs.length →
    (∀ j < i, (links[j]?).isSome = true) →
    ((framesFrom z l gs links open_ before)[i]?).isSome = true
  | [], _, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | g :: gs, l, links, open_, before, 0, _, _ => by
    unfold framesFrom
    rfl
  | g :: gs, l, links, open_, before, i + 1, h, hl => by
    unfold framesFrom
    rw [List.getElem?_cons_succ]
    have h0 : (links.head?).isSome = true := by
      have := hl 0 (Nat.succ_pos _)
      cases links with
      | nil => cases this
      | cons _ _ => rfl
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h0
    rw [hv]
    refine framesFrom_some z gs (l + 1) (links.drop 1) (open_.drop 1) (closedGroup z g gs) i
      (Nat.lt_of_succ_lt_succ h) fun j hj => ?_
    rw [List.getElem?_drop, Nat.add_comm]
    exact hl (j + 1) (Nat.succ_lt_succ hj)

section
open OnBytes.Model.Verify
variable {X : Public} {links : List ReqLink} {layout : ReqLayout} {identifiers : List Nat}
  {x : Shapes} {l : Lines} {cfg : ByteArray} {bits : Nat} {made : Configured}

/-- From configure's yes, by the link's number: the lookup at the head of the first list. -/
theorem configure_at0_link (hx : shapesWith X links layout identifiers = .ok x)
    (hc : configure l x cfg bits = .ok made) (i : Nat) (n : FrameN) (v : ReqLink)
    (hi : (framesOf made.sized.proof x.sub)[i]? = some n)
    (hv : made.sized.proof.request.link[i]? = some v) (h : FoNums.Sh) (H : FoNums.ok h = true)
    (rest : List RoundSpec)
    (hL : linkList (settingOf l) .request X i 0 =
      forestList (settingOf l) (OnBytes.Model.forestSize h) ++ rest) :
    ∃ F S2 S3, made.proof = [F, S2, S3] ∧ LookAt F (settingOf l) h
      (preZero made.sized.proof x.sub (linkList (settingOf l) .request X) i n).length := by
  obtain ⟨F, S2, S3, _, hp, _, p1, _, _⟩ := configure_proof_model hx hc
  exact ⟨F, S2, S3, hp, plan_at0_link p1 i n v hi hv h H rest hL⟩

/-- From configure's yes, by the link's number: the lookup at the head of the list of moment 2. -/
theorem configure_at2_link (hx : shapesWith X links layout identifiers = .ok x)
    (hc : configure l x cfg bits = .ok made) (i : Nat) (n : FrameN) (v : ReqLink)
    (hi : (framesOf made.sized.proof x.sub)[i]? = some n)
    (hv : made.sized.proof.request.link[i]? = some v) (hm : 2 ≤ laterOf (some v)) (h : FoNums.Sh)
    (H : FoNums.ok h = true) (rest : List RoundSpec)
    (hL : linkList (settingOf l) .request X i 2 =
      forestList (settingOf l) (OnBytes.Model.forestSize h) ++ rest) :
    ∃ F S2 S3, made.proof = [F, S2, S3] ∧ LookAt F (settingOf l) h
      (preTwo made.sized.proof x.sub (linkList (settingOf l) .request X) i n).length := by
  obtain ⟨F, S2, S3, _, hp, _, p1, _, _⟩ := configure_proof_model hx hc
  exact ⟨F, S2, S3, hp, plan_at2_link p1 i n v hi hv hm h H rest hL⟩

end
end TwLaw
