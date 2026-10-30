-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPlanAtSome.lean.
The records of a proof's first chain: there is one for each link, and a link's later moments.

OnBytes/Tie/Pv/Lookup/Peel/FoPlanAtFrames.lean asks that there is a record at place i of a chain's
records, and counts a link's
later moments off its last message (laterOf). This file pays the first for every link of the chain,
and says the second in the words of OnBytes/Iop/Req.lean.

* groupsFrom_length, groups_length: a request has one group more than it has links.
* framesOf_some: for every link number i there is a record at place i.
* framesOf_link: that record n has n.l = i, n.link = some v and n.moments = laterOf (some v), where
  v is link number i.
* laterOf_moments: laterOf (some v) = OnBytes.reqMoments v - 1.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Peel.FoPlanAtFrames

set_option autoImplicit false

namespace TwLaw
open OnBytes OnBytes.Params OnBytes.Plan

theorem groupsFrom_length (s : ReqShape) : ∀ (count l : Nat) (alive : List ReqAlive),
    (reqGroupsFrom s count l alive).length = count
  | 0, _, _ => rfl
  | count + 1, l, alive => by
    show (reqGroupsFrom s count (l + 1) (reqGroupAt s l alive).2).length + 1 = count + 1
    rw [groupsFrom_length s count]

/-- A request has one group more than it has links. -/
theorem groups_length (s : ReqShape) : (reqGroups s).toList.length = s.link.length + 1 := by
  rw [reqGroups_eq, groupsFrom_length]

/-- For every link there is a record. -/
theorem framesOf_some (z : ProofSized) (sub : Subproofs) (i : Nat)
    (hi : i < z.request.link.length) : ((framesOf z sub)[i]?).isSome = true := by
  unfold framesOf
  refine framesFrom_some z _ 0 _ _ _ i (by rw [groups_length]; omega) fun j hj => ?_
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- The record of link number i. -/
theorem framesOf_link (z : ProofSized) (sub : Subproofs) (i : Nat) (v : ReqLink)
    (hv : z.request.link[i]? = some v) :
    ∃ n, (framesOf z sub)[i]? = some n ∧ n.l = i ∧ n.link = some v ∧
      n.moments = laterOf (some v) := by
  have hi : i < z.request.link.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hv
    cases hv
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (framesOf_some z sub i hi)
  obtain ⟨a1, a2, a3⟩ := framesOf_at z sub i n hn
  exact ⟨n, hn, a1, a2.trans hv, by rw [a3, a2, hv]⟩

/-- A link's later moments, in the words of OnBytes/Iop/Req.lean. -/
theorem laterOf_moments (v : ReqLink) : laterOf (some v) = OnBytes.reqMoments v - 1 := by
  unfold laterOf OnBytes.reqMoments
  show ((v.messages.getLast?.map (·.moment + 1)).getD 0) - 1 = _
  cases v.messages.getLast? <;> rfl

end TwLaw
