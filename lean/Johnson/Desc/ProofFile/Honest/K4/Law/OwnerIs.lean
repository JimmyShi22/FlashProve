-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OwnerIs.lean: where K4's honest parts read a matrix of the
segment's list (`k4Owner`, Honest/K4/Part.lean) is the frame's owner's key (`ownerKeyBy`,
`ownerKey`, Honest/BorrowedOne.lean). Statements with their proofs, by unfolding.

Limits. CONDITIONAL: that the list which the key's reader gives at the owner's segment has the
matrices of the plan's own list for the owner's group is a hypothesis, asked at a borrowed entry
alone; at the public parameters also: two segments a group, and the owner's group stands below the
number of groups. Nothing shows these of any plan. Nothing on a run, a coin or a measure. Nothing on
soundness, on completeness or on any other property. No property is claimed.

  `name_at`      the name of entry i of entry og of a list of lists, read with empty entries beyond
      the lists, is the name read through options, "" beyond them.
  `k4Owner_by`   k4Owner Q mu = ownerKeyBy 2 tl Q.seg M, M the entry number mu of the group's list.
  `tlAt_even`    at two segments a group the plan's list at segment 2 og, og below the number of
      groups, is group og's.
  `k4Owner_key`  k4Owner Q mu = ownerKey X Q.seg M.

-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Honest.BorrowedOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (TMat Tail HTailF2)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc.First.Look (tlAt)

/-- A name read with empty entries beyond the lists is the name read through options. -/
theorem name_at (ts : Array Tail) (og i : Nat) :
    ((ts.getD og {}).mats.getD i {}).name =
      ((((ts[og]?).map (·.mats)).bind (·[i]?)).map (·.name)).getD "" := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases h1 : ts[og]? with
  | none => simp
  | some t =>
    simp only [Option.getD_some, Option.map_some, Option.bind_some]
    cases h2 : t.mats[i]? with
    | none => simp
    | some M => simp

/-- **K4's key is the frame's**, of the segments' lists as a parameter. CONDITIONAL. -/
theorem k4Owner_by (Q : K4Pub) (mu : Nat) (tl : Nat → Option HTailF2)
    (htl : ((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind = 1 →
      (tl (2 * (((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId / 256 - 1))).map (·.mats) =
        (Q.P.tails[((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId / 256 - 1]?).map (·.mats)) :
    k4Owner Q mu = ownerKeyBy 2 tl Q.seg ((Q.P.tails.getD Q.g {}).mats.getD mu {}) := by
  unfold k4Owner ownerKeyBy
  by_cases hk : ((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind = 1
  · have hb : (((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind == 1) = true := by simpa using hk
    rw [if_pos hb, if_pos hb]
    have e : ((tl (2 * (((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId / 256 - 1))).bind
        (·.mats[((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId % 256]?)) =
        (((tl (2 * (((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId / 256 - 1))).map (·.mats)).bind
          (·[((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId % 256]?)) := by
      cases tl (2 * (((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId / 256 - 1)) <;> rfl
    rw [e, htl hk, ← name_at]
  · have hb : ¬ (((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind == 1) = true := by simpa using hk
    rw [if_neg hb, if_neg hb]

/-- At two segments a group, segment 2 og's list is group og's. -/
theorem tlAt_even (X : OnBytes.Model.Verify.Public) (h4 : X.p4 = true) {og : Nat}
    (hog : og < X.NGr) : tlAt X (2 * og) = (X.G[og]?).map (·.tl) := by
  unfold tlAt
  have h1 : (2 * og == 2 * X.NGr) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  have h2 : (2 * og % 2 == 0) = true := by
    simp only [beq_iff_eq]
    omega
  have h3 : 2 * og / 2 = og := by omega
  simp only [h4, if_true, h1, Bool.false_eq_true, if_false, h2, h3]

/-- **K4's key is the frame's**, off the public parameters. CONDITIONAL. -/
theorem k4Owner_key (Q : K4Pub) (mu : Nat) (X : OnBytes.Model.Verify.Public) (h4 : X.p4 = true)
    (hog : ((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind = 1 →
      ((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId / 256 - 1 < X.NGr)
    (hG : ∀ og, og < X.NGr → (X.G[og]?).map (·.tl.mats) = (Q.P.tails[og]?).map (·.mats)) :
    k4Owner Q mu = ownerKey X Q.seg ((Q.P.tails.getD Q.g {}).mats.getD mu {}) := by
  unfold ownerKey
  simp only [h4, if_true]
  refine k4Owner_by Q mu (tlAt X) fun hk => ?_
  rw [tlAt_even X h4 (hog hk), ← hG _ (hog hk), Option.map_map]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.name_at
#print axioms ProofFile.Honest.K4.k4Owner_by
#print axioms ProofFile.Honest.K4.tlAt_even
#print axioms ProofFile.Honest.K4.k4Owner_key
