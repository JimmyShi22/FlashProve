-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/Stands24.lean: code switching: THE NUMBERS OF THE PLACE WHOSE SWITCH OPENS
GROUP 25 (ProofFile.pAtK2 Z 24, Johnson/Desc/ProofFile/CarryAt.lean) DO NOT STAND IN THE HEAD's DRESS:
under the test spotsFitB Z (K2Caller/PAtSeated.lean) and «25 links». NO SUB-PROTOCOL IMPORTS THIS
FILE.
  dress_head    dressOf L link is the head's only at the link L - 1
  spot_group    a member of ProofFile.k2SpotsAt Z opens the group of its link's number (the number of
                links, where it has no link)
  stands24      THE STATEMENT. Where pAtK2? answers nothing the dead numbers stand in a link's
                dress. Where it answers, the place opens group 25; its dress goes by its link (the
                test's second half); the head's dress would ask link 24, whose group is 24.
LIMITS. No scope, no opening, no test on the list of rounds is spent. spotsFitB IS A NAMED TEST THAT
THE VERIFIER DOES NOT RUN. That the dress IS the finish's lies elsewhere, in scope (k02_sits_pAt,
K2Caller/SitsAtP.lean). No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.PAtSeated
import Johnson.Top.H0.Tw.K2C.GroupAtNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.First.K2 (P2 At)

theorem dress_head {L : Nat} {link : Option Nat} (h : dressOf L link = .head) :
    ∃ l, link = some l ∧ l + 1 = L := by
  unfold dressOf at h
  split at h
  · cases h
  · rename_i l
    split at h
    · rename_i e
      exact ⟨l, rfl, by simpa using e⟩
    · cases h

theorem spot_group {Z : ProofFile.Pub} {y : ProofFile.Spot × P2} (hy : y ∈ ProofFile.k2SpotsAt Z) :
    y.2.grp = y.1.place.link.getD Z.s₀.check.frame.shape.link.length := by
  unfold ProofFile.k2SpotsAt at hy
  cases hG : ProofFile.blankBy ProofFile.pureRoad.links Z with
  | none =>
    rw [hG] at hy
    cases hy
  | some G₀ =>
    rw [hG] at hy
    have hy' : y ∈ P1K2.pureSpots Z G₀ := hy
    obtain ⟨Q, n, hQ, hn, e⟩ := spot_is hy'
    have hg : y.2.grp = n.grp := by rw [e]; rfl
    rw [hg, P1K2.numsAt_grp hn, (P1K2.prepOf_request hQ).1]

/-- **The numbers at the last switch do not stand in the head's dress.** -/
theorem stands24 {Z : ProofFile.Pub} (hT : spotsFitB Z = true)
    (hL : Z.s₀.check.frame.shape.link.length = 25) : (ProofFile.pAtK2 Z 24).stands ≠ .head := by
  unfold ProofFile.pAtK2 ProofFile.pAtK2?
  cases hf : (ProofFile.k2SpotsAt Z).find? (fun x => x.2.grp == 24 + 1) with
  | none =>
    intro h
    cases h
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hg : y.2.grp = 25 := by simpa using List.find?_some hf
    unfold spotsFitB at hT
    rw [Bool.and_eq_true] at hT
    have hD := of_decide_eq_true (List.all_eq_true.1 hT.2 y hy)
    intro h
    have h' : y.2.stands = .head := h
    rw [hD] at h'
    obtain ⟨l, hl, e⟩ := dress_head h'
    have hs := spot_group hy
    rw [hl, hg] at hs
    rw [hL] at e
    have hs' : 25 = l := hs
    omega

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.dress_head
#print axioms VerifiableInference.Desc.First.K2Caller.spot_group
#print axioms VerifiableInference.Desc.First.K2Caller.stands24
