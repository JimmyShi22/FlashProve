-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/K8AtSeat.lean: THE SMALLNESS TEST: THE PREMISE `K8At` OF THE LAW ON
THE COUNTS IN FRONT OF THE BATCHING (Johnson/Desc/ProofFile/Honest/K8/CountsFrontK8.lean) PAID AT A
LINK THAT HAS ITS SORT's ORDERS AND WHOSE HEARING BLOCK AT THE KIND's ENTRY IS LAID ALONE OVER THE
KIND's BLOCK, WHOLE: the kind's entry stands in the order, and the run that the link's blocks state
there is the kind's own under the seat's guard, which only refuses more. Lemmas on the verifier's
own text; none of the library's goals.

  `lookup_map`   what a list of named things yields under a name, where each thing was wrapped by g
  `claims_of_alone`   a block laid alone states the lot's block's runs of claims, each under the
                   seat's guard
  **`k8At_of_alone`**   k8Entry k ∈ Lk.order → Lk.hear[(k8Entry k).1]? = some b → b is laid alone
                   over K8.whole pW → K8At Lk k pW
  `entry_layers`, `entry_attention`, `entry_head`   the kind's entry stands in the order of a
                   segment of each sort
Limits. That a description's link has these two properties is the library's (`IM.k8_of_layers`,
`IM.k8_of_attention`, `IM.k8_of_head`, Johnson/IMR/K8Seat.lean; `LinkJoin.SegAt`): not called here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.CountsFrontK8
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest.K9 (claimsRunOf RunUnder k8Entry guardedRun guardedRun_under ClaimsRun)

/-- What a list of named things yields under a name, where each thing was wrapped by g. -/
theorem lookup_map {β γ : Type} (g : β → γ) : ∀ (l : List (String × β)) (n : String) (y : γ),
    (l.map fun c => (c.1, g c.2)).lookup n = some y → ∃ r, (n, r) ∈ l ∧ y = g r
  | [], n, y, h => by simp at h
  | c :: l, n, y, h => by
    rw [List.map_cons, List.lookup_cons] at h
    cases hk : (n == c.1) with
    | true =>
      rw [hk] at h
      have e : n = c.1 := by simpa using hk
      exact ⟨c.2, by rw [e]; exact List.mem_cons_self, (Option.some.inj h).symm⟩
    | false =>
      rw [hk] at h
      obtain ⟨r, hr, e⟩ := lookup_map g l n y h
      exact ⟨r, List.mem_cons_of_mem _ hr, e⟩

/-- A block laid alone states the lot's block's runs of claims, each under the seat's guard. -/
theorem claims_of_alone {b b' : Block S Claim} {name : String} {a : Place}
    (h : IM.LaidAlone ProofFile.sameReply b b' name a) :
    b.claims = b'.claims.map fun c => (c.1, guardedRun ProofFile.sameReply c.2) :=
  (congrArg (·.claims) h).trans rfl

/-- **The premise, at a link whose block at the kind's entry is laid alone.** -/
theorem k8At_of_alone {Lk : Link S Claim} {k : Desc.K9.SegSort} {pW : K8.ParW}
    {b : Block S Claim} {name : String} {a : Place} (ho : k8Entry k ∈ Lk.order)
    (hb : Lk.hear[(k8Entry k).1]? = some b)
    (la : IM.LaidAlone ProofFile.sameReply b (K8.whole pW) name a) : K8At Lk k pW := by
  refine ⟨ho, fun run hr => ?_⟩
  have hn : (k8Entry k).2 = "K8.equations" := by cases k <;> rfl
  unfold claimsRunOf at hr
  rw [hb, hn] at hr
  have hr' : b.claims.lookup "K8.equations" = some run := hr
  rw [claims_of_alone la] at hr'
  obtain ⟨r, hm, rfl⟩ := lookup_map (guardedRun ProofFile.sameReply) _ _ _ hr'
  exact ⟨r, hm, guardedRun_under ProofFile.sameReply r⟩

theorem entry_layers {l : Nat} {Lk : Link S Claim} (h : LinkJoin.SegAt l .layers Lk) :
    k8Entry .layers ∈ Lk.order := by
  rw [h.order]
  simp [First.orderOf, First.orderCuts, k8Entry]

theorem entry_attention {l : Nat} {Lk : Link S Claim} (h : LinkJoin.SegAt l .attention Lk) :
    k8Entry .attention ∈ Lk.order := by
  rw [h.order]
  simp [First.orderOf, First.orderCuts, k8Entry]

theorem entry_head {l : Nat} {Lk : Link S Claim} (h : LinkJoin.SegAt l .head Lk) :
    k8Entry .head ∈ Lk.order := by
  rw [h.order]
  simp [First.orderOf, First.orderCuts, k8Entry]

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.lookup_map
#print axioms ProofFile.Honest.K8.claims_of_alone
#print axioms ProofFile.Honest.K8.k8At_of_alone
#print axioms ProofFile.Honest.K8.entry_layers
#print axioms ProofFile.Honest.K8.entry_attention
#print axioms ProofFile.Honest.K8.entry_head
