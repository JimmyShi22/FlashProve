-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MomentsCount.lean: A LINK's MESSAGES, COUNTED BY MOMENT: where the shape
lists them by moment (`reqMomentsOk`, OnBytes/Iop/Req.lean) and the link has at most three moments
(`reqMoments`), the messages of the moments 0, 1 and 2 are all of them. On lists alone. Theorems. It
changes no other file.

  `le_last`: listed by moment, no message has a greater moment than the last (by
    `moments_ge`, Johnson/Desc/First/K8/LawBookNames.lean).
  `moment_lt`: so every message's moment is below `reqMoments` of the link.
  `count_three`: every moment below 3 ⊢ the three counts add up to the list's length.
  `count_link`: **reqMomentsOk 0 L.messages = true · reqMoments L ≤ 3 ⊢ the three counts add up to
    L.messages.length.**
Limits. That a link of the first chain's shape has at most three moments is not said here. Nothing
on soundness.
-/
import Johnson.Desc.First.K8.LawBookNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Params (ReqMessage ReqLink)
open VerifiableInference.Desc.First.K8.Named (moments_ge)

theorem le_last : ∀ (t : ℕ) (ms : List ReqMessage), reqMomentsOk t ms = true →
    ∀ z, ms.getLast? = some z → ∀ m ∈ ms, m.moment ≤ z.moment
  | _, [], _, _, _, _, h => nomatch h
  | t, m0 :: ms, hk, z, hz, m, hm => by
    simp only [reqMomentsOk, Bool.and_eq_true] at hk
    cases ms with
    | nil =>
      obtain rfl : m0 = z := by simpa using hz
      obtain rfl : m = m0 := by simpa using hm
      exact Nat.le_refl _
    | cons m1 ms' =>
      have hz' : (m1 :: ms').getLast? = some z := by
        rw [List.getLast?_cons_cons] at hz
        exact hz
      rcases List.mem_cons.1 hm with rfl | hm
      · obtain ⟨j, hj⟩ := List.getElem?_of_mem (List.mem_of_getLast? hz')
        exact moments_ge _ _ hk.2 j z hj
      · exact le_last _ _ hk.2 z hz' m hm

theorem moment_lt {L : ReqLink} (hk : reqMomentsOk 0 L.messages = true) :
    ∀ m ∈ L.messages, m.moment < reqMoments L := by
  intro m hm
  unfold reqMoments
  cases e : L.messages.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at e
    rw [e] at hm
    exact nomatch hm
  | some z =>
    have := le_last 0 _ hk z e m hm
    show m.moment < z.moment + 1
    omega

theorem count_three : ∀ (ms : List ReqMessage), (∀ m ∈ ms, m.moment < 3) →
    (ms.filter fun m => m.moment == 0).length + (ms.filter fun m => m.moment == 1).length +
      (ms.filter fun m => m.moment == 2).length = ms.length
  | [], _ => rfl
  | m0 :: ms, h => by
    have ih := count_three ms fun m hm => h m (List.mem_cons_of_mem _ hm)
    have h0 := h m0 List.mem_cons_self
    simp only [List.filter_cons, List.length_cons]
    obtain e | e | e : m0.moment = 0 ∨ m0.moment = 1 ∨ m0.moment = 2 := by omega
    all_goals
      simp only [e]
      simp
      omega

theorem count_link {L : ReqLink} (hk : reqMomentsOk 0 L.messages = true)
    (h3 : reqMoments L ≤ 3) :
    (L.messages.filter fun m => m.moment == 0).length +
      (L.messages.filter fun m => m.moment == 1).length +
      (L.messages.filter fun m => m.moment == 2).length = L.messages.length :=
  count_three _ fun m hm => Nat.lt_of_lt_of_le (moment_lt hk m hm) h3

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.le_last
#print axioms VerifiableInference.Desc.LinkJoin.moment_lt
#print axioms VerifiableInference.Desc.LinkJoin.count_three
#print axioms VerifiableInference.Desc.LinkJoin.count_link
