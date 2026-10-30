-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/SeatsOwnPromise.lean: THE SMALLNESS TEST: `K9.SeatsOwn (N.group l) p s`
(Johnson/Desc/First/Batch/SmallNear.lean: the book's seat of each message in which one of the test's
arrays lies is a seat of the segment's group) OUT OF THE FIRST TABLE'S PROMISE, IN FRONT OF THE DRAW
OF SEGMENT l, AT THE FULL SIZE. Statements with their proofs; no definition.


Main names (namespace `VerifiableInference.Desc.First.K8`).
  `member_sent`: THE CORE, in letters: under the promise's test `membersHeld N O s`, where a class
    of rows of segment m is open, its group G is made and `pin m 2` is not open: the book's place of
    a member of G is in `N.sent m 0` or `N.sent m 1`. (The step inside `sent_of_members`,
    Johnson/Desc/First/K8/SentPromise.lean, said by itself.) `sent_in_group`: `N.sent m t ⊆ N.group
    m` for t ∈ [0, 1]: by `Numbers.group`'s text.
  **`seatsOwn_of_onQ`**: from `onQ` at `drawAt l`, no mark, and, at every copy L with `s.link? =
    some L`: `FrameJoined s.st L.check.frame` (Johnson/Desc/First/K8/MsgsOfFrame.lean) and
    `L.check.frame.group = N.groupAt l`: `K9.SeatsOwn (N.group l) p s`, AT EVERY p.

Every "there is": none in the conclusion.
Of `SeatsOwn`'s own premises two are not spent: that the seat's tree is among those that the place
names, and that the book's list of that tree's parts has the message there.
WHAT IS NOT PAID HERE: `FrameJoined` and which group the copy names: facts on the verifier's state
in front of the draw.
Limits. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K8.MsgsOfFrame
import Johnson.Desc.First.Batch.SmallNear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers rowSegs membersHeld flatPlacesOf)

/-- **THE CORE**: the book's place of a member of the open group is a tenant that the segment sends
at moment 0 or 1. -/
theorem member_sent (N : Numbers) (O : List Item) (s : S) (m : ℕ) (G : Group)
    (hM : membersHeld N O s = true) (hrow : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) (h2 : O.contains (.pin m 2) = false)
    (o : ℕ) (ho : o ∈ G.members.toList) (jt : ℕ × ℕ) (hp : s.book.place[o]? = some jt) :
    ∃ t ∈ [0, 1], jt ∈ N.sent m t := by
  have h := List.all_eq_true.1 hM m hrow
  simp only [hG, Bool.and_eq_true] at h
  have h1 := (Bool.and_eq_true _ _ ▸ h.2 : _ ∧ _).1
  have hin : jt ∈ G.members.toList.filterMap fun o => s.book.place[o]? :=
    List.mem_filterMap.2 ⟨o, ho, hp⟩
  have hc := List.all_eq_true.1 h1 _ hin
  obtain ⟨t, ht, hs⟩ := List.mem_flatMap.1 (List.contains_iff_mem.1 hc)
  have ht3 : t < 3 := List.mem_range.1 ht
  by_cases hO : O.contains (.pin m t) = true
  · rw [if_pos hO] at hs
    have hne : t ≠ 2 := by
      rintro rfl
      rw [h2] at hO
      cases hO
    refine ⟨t, ?_, hs⟩
    have : t = 0 ∨ t = 1 := by omega
    rcases this with rfl | rfl <;> simp
  · rw [if_neg hO] at hs
    cases hs

/-- What a segment sends at moment 0 or 1 lies in its group. -/
theorem sent_in_group (N : Numbers) (m t : ℕ) (ht : t ∈ [0, 1]) (jt : ℕ × ℕ)
    (h : jt ∈ N.sent m t) : jt ∈ N.group m := by
  unfold Numbers.group
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact List.mem_append_left _ (List.mem_append_left _ h)
  · exact List.mem_append_left _ (List.mem_append_right _ h)

/-- **`SeatsOwn` OUT OF THE PROMISE, AT THE FULL SIZE, IN FRONT OF THE DRAW OF SEGMENT l.** -/
theorem seatsOwn_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (get : A → P × First.S) (l : ℕ) (hl : l ≤ 24) (a : A × Fr.E.Str)
    (h : onQ N Mg linksFull (flatPlacesOf linksFull true) get (drawAt l) a)
    (hm : (get a.1).2.failed = none)
    (hJ : ∀ L, (get a.1).2.link? = some L →
      FrameJoined (get a.1).2.st L.check.frame ∧ L.check.frame.group = N.groupAt l)
    (p : Par) : K9.SeatsOwn (N.group l) p (get a.1).2 := by
  intro tl L _ hL t htm o jt hto hp _ _
  obtain ⟨hJ1, hg⟩ := hJ L hL
  obtain ⟨G, hG, hmem⟩ := hJ1 o (msgs_own_or_kept tl L o (Named.mem_msgs.2 ⟨t, htm, hto⟩))
  rw [hg] at hG
  obtain ⟨t', ht', hs⟩ := member_sent N _ _ l G (membersHeld_of_onQ N Mg _ _ get _ a h hm)
    (front_open_full l hl).1 hG (front_open_full l hl).2 o hmem jt hp
  exact sent_in_group N l t' ht' jt hs

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.member_sent
#print axioms VerifiableInference.Desc.First.K8.sent_in_group
#print axioms VerifiableInference.Desc.First.K8.seatsOwn_of_onQ
