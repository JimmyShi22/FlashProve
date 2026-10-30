-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/AliveAt.lean: WHICH ORACLE MESSAGES OF EARLIER LINKS ARE STILL KEPT IN
FRONT OF A LINK's GROUP, BY THE TEXT `reqGroups` (OnBytes/Iop/Req.lean): a message number i of link
born whose life reaches link l stands in group l's list `born`, at a place below the number of the
group's kept targets. By the make: definitions and theorems on that text alone. It changes no
other file.

  `aliveFrom s l₀ al j`: the list «alive» j groups on. `aliveAt s l`: in front of group l.
  `from_get`, `groups_get`: group number l of `reqGroups s` is `reqGroupAt s l (aliveAt s l)`'s.
  `alive_mem`: **born < l · s.link[born]? = some L · L.messages[i]? = some m · l - born ≤ m.life ⊢
    some a of aliveAt s l has a.born = (born, i)** (and a.left = m.life - (l - 1 - born)).
  `born_at`: **so, at l ≤ s.link.length: (born, i) is a member of ((reqGroups s).getD l {}).born,
    and that list is as long as the group's target's list of kept** (the latter:
    `groupAt_kept`, Johnson/Desc/First/Att/K05KeptBorn.lean; what `reqGroupAt` hands on:
    `reqGroupAt_alive`, OnBytes/Params/Fit/TreesReq.lean).
Limits. One direction alone: that nothing else is alive, and that no pair stands twice, is not
said. Nothing on soundness.
-/
import OnBytes.Params.Fit.TreesReq
import Johnson.Desc.First.Att.K05KeptBorn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape)

/-- The list «alive» j groups on from group l₀. -/
def aliveFrom (s : ReqShape) : (l₀ : Nat) → List ReqAlive → Nat → List ReqAlive
  | _, al, 0 => al
  | l₀, al, j + 1 => aliveFrom s (l₀ + 1) (reqGroupAt s l₀ al).2 j

/-- In front of group l. -/
def aliveAt (s : ReqShape) (l : Nat) : List ReqAlive := aliveFrom s 0 [] l

theorem aliveFrom_succ (s : ReqShape) : ∀ (j l₀ : Nat) (al : List ReqAlive),
    aliveFrom s l₀ al (j + 1) = (reqGroupAt s (l₀ + j) (aliveFrom s l₀ al j)).2
  | 0, _, _ => rfl
  | j + 1, l₀, al => by
    show aliveFrom s (l₀ + 1) (reqGroupAt s l₀ al).2 (j + 1) = _
    rw [aliveFrom_succ s j (l₀ + 1)]
    show _ = (reqGroupAt s (l₀ + (j + 1)) (aliveFrom s (l₀ + 1) (reqGroupAt s l₀ al).2 j)).2
    rw [show l₀ + 1 + j = l₀ + (j + 1) by omega]

theorem aliveAt_succ (s : ReqShape) (l : Nat) :
    aliveAt s (l + 1) = (reqGroupAt s l (aliveAt s l)).2 := by
  unfold aliveAt
  rw [aliveFrom_succ, Nat.zero_add]

theorem from_get (s : ReqShape) : ∀ (count l₀ : Nat) (al : List ReqAlive) (j : Nat), j < count →
    (reqGroupsFrom s count l₀ al)[j]? = some (reqGroupAt s (l₀ + j) (aliveFrom s l₀ al j)).1
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | count + 1, l₀, al, 0, _ => rfl
  | count + 1, l₀, al, j + 1, h => by
    show (reqGroupsFrom s count (l₀ + 1) (reqGroupAt s l₀ al).2)[j]? = _
    rw [from_get s count (l₀ + 1) _ j (by omega), show l₀ + 1 + j = l₀ + (j + 1) by omega]
    rfl

theorem groups_get (s : ReqShape) {l : Nat} (hl : l ≤ s.link.length) :
    (reqGroups s).getD l {} = (reqGroupAt s l (aliveAt s l)).1 := by
  rw [reqGroups_eq, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    from_get s _ 0 [] l (by omega), Nat.zero_add]
  rfl

/-- **A MESSAGE WHOSE LIFE REACHES LINK l IS ALIVE IN FRONT OF GROUP l.** -/
theorem alive_mem (s : ReqShape) {born i : Nat} {L : ReqLink} {m : ReqMessage}
    (hL : s.link[born]? = some L) (hm : L.messages[i]? = some m) :
    ∀ l, born < l → l - born ≤ m.life →
      ∃ a ∈ aliveAt s l, a.born = (born, i) ∧ a.left = m.life - (l - 1 - born)
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | l + 1, h, hlife => by
    rw [aliveAt_succ, Params.reqGroupAt_alive]
    by_cases hb : born = l
    · subst hb
      refine ⟨{ shape := m.shape, leafClass := m.leafClass, left := m.life, born := (born, i) },
        List.mem_append_right _ (List.mem_filterMap.2 ⟨(m, i), ?_, ?_⟩), rfl, by
          show m.life = m.life - (born + 1 - 1 - born)
          omega⟩
      · rw [hL]
        exact List.mk_mem_zipIdx_iff_getElem?.2 hm
      · have h0 : (m.life == 0) = false := by
          rw [beq_eq_false_iff_ne]
          omega
        show (if (m.life == 0) = true then none else some _) = some _
        rw [h0]
        rfl
    · obtain ⟨a, ha, e1, e2⟩ := alive_mem s hL hm l (by omega) (by omega)
      refine ⟨{ a with left := a.left - 1 }, List.mem_append_left _ (List.mem_map.2
        ⟨a, List.mem_filter.2 ⟨ha, by
          rw [decide_eq_true_eq, e2]
          omega⟩, rfl⟩), e1, by
        show a.left - 1 = m.life - (l + 1 - 1 - born)
        rw [e2]
        omega⟩

/-- **IN GROUP l's LIST OF WHAT ITS KEPT TARGETS WERE BORN AS.** -/
theorem born_at (s : ReqShape) {born i l : Nat} {L : ReqLink} {m : ReqMessage}
    (hL : s.link[born]? = some L) (hm : L.messages[i]? = some m) (hb : born < l)
    (hlife : l - born ≤ m.life) (hl : l ≤ s.link.length) :
    (born, i) ∈ ((reqGroups s).getD l {}).born.toList ∧
      ((reqGroups s).getD l {}).born.size = ((reqGroups s).getD l {}).target.kept.size := by
  rw [groups_get s hl]
  obtain ⟨a, ha, e, _⟩ := alive_mem s hL hm l hb hlife
  refine ⟨?_, (First.Att.P.groupAt_kept s l (aliveAt s l)).symm⟩
  show (born, i) ∈ ((aliveAt s l).map (·.born)).toArray.toList
  exact List.mem_map.2 ⟨a, ha, e⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.groups_get
#print axioms VerifiableInference.Desc.LinkJoin.alive_mem
#print axioms VerifiableInference.Desc.LinkJoin.born_at
