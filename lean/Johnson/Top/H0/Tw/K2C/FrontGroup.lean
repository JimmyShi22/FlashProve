-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/FrontGroup.lean: the kind «the code switch»: WHAT THE FRONT OF A SWITCH DOES
TO THE STATEMENT, WRITTEN OUT: one fresh group is pushed behind the groups that stand; nothing
else of the statement turns. And what "H.0.front" (headFrontQ) leaves of the record. NO BLOCK
IMPORTS THIS FILE.
  freshGroup c m    the group { code := c, maskCode := m }
  withFresh S c m   { S with groups := S.groups.push (freshGroup c m) }
  newGroupG_is      a yes of newGroupG: S' = withFresh S c m and the new group's number is
                    S.groups.size
  firstFront_st     the statement that the front hands on: that, at the frame's shape's two codes
  fresh             the fresh group has no member, no kept mark, no open row and is in no run (the
                    structure's defaults)
  headFrontQ_st     a yes of "H.0.front": s'.st = withFresh s.st s.check.frame.shape.code
                    s.check.frame.shape.maskCode
  headFrontQ_groups so: every group that stood stands at its number as it was; there is just one
  more; codes and oracle messages are as they were
  headFrontQ_rest   and of the record: book · roots · rowsOwed · failed · check · out · req are as
                    they were («st» and «here» alone turn)
A frame fact: it reads off what the text lays. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.AsksWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (newGroupG dOf firstFront finishFront)

/-- The fresh group at two codes. -/
def freshGroup (c m : Nat) : Group := { code := c, maskCode := m }

/-- A statement with the fresh group pushed behind its groups. -/
def withFresh (S : Statement) (c m : Nat) : Statement :=
  { S with groups := S.groups.push (freshGroup c m) }

theorem newGroupG_is {S S' : Statement} {c m g : Nat} (h : newGroupG S c m = .ok (S', g)) :
    S' = withFresh S c m ∧ g = S.groups.size := by
  unfold newGroupG at h
  split at h
  · rename_i g' d hd
    cases h
    unfold Desc.Ground.newGroupP at hd
    split at hd
    · simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact ⟨rfl, rfl⟩
    · cases hd
  · cases h

theorem firstFront_st {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S f = .ok x) :
    x.st = withFresh S f.shape.code f.shape.maskCode ∧ x.f.group = S.groups.size := by
  obtain ⟨L, G, S', g, a⟩ := (_root_.Tw.K2.firstFront_iff S f x).1 h
  obtain ⟨e1, e2⟩ := newGroupG_is a.opened
  rw [a.out]
  exact ⟨e1, e2⟩

theorem fresh (c m : Nat) : (freshGroup c m).code = c ∧ (freshGroup c m).maskCode = m ∧
    (freshGroup c m).members = #[] ∧ (freshGroup c m).kept = #[] ∧ (freshGroup c m).rows = #[] ∧
    (freshGroup c m).inRun = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem headFrontQ_st {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    s'.st = withFresh s.st s.check.frame.shape.code s.check.frame.shape.maskCode := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  rw [k.out]
  exact (firstFront_st k.front).1

theorem headFrontQ_groups {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    s'.st.codes = s.st.codes ∧ s'.st.oracles = s.st.oracles ∧
      s'.st.groups.size = s.st.groups.size + 1 ∧
      (∀ i, i < s.st.groups.size → s'.st.groups[i]? = s.st.groups[i]?) ∧
      s'.st.groups[s.st.groups.size]? =
        some (freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode) := by
  rw [headFrontQ_st h]
  refine ⟨rfl, rfl, by simp [withFresh], fun i hi => ?_, by simp [withFresh]⟩
  simp [withFresh, Array.getElem?_push, Nat.ne_of_lt hi]

theorem headFrontQ_rest {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    s'.book = s.book ∧ s'.roots = s.roots ∧ s'.rowsOwed = s.rowsOwed ∧ s'.failed = s.failed ∧
      s'.check = s.check ∧ s'.out = s.out ∧ s'.req = s.req := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  have e : s₁ = s.enterHead tl := enterHeadQ k.enters
  unfold S.enterHead at e
  rw [if_pos k.between] at e
  rw [k.out, e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.newGroupG_is
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_st
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_groups
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_rest
