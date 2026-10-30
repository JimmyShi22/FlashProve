-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/FinFront.lean: the kind «the code switch»: WHAT "F.0.front" (finishFrontQ)
LAYS INTO THE FINISH's OWN PART OF THE RECORD, WRITTEN OUT. In the seat at «F:1» that step is the
way in to the switch: so these are facts on the very record at which the kind's law reads its
front. NO BLOCK IMPORTS THIS FILE.
  finishFront_st    the statement that the front hands on: one fresh group pushed; the frame's
                    group is its number
  finishFrontQ_st   a yes of "F.0.front": t.st = withFresh s.st ‹the shape's two codes›
  finishFrontQ_fr   t.here = .fin a with a.G = some G · a.fr.groups[a.fr.link]? = some G ·
                    a.fr.link = the number of the shape's links · a.fr's shape, link and groups
                    are s.check.frame's · moment 1 · no own message · a.fr.group =
                    s.st.groups.size
  finishFrontQ_rest book · roots · rowsOwed · failed · check · out · req as they were
A frame fact. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.FrontGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (newGroupG finishFront)

theorem finishFront_st {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : finishFront S f = .ok x) :
    x.st = withFresh S f.shape.code f.shape.maskCode ∧ x.f.group = S.groups.size := by
  obtain ⟨G, S', g, a⟩ := (_root_.Tw.K2.finishFront_iff S f x).1 h
  obtain ⟨e1, e2⟩ := newGroupG_is a.opened
  rw [a.out]
  exact ⟨e1, e2⟩

theorem finishFrontQ_st {s t : S} (h : finishFrontQ s = .ok t) :
    t.st = withFresh s.st s.check.frame.shape.code s.check.frame.shape.maskCode := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s t).1 h
  rw [k.out]
  exact (finishFront_st k.front).1

theorem finishFrontQ_fr {s t : S} (h : finishFrontQ s = .ok t) :
    ∃ (a : FinOwn) (G : ReqGroup), t.here = .fin a ∧ a.G = some G ∧
      a.fr.groups[a.fr.link]? = some G ∧ a.fr.link = a.fr.shape.link.length ∧
      a.fr.shape = s.check.frame.shape ∧ a.fr.link = s.check.frame.link ∧
      a.fr.groups = s.check.frame.groups ∧ a.fr.moment = 1 ∧ a.fr.own = #[] ∧
      a.fr.group = s.st.groups.size := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s t).1 h
  obtain ⟨G', S', g, fa⟩ := (_root_.Tw.K2.finishFront_iff _ _ _).1 k.front
  have hg := (finishFront_st k.front).2
  refine ⟨{ a with G := some G, fr := x.f }, G, by rw [k.out], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hg⟩
  · show x.f.groups[x.f.link]? = some G
    rw [fa.out]
    exact k.group
  · show x.f.link = x.f.shape.link.length
    rw [fa.out]
    exact fa.last
  · show x.f.shape = _
    rw [fa.out]
  · show x.f.link = _
    rw [fa.out]
  · show x.f.groups = _
    rw [fa.out]
  · show x.f.moment = 1
    rw [fa.out]
  · show x.f.own = #[]
    rw [fa.out]

theorem finishFrontQ_rest {s t : S} (h : finishFrontQ s = .ok t) :
    t.book = s.book ∧ t.roots = s.roots ∧ t.rowsOwed = s.rowsOwed ∧ t.failed = s.failed ∧
      t.check = s.check ∧ t.out = s.out ∧ t.req = s.req := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s t).1 h
  have e : s₁ = s.enterFin := ((S.unmarked_ok _ _).1 k.enters).1.symm
  unfold S.enterFin at e
  rw [if_pos k.between] at e
  rw [k.out, e]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_st
#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_fr
#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_rest
