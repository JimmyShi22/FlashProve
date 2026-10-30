--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/BaseOfLot.lean: what a member of `base` is, the list of sub-protocols
that `chainBy` is handed for the first chain of the proof file's IOP as written in Lean. Theorems
only; no file of that IOP imports this one.
Why. FirstSame.lean says that what the driver's structure gives at a place is a member of `base` at
that place, or that member with something joined after it. A law on one kind's sub-protocol, such as
"the one at the place of the kind K7 hears the reply once", speaks of a lot's own sub-protocol.
Between the two stands the text of `partsAt` (OnlineDescriptionFromBlockTables.lean), which is opened here.
  `places_of_lot`   where `partsAt T B` has a sub-protocol at a place `p` of its list: a lot
                    supplies the batching as a function at `p.place`; or it is
                    `{ guardMark b₁ with name := p.name }`, where `b₁` is a sub-protocol, at
                    `p.place`, of a lot of `B.all` that does not depend on the request
  `base_of_lot`     the same of every member of `base`
Both are unfoldings: they say how the value was computed. What `guardMark` does, which lots stand
in `B.all`, and at which places a lot supplies the batching are not said here.

-/
import Johnson.Desc.ProofFile.Law.MarkGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First

theorem places_of_lot (T : PureSeat) (B : PureBase) :
    ∀ x ∈ (partsAt T B).places, ∀ b, x.2 = .ok b → x.1 ∈ B.spots ∧
      ((∃ L ∈ T.lots, ∃ mk, L.batch B.G₀ x.1.place = some mk) ∨
        ∃ y ∈ B.all, ∃ b₁ ∈ y.2, b₁.place = x.1.place ∧ y.1.letters = false ∧
          b = { guardMark b₁ with name := x.1.name }) := by
  intro x hx b hb
  unfold partsAt at hx
  dsimp only at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  refine ⟨hp, ?_⟩
  dsimp only at hb ⊢
  split at hb
  · obtain ⟨mk', h1, _⟩ := Option.map_eq_some_iff.1 (by assumption)
    obtain ⟨mk, h2, _⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨L, hL, h3⟩ := List.exists_of_findSome?_eq_some h2
    exact .inl ⟨L, (List.mem_filter.1 hL).1, mk, h3⟩
  · have hy := List.mem_of_find?_eq_some (by assumption)
    have hq := List.find?_some (by assumption)
    obtain ⟨z, hz1, hz2⟩ := List.mem_filterMap.1 hy
    obtain ⟨bL, hbL, e2⟩ := Option.map_eq_some_iff.1 hz2
    subst e2
    have hbp : bL.place = p.place :=
      eq_of_beq (List.find?_some (p := fun b : Block S Cl => b.place == p.place) hbL)
    have hl : z.1.letters = false := by
      simp at hq
      exact hq.1
    exact .inr ⟨z, hz1, bL, List.mem_of_find?_eq_some hbL, hbp, hl, (Except.ok.inj hb).symm⟩
  · split at hb <;> cases hb

/-- **A member of `base` is a lot's own sub-protocol behind `guardMark`, under the place's name**,
but where a lot supplies the batching as a function. -/
theorem base_of_lot {T : PureSeat} {B : PureBase} {base : List (Block S Cl)}
    (hb : (partsAt T B).base = .ok base) :
    ∀ b ∈ base, ∃ p ∈ B.spots,
      (∃ L ∈ T.lots, ∃ mk, L.batch B.G₀ p.place = some mk) ∨
        ∃ y ∈ B.all, ∃ b₁ ∈ y.2, b₁.place = p.place ∧ y.1.letters = false ∧
          b = { guardMark b₁ with name := p.name } := by
  intro b hbm
  obtain ⟨x, hx, e⟩ := mapM_ok_mem _ _ _ hb b hbm
  obtain ⟨hp, h⟩ := places_of_lot T B x hx b e
  exact ⟨x.1, hp, h⟩

end ProofFile.Law

#print axioms ProofFile.Law.places_of_lot
#print axioms ProofFile.Law.base_of_lot
