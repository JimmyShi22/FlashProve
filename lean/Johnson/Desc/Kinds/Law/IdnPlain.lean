-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/IdnPlain.lean: THE PART "idn" OF THE OUTPUT HEAD's RELATION ON CELLS AS A SENTENCE ON THE SIZES, THE POLICY, THE REQUEST AND THE CELLS ALONE: Law/RowFront.lean's FrontIdn begins "there are letters g that given returns at the record", and its sums are typed at g's letters, the heard token and the lookup's points among them: SO IT CANNOT RIDE BACK PAST THE
LOOKUP's BLOCK, in front of which given refuses, while the table's item is open from the chain's start. HERE: IdnPlain, which reads no record, no token and no point of the lookup, AND: FrontIdn GIVES IT: STATED AND PROVED.
  IdnPlain sz pol rq c   at every position's corner the row's 17 forms are 0; the two plain sums, WRITTEN OUT AS SUMS OF INTEGERS READ IN THE FIELD (Law/Values.lean's rd_mean | rd_count's right sides), are 0.
  idnPlain_of_front      FrontIdn p L s c → IdnPlain p.sizes p.policy (L.request s) c.
  given_three          the sizes, the policy and the request of the letters that given returns are the plan's and the record's.
WHAT IT DOES NOT SAY. The way back (IdnPlain and "given returns" give FrontIdn) is not typed. That L.request s is the same at all records of the chain: the request's field is laid at the start and no function of State.lean writes it later (its own comment): no law here. All that Law/RowFront.lean does not say. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Norm (lt ls d lPd S2 T)

/-- **"idn", on the sizes, the policy, the request and the cells alone.** -/
def IdnPlain (sz : Sizes) (pol : Policy) (rq : Request) (c : NCells) : Prop :=
  letI := sz
  letI := pol
  letI := rq
  (∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0) ∧
  ((((Finset.range T).sum (fun t =>
    if costed t = true then numZ c.toCells .paid t + (C : Int) * numZ c.toCells .over t
      + numZ c.toCells .slackMean t
    else 0) - (theta : Int) * (RC : Int) : Int) : K) = 0) ∧
  ((((Finset.range T).sum (fun t =>
    if costed t = true then numZ c.toCells .over t + numZ c.toCells .slackCap t else 0)
      - ((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K) = 0)

namespace Came

/-- The sizes, the policy and the request of the letters that given returns. -/
theorem given_three {S : Type} {p : Par} {L : Seat S} {s : S} {g : Given}
    (h : given p L s = .ok g) :
    g.sizes = p.sizes ∧ g.policy = p.policy ∧ g.request = L.request s := by
  unfold given at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩

theorem idnPlain_of_front {S : Type} (p : Par) (L : Seat S) (s : S) (c : NCells)
    (h : FrontIdn p L s c) : IdnPlain p.sizes p.policy (L.request s) c := by
  obtain ⟨g, hg, hrows, hm, hc⟩ := h
  obtain ⟨e1, e2, e3⟩ := given_three hg
  rw [← e1, ← e2, ← e3]
  refine ⟨hrows, ?_, ?_⟩
  · have h1 := congrArg rd hm
    rw [rd_mean, rd_zero] at h1
    exact h1
  · have h1 := congrArg rd hc
    rw [rd_count, rd_zero] at h1
    exact h1

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.given_three
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.idnPlain_of_front
