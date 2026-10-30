-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherStays.lean: the column `hst` of `owesS_of_shares`
(Gather.lean) at the written list of rider clauses `csHead` (CsHead.lean). The column asks `StaysBy`
(Riders.lean) for every clause of the list and every sub-protocol number `b` such that the clause's
span contains `b` and `b + 1`: 138 pairs. Here they are asked in eight families. No definition.

  `hx`, `ht`, `hwo`, `hf0`, `hf1`, `hs`   the six clauses on the output head's segment whose span
       has more than one border, each at the sub-protocols inside its span
  `hatt`   in each attention segment: five sub-protocols leave the field `g` as it is
  `hlay`   in each feed-forward segment: five sub-protocols leave the field `own` as it is

  1  `csHead_stays`   the lemma

The clause on `F.next` and the 24 clauses `st l` have a span of one border, so no sub-protocol lies
inside it.

Limits.
  * A conditional lemma on this folder's own definitions. Nothing shows that a hypothesis holds at
    any `Thread`.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S)

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **Every clause of `csHead` survives every sub-protocol inside its span**, from eight families
of hypotheses. -/
theorem csHead_stays {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (hx : ∀ b, 342 ≤ b → b + 1 ≤ 347 →
      StaysBy T b (riderHead 342 347 fun a => a.x.isSome = true))
    (ht : ∀ b, 343 ≤ b → b + 1 ≤ 348 →
      StaysBy T b (riderHead 343 348 fun a => a.t.isSome = true))
    (hwo : ∀ b, 347 ≤ b → b + 1 ≤ 352 →
      StaysBy T b (riderHead 347 352 fun a => a.wo.isSome = true))
    (hf0 : ∀ b, 344 ≤ b → b + 1 ≤ 345 →
      StaysBy T b (riderHead 344 345 fun a => a.tl.foldDrawn = 0))
    (hf1 : ∀ b, 346 ≤ b → b + 1 ≤ 347 →
      StaysBy T b (riderHead 346 347 fun a => a.tl.foldDrawn = 1))
    (hs : ∀ b, 346 ≤ b → b + 1 ≤ 347 → StaysBy T b ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hatt : ∀ g, g < 12 → ∀ b, 14 * (2 * g + 1) + 4 ≤ b → b + 1 ≤ 14 * (2 * g + 1) + 9 →
      ∀ s s', T.keeps b s s' → ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g)
    (hlay : ∀ g, g < 12 → ∀ b, 28 * g + 5 ≤ b → b + 1 ≤ 28 * g + 10 →
      ∀ s s', T.keeps b s s' → ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own) :
    ∀ b, ∀ c ∈ csHead ν st R, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c := by
  intro b c hc h1 h2
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  · exact hx b h1 h2
  · exact ht b h1 h2
  · exact hwo b h1 h2
  · have a1 : 346 ≤ b := h1
    have a2 : b + 1 ≤ 346 := h2
    omega
  · exact hf0 b h1 h2
  · exact hf1 b h1 h2
  · exact hs b h1 h2
  · have a1 : 14 * l + 9 ≤ b := h1
    have a2 : b + 1 ≤ 14 * l + 9 := h2
    omega
  · exact staysBy_att_read T (fun a => a.g) (R := R g) (hatt g hg b h1 h2)
  · exact staysBy_own T (hlay g hg b h1 h2)

end ProofFile.Honest

#print axioms ProofFile.Honest.csHead_stays
