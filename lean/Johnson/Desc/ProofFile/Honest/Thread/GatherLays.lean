-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherLays.lean: the column `hl` of `owesS_head_form`
(Thread/GatherHeadForm.lean) at the list of rider clauses `csHead` (Thread/CsHead.lean), split by
clause. The column asks, for each clause of the list, that the sub-protocol just before the clause's
first border establishes the clause's fact (`LaysAtS`, Thread/SharesS.lean). The list has 55
clauses: seven written ones and three families. The equation "the clause begins at border `b + 1`"
fixes `b`, so ten hypotheses are enough. GatherStays.lean does the same for the column `hst`. No
definition.

  `csHead_lays`   at any `Thread` over the first chain's states and any `Said`: the column `hl`,
  from `LaysAtS` at the sub-protocols 341, 342, 343, 345 (three clauses), 346, `14 * l + 8`
  (`l < 24`), `14 * (2 * g + 1) + 3` and `28 * g + 4` (`g < 12`)

Limits.
  * Each of the ten hypotheses has to be shown by the authors of the lemmas on the kind of the
    sub-protocol that it names. This file shows none of them.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S)

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **The column `hl` at `csHead`, from one hypothesis for each written clause and each family.** -/
theorem csHead_lays {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (hx : LaysAtS T Said 341 (riderHead 342 347 fun a => a.x.isSome = true))
    (ht : LaysAtS T Said 342 (riderHead 343 348 fun a => a.t.isSome = true))
    (hwo : LaysAtS T Said 346 (riderHead 347 352 fun a => a.wo.isSome = true))
    (hnx : LaysAtS T Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hf0 : LaysAtS T Said 343 (riderHead 344 345 fun a => a.tl.foldDrawn = 0))
    (hf1 : LaysAtS T Said 345 (riderHead 346 347 fun a => a.tl.foldDrawn = 1))
    (hs : LaysAtS T Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hst : ∀ l, l < 24 →
      LaysAtS T Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 → LaysAtS T Said (14 * (2 * g + 1) + 3)
      (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g))
    (hown : ∀ g, g < 12 → LaysAtS T Said (28 * g + 4)
      ⟨28 * g + 5, 28 * g + 10, fun _ _ s => ∃ o, s.own? = some o⟩) :
    ∀ b, ∀ c ∈ csHead ν st R, c.lo = b + 1 → LaysAtS T Said b c := by
  intro b c hc e
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  · have e' : 342 = b + 1 := e
    obtain rfl : b = 341 := by omega
    exact hx
  · have e' : 343 = b + 1 := e
    obtain rfl : b = 342 := by omega
    exact ht
  · have e' : 347 = b + 1 := e
    obtain rfl : b = 346 := by omega
    exact hwo
  · have e' : 346 = b + 1 := e
    obtain rfl : b = 345 := by omega
    exact hnx
  · have e' : 344 = b + 1 := e
    obtain rfl : b = 343 := by omega
    exact hf0
  · have e' : 346 = b + 1 := e
    obtain rfl : b = 345 := by omega
    exact hf1
  · have e' : 346 = b + 1 := e
    obtain rfl : b = 345 := by omega
    exact hs
  · have e' : 14 * l + 9 = b + 1 := e
    obtain rfl : b = 14 * l + 8 := by omega
    exact hst l hl
  · have e' : 14 * (2 * g + 1) + 4 = b + 1 := e
    obtain rfl : b = 14 * (2 * g + 1) + 3 := by omega
    exact hatt g hg
  · have e' : 28 * g + 5 = b + 1 := e
    obtain rfl : b = 28 * g + 4 := by omega
    exact hown g hg

end ProofFile.Honest

#print axioms ProofFile.Honest.csHead_lays
