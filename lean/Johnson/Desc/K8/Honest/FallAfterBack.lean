-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallAfterBack.lean: WHERE NO ENTRY OF THE VECTOR OF READS HAS THE WEIGHT 0
BEHIND THE BATCHING BLOCK, `selfUnits` SAYS YES AT THE DATA AND THE LEDGER THAT "K8.tests" READS, AT
A FEED-FORWARD SEGMENT. Statements and proofs. No prover. Lemmas; none of the library's goals.
NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

The other way round than Johnson/Desc/K8/Honest/FallAfter.lean's `behind_layers`.
  `selfUnits_eq`   at a state that holds data tl and a ledger F: `selfUnits tl nU F` is the negation
      of `zeroUnitAt nU` at that state
  **`units_pass_layers`**   t: the state behind the batching block; z₁, z₂: what the runs that the
      segment's blocks state at "K8.lsTail" and "free-slot" return, one after the other. If
      `zeroUnitAt nU t` is false, `selfUnits` says yes at the data and the ledger that z₂ holds:
      those that the kind's own run "K8.tests" reads (Johnson/Desc/First/Batch/Law/K8Tests.lean:
      k8Tests)
WHICH RUN STANDS AT WHICH ENTRY IS A PREMISE, up to a guard: `LayersTies`.
Limits. One of the conjuncts of one of the tests of "K8.tests": that the run says yes is not said.
The ties go one way (a yes of the stated run is a yes of the kind's own): that the stated run says
yes where the kind's own does is not said. At a feed-forward segment alone.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallAfter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

theorem selfUnits_eq (nU : Array Nat) (s : S) (tl : HTailF2) (F : Fork) (h1 : s.tl? = some tl)
    (h2 : s.fork? = some F) : selfUnits tl nU F = !zeroUnitAt nU s := by
  rw [zeroUnitAt_eq nU s tl F h1 h2]
  unfold zeroUnit
  rw [Bool.not_not]

/-- **The conjunct passes at the call.** -/
theorem units_pass_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU) (t z₁ z₂ : S) (r₁ r₂ : S → Except String S)
    (a₁ : LinkJoin.AtAfter L (4, "K8.lsTail") r₁) (a₂ : LinkJoin.AtAfter L (2, "free-slot") r₂)
    (y₁ : r₁ t = .ok z₁) (y₂ : r₂ z₁ = .ok z₂) (h : zeroUnitAt nU t = false) (tl : HTailF2)
    (F : Fork) (h1 : z₂.tl? = some tl) (h2 : z₂.fork? = some F) : selfUnits tl nU F = true := by
  have e1 := zeroUnitAt_lsTail nU t z₁ (ties.tLs r₁ a₁ _ _ y₁)
  obtain ⟨q2, l2, u2⟩ := ties.tFree r₂ a₂
  obtain ⟨a, w2⟩ := OnBytes.Desc.First.K4.freeSlotAtS l2 (u2 _ _ y₂)
  have e2 := zeroUnitAt_wrote nU z₁ z₂ a w2
  rw [selfUnits_eq nU z₂ tl F h1 h2, e2, e1, h]
  rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.selfUnits_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.units_pass_layers
