-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallAfterAll.lean: BETWEEN THE ADDING AND THE SMALLNESS TEST's OWN TESTS
NOTHING TURNS WHAT `selfUnits` READS, AT AN ATTENTION SEGMENT AND AT THE HEAD's: BOTH WAYS.
Statements and proofs. No prover. Lemmas; none of the library's goals. NOTHING IS CLAIMED ON
COMPLETENESS, SOUNDNESS OR HIDING.

The like of Johnson/Desc/K8/Honest/FallAfter.lean (`behind_layers`) and FallAfterBack.lean
(`units_pass_layers`). At these two sorts of segment one run stands between the adding and
"K8.tests": "K8.lsTail" (Johnson/Desc/First/Driver/Chain.lean: orderAfterOf).
  `behind_two`   the frame's block behind the batching, where the order behind the batching is these
      two runs of block number i and they stand under the kind's own: a yes says that `zeroUnitAt`
      was false
  **`behind_att`**, **`behind_head`**   so at an attention segment and at the head's
  `units_pass_one`   z₁: what the run at "K8.lsTail" returns at t. If `zeroUnitAt nU t` is false,
      `selfUnits` says yes at the data and the ledger that z₁ holds: those that the kind's own run
      "K8.tests" reads
  **`units_pass_att`**, **`units_pass_head`**
WHICH RUN STANDS AT WHICH ENTRY IS A PREMISE, up to a guard: `AttTies`, `HeadTies`
(Johnson/Desc/First/Link/Law/PayAttention.lean, PayHead.lean).
Limits: those of the two files named. One conjunct of one test.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallAfterBack
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Link.Law.PayHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-- A yes of the frame's block behind the batching, where two runs stand behind the batching. -/
theorem behind_two (L : Link S Claim) (nU : Array Nat) (i : Nat)
    (tLs : ∀ run, LinkJoin.AtAfter L (i, "K8.lsTail") run → LinkJoin.UnderAfter run K9L.k8LsTail)
    (tTests : ∀ run, LinkJoin.AtAfter L (i, "K8.tests") run →
      LinkJoin.UnderAfter run (K9L.k8Tests nU))
    (hord : L.orderAfter = [(i, "K8.lsTail"), (i, "K8.tests")]) (t t' : S)
    (h : L.runBehind t = .ok t') : zeroUnitAt nU t = false := by
  unfold Link.runBehind at h
  split at h
  · rw [hord, afterIn_eq] at h
    simp only [afterAll] at h
    obtain ⟨z1, g1, h⟩ := bind_ok h
    obtain ⟨z2, g2, h⟩ := bind_ok h
    obtain ⟨r1, a1, y1⟩ := after_ok g1
    obtain ⟨r2, a2, y2⟩ := after_ok g2
    have e1 := zeroUnitAt_lsTail nU t z1 (tLs r1 a1 _ _ y1)
    have e2 := zeroUnitAt_tests nU z1 z2 (tTests r2 a2 _ _ y2)
    rw [← e1, e2]
  · exact absurd h (by simp)

/-- **At an attention segment.** -/
theorem behind_att (L : Link S Claim) (c : Att.P.ParC) (nU : Array Nat)
    (ties : LinkJoin.AttTies L c nU) (hord : L.orderAfter = orderAfterOf .attention) (t t' : S)
    (h : L.runBehind t = .ok t') : zeroUnitAt nU t = false :=
  behind_two L nU 4 ties.tLs ties.tTests hord t t' h

/-- **At the head's segment.** -/
theorem behind_head (L : Link S Claim) (hS : OnBytes.Model.Head.Shape) (iU3 l piece : Nat)
    (p : Kinds.Head.Par) (nU : Array Nat) (ties : LinkJoin.HeadTies L hS iU3 l piece p nU)
    (hord : L.orderAfter = orderAfterOf .head) (t t' : S) (h : L.runBehind t = .ok t') :
    zeroUnitAt nU t = false :=
  behind_two L nU 5 ties.tLs ties.tTests hord t t' h

/-- The conjunct passes at the call, where one run stands in front of it. -/
theorem units_pass_one (L : Link S Claim) (nU : Array Nat) (i : Nat)
    (tLs : ∀ run, LinkJoin.AtAfter L (i, "K8.lsTail") run → LinkJoin.UnderAfter run K9L.k8LsTail)
    (t z₁ : S) (r₁ : S → Except String S) (a₁ : LinkJoin.AtAfter L (i, "K8.lsTail") r₁)
    (y₁ : r₁ t = .ok z₁) (h : zeroUnitAt nU t = false) (tl : HTailF2) (F : Fork)
    (h1 : z₁.tl? = some tl) (h2 : z₁.fork? = some F) : selfUnits tl nU F = true := by
  have e1 := zeroUnitAt_lsTail nU t z₁ (tLs r₁ a₁ _ _ y₁)
  rw [selfUnits_eq nU z₁ tl F h1 h2, e1, h]
  rfl

theorem units_pass_att (L : Link S Claim) (c : Att.P.ParC) (nU : Array Nat)
    (ties : LinkJoin.AttTies L c nU) (t z₁ : S) (r₁ : S → Except String S)
    (a₁ : LinkJoin.AtAfter L (4, "K8.lsTail") r₁) (y₁ : r₁ t = .ok z₁)
    (h : zeroUnitAt nU t = false) (tl : HTailF2) (F : Fork) (h1 : z₁.tl? = some tl)
    (h2 : z₁.fork? = some F) : selfUnits tl nU F = true :=
  units_pass_one L nU 4 ties.tLs t z₁ r₁ a₁ y₁ h tl F h1 h2

theorem units_pass_head (L : Link S Claim) (hS : OnBytes.Model.Head.Shape) (iU3 l piece : Nat)
    (p : Kinds.Head.Par) (nU : Array Nat) (ties : LinkJoin.HeadTies L hS iU3 l piece p nU)
    (t z₁ : S) (r₁ : S → Except String S) (a₁ : LinkJoin.AtAfter L (5, "K8.lsTail") r₁)
    (y₁ : r₁ t = .ok z₁) (h : zeroUnitAt nU t = false) (tl : HTailF2) (F : Fork)
    (h1 : z₁.tl? = some tl) (h2 : z₁.fork? = some F) : selfUnits tl nU F = true :=
  units_pass_one L nU 5 ties.tLs t z₁ r₁ a₁ y₁ h tl F h1 h2

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.behind_att
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_head
#print axioms VerifiableInference.Desc.First.K8.Honest.units_pass_att
#print axioms VerifiableInference.Desc.First.K8.Honest.units_pass_head
