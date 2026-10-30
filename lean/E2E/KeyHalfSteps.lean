-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyHalfSteps.lean: `chainSteps` at one member of the shared chain, at the key file's book, at all
coins, where the member's half has one part.

Why. `Plays` takes it as a premise at each member with a half; this file has it at any place that
passes three closed tests.

Main names.
  `placeTests`: the three tests of `chainSteps` on the book, at a place and a cut.
  `full_point`, `full_folded`: they say yes at the written book, at «LIN point» and at «send o_u». By
    Lean's kernel.
  `steps_half`: the steps return, at all coins.

What stays open. The member and the half are letters. Nothing says that the thread stands.

No statement here names a coin of the committer: `k` ranges over all coins. No law over coins here.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyBookHeldHash

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyHalfSteps
open ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open AtPublicFiles.KeyBook

/-- The three tests of `chainSteps` on the book, at a place and a cut. -/
def placeTests (K : KeyPub) (a : Place) (cut : List Nat) : Bool :=
  ((keyBook K).cuts.lookup a == some cut) &&
    !((keyBook K).shared.any fun r => r.1.place == a && decide (1 ≤ r.1.part)) &&
    !((keyBook K).ahead.any fun e => e.spender.place == a && decide (1 ≤ e.spender.part))

theorem full_point : atFull (fun K => placeTests K pointPlace [1]) = true := by decide +kernel

theorem full_folded : atFull (fun K => placeTests K foldedPlace [2]) = true := by decide +kernel

/-- **`chainSteps` at one member, at all coins.** -/
theorem steps_half {V W X S Cl : Type} (K : KeyPub) (hK : fullPub = some K) (a : Place)
    (cut : List Nat) (ht : placeTests K a cut = true) (ha : (chainPlaces 1).contains a = true)
    (h : Placed V W X) (hlen : h.parts.length = 1)
    (hcut : h.parts.map (·.moves.length) = cut)
    (hst : ∀ i p, h.parts[i]? = some p → Stated (keyBook K) ((keyBook K).rowsOf 1) ⟨a, i⟩ p)
    (b : Block S Cl) (hp : b.place = a) (ho : b.oracles.length = b.rounds.length)
    (hrd : h.rounds = b.rounds.length) (hs : List (Placed V W X))
    (hf : (hs.find? fun g => g.place == b.place) = some h) (k : Coins (keyBook K)) (v : Option V) :
    ∃ l, chainSteps (keyBook K) ((keyBook K).rowsOf 1) (k.look 1) v [b] hs = .ok l := by
  obtain ⟨c, hcoin⟩ := key_lends K hK k 1 (Or.inr (Or.inl rfl)) a ha h.parts hst
  simp only [placeTests, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ht
  obtain ⟨⟨t1, t2⟩, t3⟩ := ht
  have e1 : (b.oracles.length != b.rounds.length) = false := by
    rw [ho]
    simp
  have e2 : (h.rounds != b.rounds.length) = false := by
    rw [hrd]
    simp
  have e3 : (((keyBook K).cuts.lookup b.place) != some (h.parts.map (·.moves.length))) = false := by
    rw [hp, hcut, t1]
    simp
  have e4 : ((keyBook K).rowsOf 1).any
      (fun r => r.1.place == b.place && decide (h.parts.length ≤ r.1.part)) = false := by
    rw [hp, hlen]
    exact t2
  have e5 : (keyBook K).ahead.any
      (fun e => e.spender.place == b.place && decide (h.parts.length ≤ e.spender.part)) = false := by
    rw [hp, hlen]
    exact t3
  have hc2 : lendRow (keyBook K) ((keyBook K).rowsOf 1) (k.look 1) b.place h.parts 0 = .ok c := by
    rw [hp]
    exact hcoin
  refine ⟨h.steps b v c ++ [], ?_⟩
  simp only [chainSteps, e1, hf, e2, e3, e4, e5, hc2]
  rfl

end AtPublicFiles.KeyHalfSteps

#print axioms AtPublicFiles.KeyHalfSteps.full_point
#print axioms AtPublicFiles.KeyHalfSteps.full_folded
#print axioms AtPublicFiles.KeyHalfSteps.steps_half
