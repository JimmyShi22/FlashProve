-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/RchIsReach.lean: "REACHED" AT THE HEAD's DESCRIPTION IS "REACHED" OVER THE CHAIN's OWN LETTERS. Two theorems.
  Why. Every paid field of the facts on every reached state (FoldFacts) has one premise of the form hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (at_ a), at the maker's opening's letters c | Z. The counted laws' Rch stands at RchAt (F0T o Zp Np cF) (Johnson/Top/H0/Walk/ReachAt.lean: over the wrapped sub-protocols).
  rch_is_reach: RchAt (F0T o Zp Np cF) k a = Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1: BY UNFOLDING: the seated description's first chain IS cF and its first start IS startS Zp.
  hRch_at: so at any Rch that gives RchAt (F0T …) and at_ := fun a => a.1 the premise holds.
Limits. An unfolding. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LaidOpens
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)

theorem rch_is_reach {Str : Type} (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (k : ℕ)
    (a : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × Str) :
    RchAt (F0T o Zp Np cF) k a =
      Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) k a.1 := rfl

theorem hRch_at {Str : Type} (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl)
    (Rch : ℕ → ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × Str → Prop)
    (h : ∀ k a, Rch k a → RchAt (F0T o Zp Np cF) k a) :
    ∀ k a, Rch k a →
      Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) k a.1 :=
  fun k a hr => (rch_is_reach o Zp Np cF k a) ▸ h k a hr

end P5J

#print axioms P5J.rch_is_reach
#print axioms P5J.hRch_at
