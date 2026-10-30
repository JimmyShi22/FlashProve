-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowChainProofs.lean: the proofs of the statements of Ior/KnowChain.lean: round-by-round
knowledge soundness of a chain of links from that of its links.

Proofs only. The rule for two in a row is `know_seq` (Ior/SeqProofs.lean); the rest is an induction
over the chain.

Main names: `knowT_seq`, `onOut_seq`, `chain_knowT`, `chain_onOut`, `knowT_append`, `onOut_append`,
`knowT_of_goodT`, `onOut_of_goodT`, `knowT_of_allT`, `onOut_of_allT`; the unfolding lemmas
`IOR.Chain.knowT_one`, `knowT_snoc`, `onOut_one`, `onOut_snoc`.

Limits: those of Ior/KnowChain.lean.

-/
import Ior.KnowChain

set_option autoImplicit false

namespace Iop

namespace IOR.Chain
variable {K : Type} {A B C : Joint K}

/-- `KnowT` of a chain of one link. -/
theorem knowT_one (l : Link K A B) : (Chain.one l).KnowT ↔ l.KnowT := by rw [KnowT]

/-- `KnowT` of a chain with one more link. -/
theorem knowT_snoc (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).KnowT ↔ c.KnowT ∧ l.KnowT := by rw [KnowT]

/-- `OnOut` of a chain of one link. -/
theorem onOut_one (l : Link K A B) : (Chain.one l).OnOut ↔ l.OnOut := by rw [OnOut]

/-- `OnOut` of a chain with one more link. -/
theorem onOut_snoc (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).OnOut ↔ c.OnOut ∧ l.OnOut := by rw [OnOut]

end IOR.Chain

open IOR IOR.Chain

theorem knowT_seq : Spec.knowT_seq := by
  intro K A B C l l' d h ho h'
  exact know_seq _ _ _ _ _ _ l.R l'.R _ _ _ _ _ _ _ _ l.ext l'.ext l.P.err l'.P.err d h h' ho

theorem onOut_seq : Spec.onOut_seq := by
  intro K A B C l l' d h h' a τ c ha hc
  obtain ⟨b, hb, hc'⟩ :=
    Option.bind_eq_some_iff.1 ((IOR.red_seq_out l.R l'.R a τ).symm.trans hc)
  exact h' b _ c (h a _ b ha hb) hc'

theorem chain_onOut : Spec.chain_onOut := by
  intro K A B c
  induction c with
  | one l =>
      intro h d
      rw [link_one]
      exact (onOut_one l).1 h
  | snoc c l ih =>
      intro h d
      rw [link_snoc]
      exact onOut_seq K _ _ _ _ _ d (ih ((onOut_snoc c l).1 h).1 d) ((onOut_snoc c l).1 h).2

theorem chain_knowT : Spec.chain_knowT := by
  intro K A B c
  induction c with
  | one l =>
      intro h _ d
      rw [link_one]
      exact (knowT_one l).1 h
  | snoc c l ih =>
      intro h ho d
      rw [link_snoc]
      exact knowT_seq K _ _ _ _ _ d (ih ((knowT_snoc c l).1 h).1 ((onOut_snoc c l).1 ho).1 d)
        (chain_onOut K _ _ c ((onOut_snoc c l).1 ho).1 d) ((knowT_snoc c l).1 h).2

theorem knowT_append : Spec.knowT_append := by
  intro K A B C c c'
  induction c' with
  | one l => rw [append_one, knowT_snoc, knowT_one]
  | snoc c' l ih => rw [append_snoc, knowT_snoc, knowT_snoc, ih, and_assoc]

theorem onOut_append : Spec.onOut_append := by
  intro K A B C c c'
  induction c' with
  | one l => rw [append_one, onOut_snoc, onOut_one]
  | snoc c' l ih => rw [append_snoc, onOut_snoc, onOut_snoc, ih, and_assoc]

theorem knowT_of_goodT : Spec.knowT_of_goodT := fun _ _ _ _ g => g.know

theorem onOut_of_goodT : Spec.onOut_of_goodT := fun _ _ _ _ g => g.onOut

theorem knowT_of_allT : Spec.knowT_of_allT := by
  intro K A B c
  induction c with
  | one l => exact fun h => (knowT_one l).2 ((allT_one l).1 h).know
  | snoc c l ih =>
      exact fun h => (knowT_snoc c l).2 ⟨ih ((allT_snoc c l).1 h).1, ((allT_snoc c l).1 h).2.know⟩

theorem onOut_of_allT : Spec.onOut_of_allT := by
  intro K A B c
  induction c with
  | one l => exact fun h => (onOut_one l).2 ((allT_one l).1 h).onOut
  | snoc c l ih =>
      exact fun h => (onOut_snoc c l).2 ⟨ih ((allT_snoc c l).1 h).1, ((allT_snoc c l).1 h).2.onOut⟩

end Iop
