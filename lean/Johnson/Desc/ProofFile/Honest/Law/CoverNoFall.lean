-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverNoFall.lean: lemmas for a chain whose list of falls is empty.
`falls_local` (Honest/Law/CoverAll.lean) bounds the chance that a run meets a fall. It takes, for
each of the three chains, one bound for each gated sub-protocol (`LocalDebts`,
Honest/Law/CoverHeld.lean) and the fact that the run has met no fall before the chain's first round.
This file proves both for a chain with an empty list of falls, if none of the chain's marks fires at
a typed message of its sub-protocol's own rounds.

  1  `stretch_len`   the length of a sub-protocol's share of the chain's data
  2  `fellBy_noFall`   the run has met no fall
  3  `debt_noFall`, `localDebts_noFall`   the bound for one sub-protocol, and for all of them

The hypothesis `hmk` says that no mark at the sub-protocol's place fires at a typed message of the
sub-protocol's share of the data. For the marks that test whether the challenges fit the rounds it
follows from `fit_at_member` (Honest/Law/CoverFitAt.lean) with `mark_silent`
(Honest/Law/CoverFit.lean). For the marks that repeat the stops it follows from `stopMarks_none`
(Honest/Law/CoverPay.lean) where no part has a stop that fires.

Nothing is assumed about the state from which the chain's walk starts. With an empty list of falls
it does not matter which sub-protocols are still to be asked.

Limits.
  * That a chain's list of falls is empty is a hypothesis. All falls that have been written for the
    proof file so far are in the first chain. That the other two chains need none has been stated
    for single sub-protocols, not for a whole chain.
  * The lemmas are applied to no description here.
  * No number follows from them.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-- A sub-protocol's share of the data has as many entries as the sub-protocol has rounds, if the
chain's data have as many entries as the chain has rounds. -/
theorem stretch_len (ds : List RDT) (A B : List (Block S Cl)) (b : Block S Cl)
    (h : ds.length = ((A ++ b :: B).flatMap (·.rounds)).length) :
    ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length).length = b.rounds.length := by
  rw [List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append] at h
  rw [List.length_take, List.length_drop]
  omega

/-- With an empty list of falls the run has met no fall, up to any round. -/
theorem fellBy_noFall (all : List (Block S Cl)) (X : ChainAt S Cl W Y) (n : Nat)
    (dr : List Fmt.Drawn) : fellBy all [] X n dr = false := by
  unfold fellBy
  split
  · split
    · rw [chainFall_none [] _ all (fun _ _ f hf => by cases hf)]
      rfl
    · rfl
  · rfl

/-- The bound for one sub-protocol, with an empty list of falls. It holds for any number `p j`, for
any fixed challenges `tl` after the sub-protocol's own, and whether or not the sub-protocol has a
round. -/
theorem debt_noFall (C : CK) (all : List (Block S Cl)) (ms : List Mark) (skip : Nat)
    (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞) (bs : List (Block S Cl))
    {b : Block S Cl} {j n : Nat} {dsb : List RDT} {tl : List Fmt.Drawn} {last : Bool}
    (hj : bs[j]? = some b) (hn : n = ((bs.take j).flatMap (·.rounds)).length)
    (hlen : dsb.length = b.rounds.length)
    (hmk : ∀ fr (ρ : Iop.Rho (uLT C dsb)), markOf ms b.place fr (drawnT C dsb ρ) = none) :
    DebtAt C all [] ms skip X p (silentQ ms skip bs) b j n dsb tl last := by
  intro fr h1 h2 h3 h4
  refine ⟨zero_of_not C dsb _ (fun ρ hρ => ?_) _, fun _ ρ hm _ =>
    silentQ_step ms skip bs hj fr _ h1 (by rw [h2, hn]) (by rw [drawnT_len, hlen]) h4 hm⟩
  rcases hρ with hm | ⟨a, z, s', -, -, -, z', ps, cs, -, -, -, y4⟩
  · rw [hmk] at hm
    cases hm
  · rw [chainFall_none [] _ z.todo (fun _ _ f hf => by cases hf)] at y4
    cases y4

/-- With an empty list of falls the bounds of all gated sub-protocols hold, for any numbers. -/
theorem localDebts_noFall (C : CK) (all bs : List (Block S Cl)) (ms : List Mark) (skip : Nat)
    (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞) (tail : List Fmt.Drawn)
    (ds : List RDT) (hlen : ds.length = (bs.flatMap (·.rounds)).length)
    (hmk : ∀ (A : List (Block S Cl)) (b : Block S Cl) (B : List (Block S Cl)), bs = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms b.place fr (drawnT C _ ρ) = none) :
    LocalDebts C all [] ms skip X p tail (silentQ ms skip bs) bs 0 0 ds := by
  refine localDebts_of C all [] ms skip X p tail (silentQ ms skip bs) bs 0 0 ds
    fun A b B e => ?_
  have hj : bs[0 + A.length]? = some b := by
    rw [Nat.zero_add, e, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hn : 0 + (A.flatMap (·.rounds)).length =
      ((bs.take (0 + A.length)).flatMap (·.rounds)).length := by
    rw [Nat.zero_add, Nat.zero_add, e, List.take_left' rfl]
  exact debt_noFall C all ms skip X p bs hj hn (stretch_len ds A B b (by rw [← e]; exact hlen))
    (hmk A b B e)

end ProofFile.Honest

#print axioms ProofFile.Honest.stretch_len
#print axioms ProofFile.Honest.fellBy_noFall
#print axioms ProofFile.Honest.debt_noFall
#print axioms ProofFile.Honest.localDebts_noFall
