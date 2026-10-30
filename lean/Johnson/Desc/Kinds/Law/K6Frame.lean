-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/K6Frame.lean: THREE SMALL LAWS ON THE FRAME, for the call of the bridge from a kind's rule of bad elements to a block's own law at the table (Johnson/Desc/Sound/RuleAtKit.lean: OwnOfRuleAtKit) at the output head's block: general in the block: STATED AND PROVED.
  out_step              where a piece's reduction gives a statement behind, ITS BLOCK's Block.step WENT ON, on the view's rounds (with what is put behind them), to that statement's record. ("The piece's out gives Block.step": owed in Law/RowPins.lean's head.)
  below_step            the proof's device "below b" (Johnson/Desc/Sound/ChainRule.lean: the block that first tests that every word shown to it is below the prime, then decides as b does; the fold of such blocks IS the fold with that test on the whole view in front: foldBelow): where its step goes on, the test
                        passed on its rounds and b's own step went on to the same record.
  canonical_of_okViewW  where that test passes, the rounds are Canonical (HeadLaw.lean): every element SENT OR DRAWN is written in its one canonical way.
SO Canonical rs, WHICH THE OUTPUT HEAD's LAWS TAKE WHOLE, IS PAID AT A PIECE THAT HOLDS below b, for what the prover sends too. (That the text which runs asks this test once, of the whole view, in front of its three folds, is ChainRule.lean § 7's own word on the file's decision: NOT HELD HERE.)
WHAT IT DOES NOT SAY. Nothing of any kind's law. No chance in it.

-/
import Mathlib
import Johnson.Desc.Sound.FoldBelowProof
import Johnson.Desc.Kinds.HeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc.Sound (Piece Frame foldRun)

/-- **Where the test on the words passes, the rounds are Canonical.** -/
theorem canonical_of_okViewW {R : List Fmt.RoundView} {c : List OpenedColumn} (h : viewWordsBelowPrime ⟨R, c⟩ = true) :
    Canonical R := by
  unfold viewWordsBelowPrime at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  obtain ⟨h1, h2⟩ := h.1 r hr
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h3 := h2 (.e x) hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    simp only [OnBytes.okE, OnBytes.okF, E.ofTriple, E.mk3, Bool.and_eq_true, decide_eq_true_eq]
    exact h3
  · have h3 := h1 x hx
    simp only [decide_eq_true_eq] at h3
    simp only [OnBytes.okE, OnBytes.okF, E.ofTriple, E.mk3, Bool.and_eq_true, decide_eq_true_eq]
    exact h3

/-- **Where the step of "below b" goes on.** -/
theorem below_step {S' Cl : Type} (ft : Nat) (b : Block S' Cl) (s : S') (R : List Fmt.RoundView)
    (c : List OpenedColumn) (s' : S') (n : Nat) (h : (Sound.below b).step ft s R c = .ok (s', n)) :
    Canonical R ∧ b.step ft s R c = .ok (s', n) := by
  have e := Sound.step_below ft b s R c
  rw [h] at e
  by_cases hk : viewWordsBelowPrime ⟨R, c.take ((b.reads ft (R.map (·.drawn))).flatMap id).length⟩ = true
  · rw [if_pos hk] at e
    exact ⟨canonical_of_okViewW hk, Sound.ok_of_some _ _ e.symm⟩
  · rw [if_neg hk] at e
    cases e

/-- **Where a piece's reduction gives a statement behind, its block's step went on.** -/
theorem out_step {C : CK} {F : Frame} {S' Cl W : Type} (p : Piece C F S' Cl W)
    (a b : S' × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some b) :
    ∃ cols n, p.b.step F.ft a.1 ((sView C p.stage a.2 τ).rounds ++ p.back) cols = .ok (b.1, n) := by
  have h' : (p.ior.out a.1 a.2 τ).map (fun x => (x, p.ior.imp a.2 τ)) = some b := h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h'
  have hx' : (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none)
      = some x := hx
  split at hx'
  · unfold Piece.run foldRun at hx'
    rw [VerifiableInference.Desc.chainAt_toOption] at hx'
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at hx'
    generalize hR : (sView C p.stage a.2 τ).rounds ++ p.back = R at hx' ⊢
    generalize (sView C p.stage a.2 τ).opened = cols at hx'
    simp only [foldBlocks] at hx'
    split at hx'
    · cases hx'
    · rename_i hlen
      split at hx'
      · cases hx'
      · rename_i s' k hs
        -- the fold's end: nothing is left over
        have hrest : (R.splitAt p.b.rounds.length).2 = [] ∧ s' = x := by
          cases hr : (R.splitAt p.b.rounds.length).2 with
          | nil =>
            rw [hr] at hx'
            cases hc : cols.drop k with
            | nil =>
              rw [hc] at hx'
              exact ⟨rfl, Option.some.inj hx'⟩
            | cons _ _ =>
              rw [hc] at hx'
              cases hx'
          | cons _ _ =>
            rw [hr] at hx'
            cases hx'
        obtain ⟨h1, rfl⟩ := hrest
        have hall : (R.splitAt p.b.rounds.length).1 = R := by
          rw [List.splitAt_eq] at h1 ⊢
          have h2 : R.take p.b.rounds.length ++ R.drop p.b.rounds.length = R :=
            List.take_append_drop _ _
          have h3 : R.drop p.b.rounds.length = [] := h1
          rw [h3, List.append_nil] at h2
          exact h2
        rw [hall] at hs
        exact ⟨cols, k, hs⟩
  · cases hx'

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.canonical_of_okViewW
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.below_step
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.out_step
