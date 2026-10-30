-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverStart.lean: NO CHAIN's START HAS MET A FALL. `falls_local`
(Honest/Law/CoverAll.lean) takes three premises s₁, s₂, s₃: by no round of the chain the run has met
a fall. With no round laid the members that have been asked are those WITHOUT a round in front of
the first member that has one. Here: where no fall of the chain's list sits at one of these, the
premise holds (`fellBy_start`), at whatever the walk starts from, if that is a start of the frame's
own.

WHAT THIS IS. A lemma on definitions of ours. None of the library's goals.

  `fellBy_start`

hX: what the chain's walk starts from is a start of the frame's own (`ChainProgress.start`), at some columns
handed: at a file: `at₁_starts`, `at₂_starts`, `at₃_starts` (Honest/Law/CoverAll.lean), in just this
form (`m₀.isSome` is not spent here).

Limits. That no fall sits at a chain's first members without a round is a premise: a fact on the
list of falls' places. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl W Y : Type}

/-- **By no round the run has met a fall**, where none sits at the members without a round in front
of the first that has one. -/
theorem fellBy_start (all : List (Block S Cl)) (fs : List (Fall S)) (X : ChainAt S Cl W Y)
    (hX : ∀ a s₀, X.start = some a → X.s₀ = some s₀ →
      ∃ (m₀ : Option (Mid W Y)) (front : List OpenedColumn), m₀.isSome = true ∧
        ChainProgress.start X.lay all m₀ (some s₀) front = .ok a)
    (h : ∀ d ∈ all.takeWhile (fun d => d.rounds.isEmpty), ∀ f ∈ fs, f.place ≠ d.place)
    (dr : List Fmt.Drawn) : fellBy all fs X 0 dr = false := by
  cases hs : X.start with
  | none =>
    unfold fellBy
    rw [hs]
  | some a =>
    cases h0 : X.s₀ with
    | none =>
      unfold fellBy
      rw [hs, h0]
    | some s =>
      obtain ⟨m₀, _, -, ha⟩ := hX a s hs h0
      obtain ⟨-, -, l0⟩ := start_tied X.lay all m₀ (some s) ha
      cases hw : walk X.lay (X.steps.take 0) (dr.take 0) a with
      | error e =>
        unfold fellBy
        rw [hs, h0]
        simp only
        rw [hw]
      | ok z =>
        rw [fellBy_ok all fs hs h0 hw]
        have hz : z = a := by
          rw [List.take_zero, List.take_zero] at hw
          exact walk_nil_ok hw
        rw [hz, l0]
        cases hc : (chainFall fs X.lay.firstTree all s ⟨roundsOf [], a.cols⟩).isSome with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨e, he, hf⟩ := (chainFall_iff _ _ _ _ _).1 hc
          obtain ⟨d, hd, hpl⟩ := fronts_quiet X.lay.firstTree all s a.cols e he
          rw [fallOf_none fs e.1 (fun f hf' => by rw [← hpl]; exact h d hd f hf')] at hf
          cases hf

end ProofFile.Honest

#print axioms ProofFile.Honest.fellBy_start
