-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollLit.lean: round-by-round knowledge soundness in the form with a knowledge state
function (`HasRbrKnowledge`, Ior/Know.lean), with the state function named; substeps inside one
verifier message; the state "the state before, or outside the condition".

Definitions, statements and proofs. No protocol, no code occurs here.
A reduction K (`Reduction`, Iop/Compose.lean): rounds, then a verifier that rejects or outputs a
statement. `K.Know on RA RB ext ε` (Ior/Know.lean) is round-by-round knowledge soundness in its
working form: on every statement with `on` the prover has lost, at the start (`Doomed`,
Iop/Rbr.lean), towards: every witness in RB of an output extracts, by ext, to a witness in RA of
the input.
Ior/Know.lean has the form with a knowledge state function: a function on (partial transcript,
knowledge state witness) with its three laws (`IsKState`), an extractor for each round (`RExt`),
and for each round a bound on the verifier messages after which some witness is in state 1 while
its extraction was in state 0 (`HasRbrKnowledge`: "there is a state function ..").

Main names:
  `K.HasRbrKnowledgeWith on RA RB St Ex ε`: the same with the state function St named, so that a
    proof can state the very function of a written argument.
  `Spec.literal_of_with`, `Spec.know_of_with`: it gives `HasRbrKnowledge`, hence the working form
    `Know`, with the same errors; the extractor is got by composing the rounds' extractors
    backwards, the last round's first.
  `Spec.cnt_substeps`: a verifier message that is a pair (c₁, c₂) may be analysed in two steps,
    with a state "mid" after c₁ that no transcript of the protocol shows: if at most k₁ values c₁
    move some witness from 0 (at its extraction x₁) to 1, and after every c₁ at most k₂ values c₂
    do so from "mid" to the state after the pair, then at most k₁ |C₂| + |C₁| k₂ pairs move some
    witness from 0, at the composed extraction x₁ ∘ x₂, to 1. As probabilities: the two errors add.
  `stCf K on on' RB St`, `Spec.with_cf`: the state "the state before, or outside the condition",
    and the rule for a reduction that carries the condition; see their docstrings.

Why "at least one round" in `Spec.with_cf`: in a reduction without rounds the empty transcript is
full, and the two laws for it would ask that every statement outside `on` has an output in the
enlarged relation.

Limits: this file says nothing on lists, samples, collisions: `on`, `on'` are any conditions. It
says nothing on running times.
The rule for carried conditions follows this protocol's technical report (lean/CREDITS.md), which
follows the paper that this protocol builds on; that the errors of two substeps add is the way of
the paper that this protocol builds on of analysing a verifier message in two parts.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowColl
import Ior.KnowLit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

namespace Reduction
variable {A B : Type}

/-- Round-by-round knowledge soundness, the form with a knowledge state function, with the state
function and the round extractors named. -/
def HasRbrKnowledgeWith (K : Reduction A B) {S : Type} (on : A → Prop)
    (RA : A → S → Prop) (RB : B → S → Prop) (St : A → PTr K.shape → S → Bool)
    (Ex : A → RExt S K.shape) (ε : Err K.shape) : Prop :=
  ∀ a, on a →
    K.IsKState RA RB a (St a) ∧
    ∀ τ : AtV K.shape,
      cnt (fun c : τ.round.Chal =>
          ∃ s, St a (.atV τ) ((Ex a).at τ c s) = false ∧ St a (τ.snoc c) s = true) ≤ τ.err ε

open Classical in
/-- The state "the state before, or outside the condition". On a statement with `on`: St. On a
statement outside `on`: 1 for every witness on every transcript that is not full, and on a full
transcript membership of the output in the enlarged relation (a move from 1 to 0 costs nothing). -/
def stCf (K : Reduction A B) {S : Type} (on : A → Prop) (on' : B → Prop)
    (RB : B → S → Prop) (St : A → PTr K.shape → S → Bool) : A → PTr K.shape → S → Bool :=
  fun a t s => if on a then St a t s else
    match t with
    | .full τ => decide (∃ b, K.out a τ = some b ∧ orOff on' RB b s)
    | _ => true

end Reduction

namespace Spec
open Reduction

def literal_of_with : Prop :=
  ∀ (A B S : Type) (K : Reduction A B) (on : A → Prop) (RA : A → S → Prop) (RB : B → S → Prop)
      (St : A → PTr K.shape → S → Bool) (Ex : A → RExt S K.shape) (ε : Err K.shape),
    K.HasRbrKnowledgeWith on RA RB St Ex ε → K.HasRbrKnowledge on RA RB Ex ε

def know_of_with : Prop :=
  ∀ (A B S : Type) (K : Reduction A B) (on : A → Prop) (RA : A → S → Prop) (RB : B → S → Prop)
      (St : A → PTr K.shape → S → Bool) (Ex : A → RExt S K.shape) (ε : Err K.shape),
    K.HasRbrKnowledgeWith on RA RB St Ex ε → K.Know on RA RB (fun a τ s => (Ex a).back τ s) ε

/-- States, for two substeps inside one verifier message: as probabilities the errors add; the
extractors compose. -/
def cnt_substeps : Prop :=
  ∀ (C₁ C₂ S : Type) [Fintype C₁] [Fintype C₂] (pre : S → Bool) (mid : C₁ → S → Bool)
      (post : C₁ × C₂ → S → Bool) (x₁ : C₁ → S → S) (x₂ : C₁ × C₂ → S → S) (k₁ k₂ : ℕ),
    cnt (fun c₁ : C₁ => ∃ s, pre (x₁ c₁ s) = false ∧ mid c₁ s = true) ≤ k₁ →
    (∀ c₁ : C₁,
      cnt (fun c₂ : C₂ => ∃ s, mid c₁ (x₂ (c₁, c₂) s) = false ∧ post (c₁, c₂) s = true) ≤ k₂) →
    cnt (fun c : C₁ × C₂ => ∃ s, pre (x₁ c.1 (x₂ c s)) = false ∧ post c s = true) ≤
      k₁ * Fintype.card C₂ + Fintype.card C₁ * k₂

/-- States: if the reduction carries the condition (its output is outside `on'` only if its input
is outside `on`) and has at least one round, `HasRbrKnowledgeWith` on all statements for (RA, RB)
with St gives it for the two enlarged relations (`orOff`, Ior/KnowColl.lean) with `stCf`, the same
round extractors and the same errors. -/
def with_cf : Prop :=
  ∀ (A B S : Type) (K : Reduction A B) (on : A → Prop) (on' : B → Prop)
      (RA : A → S → Prop) (RB : B → S → Prop) (St : A → PTr K.shape → S → Bool)
      (Ex : A → RExt S K.shape) (ε : Err K.shape),
    K.shape ≠ [] → (∀ a τ b, K.out a τ = some b → on a → on' b) →
    K.HasRbrKnowledgeWith (fun _ => True) RA RB St Ex ε →
    K.HasRbrKnowledgeWith (fun _ => True) (orOff on RA) (orOff on' RB) (stCf K on on' RB St) Ex ε

end Spec

open Reduction

theorem literal_of_with : Spec.literal_of_with := fun _ _ _ _ _ _ _ St _ _ h => ⟨St, h⟩

theorem know_of_with : Spec.know_of_with := fun A B S K on RA RB St Ex ε h =>
  know_of_literal A B S K on RA RB Ex ε ⟨St, h⟩

theorem cnt_substeps : Spec.cnt_substeps := by
  intro C₁ C₂ S _ _ pre mid post x₁ x₂ k₁ k₂ h₁ h₂
  refine cnt_two_rounds_le _ (fun c₁ => ∃ s, pre (x₁ c₁ s) = false ∧ mid c₁ s = true)
    k₁ k₂ h₁ fun c₁ hc₁ => ?_
  refine le_trans (cnt_mono ?_) (h₂ c₁)
  rintro c₂ ⟨s, hs, hp⟩
  refine ⟨s, ?_, hp⟩
  cases hm : mid c₁ (x₂ (c₁, c₂) s) with
  | false => rfl
  | true => exact absurd ⟨x₂ (c₁, c₂) s, hs, hm⟩ hc₁

/-- In a shape with at least one round the empty transcript is at the prover. -/
theorem PTr.empty_eq_atP : ∀ {s : Shape}, s ≠ [] → ∃ τ : AtP s, PTr.empty s = .atP τ
  | [], h => absurd rfl h
  | _ :: _, _ => ⟨Sum.inl (), rfl⟩

theorem with_cf : Spec.with_cf := by
  classical
  intro A B S K on on' RA RB St Ex ε hs hc h a _
  obtain ⟨hk, hcnt⟩ := h a trivial
  by_cases ha : on a
  · have e : stCf K on on' RB St a = St a := by
      funext t s
      unfold stCf
      rw [if_pos ha]
    rw [e]
    refine ⟨⟨fun s => (hk.empty s).trans ⟨Or.inl, fun h => h.elim id fun hn => absurd ha hn⟩,
        hk.prover,
        fun τ s => (hk.full τ s).trans ?_⟩,
      hcnt⟩
    exact ⟨fun ⟨b, hb, hw⟩ => ⟨b, hb, Or.inl hw⟩,
      fun ⟨b, hb, hw⟩ => ⟨b, hb, hw.elim id fun hn => absurd (hc a τ b hb ha) hn⟩⟩
  · have eP : ∀ (τ : AtP K.shape) s, stCf K on on' RB St a (.atP τ) s = true := fun τ s => by
      unfold stCf
      rw [if_neg ha]
    have eV : ∀ (τ : AtV K.shape) s, stCf K on on' RB St a (.atV τ) s = true := fun τ s => by
      unfold stCf
      rw [if_neg ha]
    refine ⟨⟨fun s => ?_, fun τ m s h0 => ?_, fun τ s => ?_⟩, fun τ => ?_⟩
    · obtain ⟨τ, hτ⟩ := PTr.empty_eq_atP hs
      rw [hτ, eP]
      exact ⟨fun _ => Or.inr ha, fun _ => rfl⟩
    · rw [eP] at h0
      cases h0
    · unfold stCf
      rw [if_neg ha]
      exact decide_eq_true_iff
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro c ⟨s, h0, _⟩
        rw [eV] at h0
        cases h0

end Iop
