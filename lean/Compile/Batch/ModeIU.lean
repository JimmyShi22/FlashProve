-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/ModeIU.lean: the relation `RelW` between the states of two challengers in mode I of
Rom/Defer.lean, one with the prover that hashes empty slots (`Pp`, Compile/Batch/Star.lean), one
with the prover with no query for an empty slot (`PpU`, Compile/Batch/StarU.lean), and small lemmas
on it. Used in Compile/Batch/PubProgModeI.lean (words of this library: lean/GLOSSARY.md). This file
does not prove that the two provers give the same view.
  `RelW`         the same private state; the invariant `Spec.InvD` at the first challenger's state;
                 before the setup the same state of the experiment; after it, states related by
                 `StRel` (Rom/SkipRel.lean) under a correspondence of tokens (`Wd`) in which each
                 token of the setup corresponds to itself
-/
import Compile.Batch.ChallU
import Compile.Batch.SpecSkipU
import Compile.SkipVirt
import Rom.SkipRun
import Rom.SkipWithin

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Prob
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt up chall_reply)

namespace ModeI

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- the states of the two challengers -/
abbrev WSt (W : QueryLayout lam L) : Type := Option (IskH lam L × ℕ) × DSt (spec lam W.K L)

/-- The relation between the states of the two challengers. -/
def RelW (s₁ s₂ : WSt W) : Prop :=
  s₁.1 = s₂.1 ∧ Spec.InvD W p s₁.1 s₁.2 ∧
    match s₁.1 with
    | none => s₁.2 = s₂.2
    | some (_, N₀) => ∃ w : Wd, StRel w s₁.2 s₂.2 ∧ N₀ ≤ w.n₁ ∧ N₀ ≤ w.n₂ ∧ ∀ a, a < N₀ → w.ρ a a

variable {W p}

theorem RelW.mk_some {τ₁ τ₂ : Option (IskH lam L × ℕ)} {d₁ d₂ : DSt (spec lam W.K L)}
    {k : IskH lam L} {N₀ : ℕ} (h₁ : τ₁ = some (k, N₀)) (h₂ : τ₂ = τ₁) (hI : Spec.InvD W p τ₁ d₁)
    (w : Wd) (hs : StRel w d₁ d₂) (g₁ : N₀ ≤ w.n₁) (g₂ : N₀ ≤ w.n₂) (hid : ∀ a, a < N₀ → w.ρ a a) :
    RelW W p (τ₁, d₁) (τ₂, d₂) := by
  subst h₂ h₁
  exact ⟨rfl, hI, w, hs, g₁, g₂, hid⟩

/-- a state that has the invariant is related to itself -/
theorem RelW.refl {τ : Option (IskH lam L × ℕ)}
    {d : DSt (spec lam W.K L)} (hI : Spec.InvD W p τ d) : RelW W p (τ, d) (τ, d) := by
  rcases τ with _ | ⟨k, N₀⟩
  · exact ⟨rfl, hI, rfl⟩
  · have ht := hI.1.1
    exact ⟨rfl, hI,
      Wd.same d.vals.length,
      StRel.refl d ht.shown_lt fun e he => ⟨ht.charged_lt e he, ht.tail_lt e he, ht.others_lt e he⟩,
      hI.1.2.2.1.len, hI.1.2.2.1.len,
      fun a ha => ⟨rfl, lt_of_lt_of_le ha hI.1.2.2.1.len⟩⟩

theorem RelW.table {s₁ s₂ : WSt W} (h : RelW W p s₁ s₂) : s₁.2.table = s₂.2.table := by
  obtain ⟨τ₁, d₁⟩ := s₁
  obtain ⟨-, -, hm⟩ := h
  rcases τ₁ with _ | ⟨k, N₀⟩
  · exact congrArg DSt.table hm
  · obtain ⟨w, hs, -⟩ := hm
    exact hs.table

/-- the invariant does not read the table -/
theorem invD_table {τ : Option (IskH lam L × ℕ)} {d : DSt (spec lam W.K L)}
    (h : Spec.InvD W p τ d) (T : Table (spec lam W.K L)) :
    Spec.InvD W p τ { d with table := T } := by
  rcases τ with _ | ⟨k, N₀⟩
  · rcases h with rfl | ⟨T', rfl⟩
    · exact Or.inr ⟨T, rfl⟩
    · exact Or.inr ⟨T, rfl⟩
  · obtain ⟨h, hp⟩ := h
    exact ⟨⟨h.1.table T, Disc.WorldB.iskOK_of h.2.1 fun ts _ hc => ⟨hc.lt, hc.tail, hc.others⟩,
      ⟨h.2.2.1.len, h.2.2.1.tails, h.2.2.1.low, h.2.2.1.high⟩, h.2.2.2⟩, hp⟩

theorem RelW.setTable {s₁ s₂ : WSt W} (h : RelW W p s₁ s₂) (T : Table (spec lam W.K L)) :
    RelW W p (s₁.1, { s₁.2 with table := T }) (s₂.1, { s₂.2 with table := T }) := by
  obtain ⟨τ₁, d₁⟩ := s₁
  obtain ⟨τ₂, d₂⟩ := s₂
  obtain ⟨hτ, hI, hm⟩ := h
  refine ⟨hτ, invD_table hI T, ?_⟩
  rcases τ₁ with _ | ⟨k, N₀⟩
  · have e : d₁ = d₂ := hm
    rw [e]
  · obtain ⟨w, hs, g⟩ := hm
    exact ⟨w, ⟨hs.tok, rfl, hs.evs, hs.nPlain, hs.viol⟩, g⟩

variable (W p)



end ModeI

end Compile.Batch
