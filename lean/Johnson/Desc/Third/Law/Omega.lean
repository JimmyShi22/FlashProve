--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Third/Law/Omega.lean: from the shared chain's book to the declared rounds of the last
chain's own test. Theorems.

Main names:
  `omega_tied`: if K14's second part says yes from s₀ to s₁ and the sources are tied at s₁ to the
    declared rounds of the block `own`, then some round of `own` opens, under the label n, a tree
    with the source "taken from chain 1, number n", n the number of Omega's tree in the shared
    chain's book. So the decision's book and what the compiler is handed name one tree for Omega.
  `no_round_not_tied`: a control: behind K14's second part's yes the sources are not tied to a block
    that declares no round.

Limits. Which of a round's openings is Omega's, where two trees bear one number, is not stated.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Book
import Johnson.Desc.Third.Law.Sources

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Later

namespace VerifiableInference.Desc.Third.Law

theorem obind_ok {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- A mapM in Option that returns: every member was mapped, and its value is in the list returned.
-/
theorem mapM_some_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → ∀ a ∈ l, ∃ b, f a = some b ∧ b ∈ r := by
  intro l
  induction l with
  | nil =>
    intro r _ a ha
    cases ha
  | cons x l ih =>
    intro r h a ha
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := obind_ok h
    obtain ⟨bs, hbs, h⟩ := obind_ok h
    have e : b :: bs = r := Option.some.inj h
    subst e
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]
      exact ⟨b, hb, List.Mem.head _⟩
    · obtain ⟨c, hc, hm⟩ := ih bs hbs a ha
      exact ⟨c, hc, List.Mem.tail _ hm⟩

/-- **Omega's tree is declared as taken from the shared chain, under the number that it has in the
shared chain's book.** -/
theorem omega_tied {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) (s₀ s₁ : S₃) (r₀ : List Fmt.RoundView)
    (g₀ : List (List (Nat × List UInt64)))
    (h₀ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ r₀ g₀ = .ok s₁) (ht : Tied own s₁) :
    ∃ (x : Border) (q : Nat × Nat) (t : Tree), s₀.loc.border = some x ∧
      x.shared.book.place[x.shared.omega]? = some q ∧ x.shared.book.trees[q.1]? = some t ∧
      opensTaken own.rounds 1 t.number = true := by
  obtain ⟨_, _, G, dot, _, hl, _, _, _, _, _, _, _, _, hg, _⟩ := says_k14Second p s₀ s₁ r₀ g₀ h₀
  obtain ⟨x, q, t, q', hx, hq, htr, _, hq', _, ⟨tO, hO, hn, _⟩, _⟩ :=
    bookSays_k14Second p s₀ s₁ r₀ g₀ h₀
  obtain ⟨ts, h1, h2, _⟩ := ht
  have lo : s₁.loc.own = s₀.loc.own := by
    have t := congrArg Loc₃.own hl
    exact t
  have lm : s₁.loc.omega = s₀.st.oracles.size := by
    have t := congrArg Loc₃.omega hl
    exact t
  unfold takenOf at h1
  rw [lo, hg] at h1
  have hin : s₀.st.oracles.size ∈
      (G.members.insertIdxIfInBounds (G.members.filter (· < s₀.st.oracles.size)).size
        s₀.st.oracles.size).toList ++ s₁.loc.mask.toList :=
    List.mem_append_left _
      (Array.mem_toList_iff.2 (self_mem_insertIdxIfInBounds _ _ _ (size_filter_le' _ _)))
  obtain ⟨b, hb, hbm⟩ := mapM_some_mem _ _ _ h1 _ hin
  simp [hq', hO, lm] at hb
  have hall := List.all_eq_true.1 h2 b hbm
  rw [← hb] at hall
  refine ⟨x, q, t, hx, hq, htr, ?_⟩
  rw [← hn]
  exact hall

/-- **A control**: behind K14's second part's yes the sources are not tied to a block that declares
no round. -/
theorem no_round_not_tied {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) (hr : own.rounds = [])
    (s₀ s₁ : S₃) (r₀ : List Fmt.RoundView) (g₀ : List (List (Nat × List UInt64)))
    (h₀ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ r₀ g₀ = .ok s₁) : ¬ Tied own s₁ := by
  intro ht
  obtain ⟨_, _, t, _, _, _, h⟩ := omega_tied p own s₀ s₁ r₀ g₀ h₀ ht
  rw [hr] at h
  cases h

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.no_round_not_tied
#print axioms VerifiableInference.Desc.Third.Law.mapM_some_mem
#print axioms VerifiableInference.Desc.Third.Law.omega_tied
