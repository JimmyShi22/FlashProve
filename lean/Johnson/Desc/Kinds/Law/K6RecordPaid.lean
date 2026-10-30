-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6RecordPaid.lean: WHAT Law/K6Stated.lean's TOPS ASK OF THE RECORD BEHIND THE
OUTPUT HEAD's OWN BLOCK, AS FAR AS THIS FILE CAN PAY IT. Statements and proofs.

  apart_of         Law/TabsApart.lean's "no entry lies in two tables' stretches" gives TabsApart.
  tabsApart_at     hApart: AT EVERY RECORD, NO PREMISE: the tables that withTables lays are apart.
  below_at         each table that withTables lays ends below the plan's length of the vector of
                   reads.
  below_of_width   hBelow: so below the width of the reads' array at the record, where that width is
                   no less than the plan's length (hK).
  canonical_of_view, canonical_of_below   where the test on the view says yes the rounds are
                   canonical; a yes of the strict reading of a block (Sound.below) is a yes of the
                   block at canonical rounds.
  heardAt_of_below K6HeardAt behind a yes of the strict reading of K6's block: NO PREMISE ON
                   THE ROUNDS (Law/K6Claims.lean's k6_border asked "Canonical rs").
  ELSEWHERE: hRd: Law/K6Silent.lean's readers_silent (where no tables are laid at the record) ·
                   K6HeardAt: Law/K6Claims.lean's k6_border (behind a yes of K6's block).

WHAT IT IS NOT. hK (the array of the reads is as wide as the plan says) stays a premise. Nothing on
"the lookup's last claim names no entry", nor on the array's name.
Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Stated
import Johnson.Desc.Kinds.Law.K6Silent
import Johnson.Desc.Kinds.Law.TabsApart
import Johnson.Desc.Kinds.Law.HeadTabRows
import Johnson.Desc.Kinds.Law.K6Claims
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S HeadOwn)

/-- Law/TabsApart.lean's sentence StretchesApart gives Law/K6Stated.lean's TabsApart. -/
theorem apart_of {tt : OnBytes.Model.Head.Tables} (hA : StretchesApart tt) : TabsApart tt := by
  intro x hx y hy pos h1 h2
  unfold inStretch at h1 h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  exact hA x hx y hy pos h1.1 h1.2 h2.1 h2.2

/-- **hApart of Law/K6Stated.lean's tops: at every record.** -/
theorem tabsApart_at (P : K8.ReadsQuiet.PH) (s : S) :
    ∀ e o tt, withTables P s = some e → e.here = .head o → o.t = some tt → TabsApart tt := by
  intro e o tt he ho ht
  obtain ⟨a, cov, x, tt', _, _, _, _, h5, rfl⟩ := (withTables_iff P s e).1 he
  injection ho with ho
  subst ho
  obtain rfl : tt' = tt := Option.some.inj ht
  exact apart_of (tables_apart h5).2

/-- Each table ends below the vector's planned length. -/
theorem below_at (P : K8.ReadsQuiet.PH) (s : S) :
    ∀ e o tt, withTables P s = some e → e.here = .head o → o.t = some tt →
      ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ P.hp.nU.getD 2 0 := by
  intro e o tt he ho ht x hx
  obtain ⟨a, cov, x', tt', _, _, _, _, h5, rfl⟩ := (withTables_iff P s e).1 he
  injection ho with ho
  subst ho
  obtain rfl : tt' = tt := Option.some.inj ht
  obtain ⟨h1, h2⟩ := tables_tab_below h5
  rw [← h2]
  exact h1 x hx

/-- **hBelow of Law/K6Stated.lean's tops**, where the reads' array is as wide as the plan says. -/
theorem below_of_width (P : K8.ReadsQuiet.PH) (s : S) (iU3 : Nat)
    (hK : ∀ e F tr, withTables P s = some e → e.fork? = some F → F.trees[iU3]? = some tr →
      P.hp.nU.getD 2 0 ≤ tr.K) :
    ∀ e o tt F tr, withTables P s = some e → e.here = .head o → o.t = some tt →
      e.fork? = some F → F.trees[iU3]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K := by
  intro e o tt F tr he ho ht hF htr x hx
  exact (below_at P s e o tt he ho ht x hx).trans (hK e F tr he hF htr)

/-- **WHERE THE TEST ON THE VIEW SAYS YES, THE ROUNDS ARE CANONICAL**: every element that is sent or
drawn is written with its three words below the prime. -/
theorem canonical_of_view (rs : List Fmt.RoundView) (op : List (Nat × Nat × List UInt64))
    (h : viewWordsBelowPrime ⟨rs, op⟩ = true) : Canonical rs := by
  unfold viewWordsBelowPrime at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  have h1 := h.1 r hr
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h1
  have key : ∀ x : UInt64 × UInt64 × UInt64,
      (Decidable.decide (x.1 < fieldPrimeWord) && Decidable.decide (x.2.1 < fieldPrimeWord) &&
        Decidable.decide (x.2.2 < fieldPrimeWord)) = true → OnBytes.okE (OnBytes.E.ofTriple x) = true :=
    fun _ hx => hx
  exact ⟨fun x hx => key x (h1.2 (Fmt.ItemValue.e x) hx), fun x hx => key x (h1.1 x hx)⟩

/-- **A YES OF THE STRICT READING OF A BLOCK** (Johnson/Desc/Sound/ChainRule.lean: below: the test
on the view in front) **IS A YES OF THE BLOCK AT CANONICAL ROUNDS.** -/
theorem canonical_of_below {Cl : Type} (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below b).decide s rs gs = .ok s') :
    Canonical rs ∧ b.decide s rs gs = .ok s' := by
  have h' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := h
  split at h'
  · rename_i hv
    exact ⟨canonical_of_view rs _ hv, h'⟩
  · cases h'

/-- **K6HeardAt BEHIND A YES OF THE STRICT READING OF THE HEAD's BLOCK**: no premise on the rounds
is left. -/
theorem heardAt_of_below (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hOn : K6On W s)
    (h : (Sound.below b).decide s rs gs = .ok s') :
    K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s' := by
  obtain ⟨hcan, hd⟩ := canonical_of_below b s s' rs gs h
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp hb
  have hr : readsOf W = iU3 := by
    unfold readsOf
    rw [hu]
    rfl
  subst hbb
  have hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s) := hOn.1
  rw [hr] at hWL ⊢
  have hd' : (blockAt W.hS iU3 (workOf W) l).decide s rs gs = .ok s' := hd
  obtain ⟨g, H, F, w, s1, s2, hg, hh, e1, e2, hs'⟩ :=
    decide_hears_at W.hS iU3 (workOf W) l s s' rs gs hd'
  obtain ⟨b1, b2, b3, _⟩ := seatBack_at W.hS iU3 (workOf W) s g rs [] F H w s1 s2 hg
    hWL hcan hh e1 e2
  rw [hs']
  exact ⟨g, H, _, F, rs, b3.trans hg, b2, hWL, hh, by rw [b1]; exact OnBytes.PscRun.Later.refl _⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.canonical_of_view
#print axioms VerifiableInference.Desc.Kinds.Head.Law.canonical_of_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heardAt_of_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tabsApart_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.below_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.below_of_width
