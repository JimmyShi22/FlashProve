-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineWorld.lean: from single steps of a challenger to whole runs against an
adversary that asks for one setup and then for batches.

The lemma on deferred programming (`Rom.Spec.defer`) needs that every run of the adversary against
the challenger ends in a state within given counts. `within_interactB` is the induction on the
adversary, generic in the challenger and in the family of oracles: if an invariant of the
challenger's state and the state of the experiment is kept by every step and does not depend on the
table (`htab`), and the setup makes at most (eS, mS) ordinary and marked queries (counted by
`nPlain`, `nEv`) and a batch at most (eP, mP), then from every state in which it holds, after one
setup and at most n batches the invariant holds and the counts have grown by at most eS + n eP and
mS + n mP.
-/
import Compile.Batch.SpecGlue
import Compile.SpecDiscipline

namespace Compile.Batch.Disc
open Rom Prob
open Compile.GlueB (GCall GIn GAdm)
open Compile.Disc (nEv)

variable {X Wn IVK Pf : Type}

/-- what a call may cost -/
def callCostB {ι : Type} (cS cP : ι → ℕ) : GCall X Wn → ι → ℕ
  | .setup => cS
  | .batch _ => cP

/-- From steps to runs. -/
theorem within_interactB {S : OSpec} {sp : Split S} {α : Type}
    (C : Chall S sp (GCall X Wn) (GIn IVK Pf)) (m : Bool) (Inv : C.τ → DSt S → Prop)
    (eS mS eP mP : S.ι → ℕ) (htab : ∀ s d T, Inv s d → Inv s { d with table := T })
    (hstep : ∀ s d c, Inv s d →
      ∀ y ∈ ((C.step s c).run m d).support,
        Inv y.1.2 y.2 ∧
        ∀ o,
          y.2.nPlain o ≤ d.nPlain o + callCostB eS eP c o ∧
          nEv y.2 o ≤ nEv d o + callCostB mS mP c o)
    (ok : ZKCP.Gen.Batch X Wn → Prop) (A : Adv S (GCall X Wn) (GIn IVK Pf) α) :
    ∀ (b : Bool) (n : ℕ) (s : C.τ) (d : DSt S), GAdm ok A b n → Inv s d →
      ∀ x ∈ (interact (C.world m) A (s, d)).support,
        Inv x.2.1 x.2.2 ∧
        ∀ o,
          x.2.2.nPlain o ≤ d.nPlain o + (if b then 0 else eS o) + n * eP o ∧
          nEv x.2.2 o ≤ nEv d o + (if b then 0 else mS o) + n * mP o := by
  induction A with
  | halt a =>
      intro b n s d _ hI x hx
      rw [interact, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hI,
        fun o =>
          ⟨by rw [Nat.add_assoc]; exact Nat.le_add_right _ _,
            by rw [Nat.add_assoc]; exact Nat.le_add_right _ _⟩⟩
  | sample N k ih =>
      intro b n s d hA hI x hx
      rw [interact, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, _, hr⟩ := hx
      exact ih r b n s d (hA r) hI x hr
  | query o q k ih =>
      intro b n s d hA hI x hx
      rw [interact, PMF.mem_support_bind_iff] at hx
      obtain ⟨y, hy, hr⟩ := hx
      obtain ⟨pr, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      exact ih pr.1 b n s _ (hA pr.1) (htab s d pr.2 hI) x hr
  | call c k ih =>
      intro b n s d hA hI x hx
      rw [interact, PMF.mem_support_bind_iff] at hx
      obtain ⟨y, hy, hr⟩ := hx
      obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      obtain ⟨hI', hc⟩ := hstep s d c hI z hz
      cases c with
      | setup =>
          obtain ⟨rfl, hk⟩ := hA
          obtain ⟨h1, h2⟩ := ih z.1.1 true n z.1.2 z.2 (hk z.1.1) hI' x hr
          refine ⟨h1, fun o => ?_⟩
          have a := h2 o
          have c' := hc o
          simp only [callCostB, if_true, Bool.false_eq_true, if_false] at a c' ⊢
          omega
      | batch bt =>
          cases n with
          | zero => exact hA.elim
          | succ n =>
              obtain ⟨_, _, hk⟩ := hA
              obtain ⟨h1, h2⟩ := ih z.1.1 b n z.1.2 z.2 (hk z.1.1) hI' x hr
              refine ⟨h1, fun o => ?_⟩
              have a := h2 o
              have c' := hc o
              simp only [callCostB] at c'
              rw [Nat.succ_mul, Nat.succ_mul]
              omega

end Compile.Batch.Disc
