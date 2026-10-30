-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Overrun.lean: stopping before a leaf is used too often, for any two challengers (`World`).

W₂ is W₁ with a counter for each leaf (a leaf: one of the M + 1 indices in `Fin (M + 1)`). Its
state is mapped to a state of W₁ by fg (forget the counters), and ctr reads the counters. Oracle
queries are answered alike and change no counter. A call, from a given state, is of one of two
kinds:
    Quiet   both challengers reply alike, and no counter rises;
    Draw    both make the same first moves (any distribution pre), then sample a leaf j uniformly;
            if the counter of j is below s1 both go on alike and W₂ counts j once more;
            otherwise the two may differ in any way.
Only calls with the property P may be of the second kind, and the adversary makes at most n calls
with P on every path (`Adv.CallBound`). Then the views differ by at most
`Prob.overPotential s1 (counters) n`, which at counters 0 is `Prob.pOver (number of leaves) s1 n`
(`tv_le_potential`, `tv_le_pOver`).

The proof is an induction on the adversary with the potential of Prob/Tail.lean: Draw keeps it on
average; after an overrun (some counter above s1) it is at least 1.
-/
import Rom.World
import Prob.Tail

open scoped ENNReal
open Prob

namespace Rom

variable {S : OSpec} {Out In α : Type}

/-- at most n calls with the property P, on every path -/
def Adv.CallBound (P : Out → Prop) : Adv S Out In α → ℕ → Prop
  | .halt _, _ => True
  | .sample _ k, n => ∀ r, (k r).CallBound P n
  | .query _ _ k, n => ∀ r, (k r).CallBound P n
  | .call m k, n => (P m → ∃ n', n = n' + 1 ∧ ∀ a, (k a).CallBound P n') ∧ (¬ P m → ∀ a, (k a).CallBound P n)

namespace Overrun

/-- A challenger and the same challenger with a counter for each of M + 1 leaves. -/
structure Pair (W₁ W₂ : World S Out In) (M : ℕ) where
  fg : W₂.σ → W₁.σ
  ctr : W₂.σ → Fin (M + 1) → ℕ

variable {W₁ W₂ : World S Out In} {M : ℕ} (D : Pair W₁ W₂ M)

/-- both challengers reply alike, and no counter rises -/
def Quiet (s : W₂.σ) (m : Out) : Prop :=
  W₁.reply (D.fg s) m = (W₂.reply s m).map (Prod.map id D.fg) ∧
  ∀ x ∈ (W₂.reply s m).support, ∀ j, D.ctr x.2 j ≤ D.ctr s j

/-- the same first moves, then a uniform leaf j; below s1 both go on alike and j is counted once
more -/
def Draw (s1 : ℕ) (s : W₂.σ) (m : Out) : Prop :=
  ∃ (β : Type) (pre : PMF β) (K₁ : β → Fin (M + 1) → PMF (In × W₁.σ))
      (K₂ : β → Fin (M + 1) → PMF (In × W₂.σ)),
    W₁.reply (D.fg s) m =
      pre.bind (fun b => (PMF.uniformOfFintype (Fin (M + 1))).bind fun j => K₁ b j) ∧
    W₂.reply s m = pre.bind (fun b => (PMF.uniformOfFintype (Fin (M + 1))).bind fun j => K₂ b j) ∧
    ∀ b j, D.ctr s j < s1 →
      K₁ b j = (K₂ b j).map (Prod.map id D.fg) ∧
      ∀ x ∈ (K₂ b j).support, D.ctr x.2 = Function.update (D.ctr s) j (D.ctr s j + 1)

/-- what is required of the two challengers -/
structure Laws (s1 : ℕ) (P : Out → Prop) : Prop where
  answer : ∀ s o q, W₁.answer (D.fg s) o q = (W₂.answer s o q).map (Prod.map id D.fg)
  answer_ctr : ∀ s o q, ∀ x ∈ (W₂.answer s o q).support, D.ctr x.2 = D.ctr s
  reply : ∀ s m, Quiet D s m ∨ (P m ∧ Draw D s1 s m)

/-- larger counters have a larger potential -/
theorem overPotential_mono_ctr
    {L : Type} [Fintype L] (s : ℕ) {c c' : L → ℕ} (h : ∀ k, c k ≤ c' k) (m : ℕ) :
    overPotential s c m ≤ overPotential s c' m :=
  Finset.sum_le_sum fun k _ => hitTail_anti _ _ (Nat.sub_le_sub_left (h k) _)

variable {D}

/-- Stopping before a leaf is used more than s1 times, from any state: under `Laws`, for an
adversary with at most n calls with P, the outputs differ by at most the potential of the counters.
-/
theorem tv_le_potential {s1 : ℕ} {P : Out → Prop} (hD : Laws D s1 P) (A : Adv S Out In α) :
    ∀ (n : ℕ) (s : W₂.σ), A.CallBound P n →
      tv ((interact W₁ A (D.fg s)).map Prod.fst) ((interact W₂ A s).map Prod.fst) ≤
        overPotential s1 (D.ctr s) n := by
  induction A with
  | halt a =>
    intro n s _
    simp only [interact, PMF.pure_map, tv_self]
    exact zero_le _
  | sample m k ih =>
    intro n s hA
    simp only [interact, PMF.map_bind]
    exact tv_bind_right_le_of_forall _ _ _ fun r _ => ih r n s (hA r)
  | query o q k ih =>
    intro n s hA
    simp only [interact, PMF.map_bind]
    rw [hD.answer s o q, PMF.bind_map]
    refine tv_bind_right_le_of_forall _ _ _ fun x hx => ?_
    have h := ih x.1 n x.2 (hA x.1)
    rw [hD.answer_ctr s o q x hx] at h
    exact h
  | call m k ih =>
    intro n s hA
    simp only [interact, PMF.map_bind]
    -- a quiet call, with n' calls left afterwards
    have hquiet : Quiet D s m →
        ∀ n', n' ≤ n → (∀ a, (k a).CallBound P n') →
          tv ((W₁.reply (D.fg s) m).bind fun p => (interact W₁ (k p.1) p.2).map Prod.fst)
              ((W₂.reply s m).bind fun p => (interact W₂ (k p.1) p.2).map Prod.fst) ≤
            overPotential s1 (D.ctr s) n := by
      intro hq n' hn hk
      rw [hq.1, PMF.bind_map]
      refine tv_bind_right_le_of_forall _ _ _ fun x hx => ?_
      exact ((ih x.1 n' x.2 (hk x.1)).trans (overPotential_mono_ctr s1 (hq.2 x hx) n')).trans
        (overPotential_mono s1 _ hn)
    rcases hD.reply s m with hq | ⟨hP, β, pre, K₁, K₂, h1, h2, h3⟩
    · by_cases hP : P m
      · obtain ⟨n', rfl, hk⟩ := hA.1 hP
        exact hquiet hq n' (Nat.le_succ _) hk
      · exact hquiet hq n le_rfl (hA.2 hP)
    · obtain ⟨n', rfl, hk⟩ := hA.1 hP
      rw [h1, h2]
      simp only [PMF.bind_bind]
      refine tv_bind_right_le_of_forall _ _ _ fun b _ => ?_
      refine (tv_bind_right_le _ _ _).trans ?_
      rw [← avg_overPotential, expect_unif_sum]
      refine Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl ?_
      by_cases hj : D.ctr s j < s1
      · obtain ⟨e1, e2⟩ := h3 b j hj
        rw [e1, PMF.bind_map]
        refine tv_bind_right_le_of_forall _ _ _ fun x hx => ?_
        have h := ih x.1 n' x.2 (hk x.1)
        rw [e2 x hx] at h
        exact h
      · refine (tv_le_one _ _).trans (one_le_overPotential _ _ _ ⟨j, ?_⟩)
        rw [Function.update_self]
        omega

/-- `tv_le_potential` from a state with all counters 0. -/
theorem tv_le_pOver {s1 : ℕ} {P : Out → Prop} (hD : Laws D s1 P) (A : Adv S Out In α) (n : ℕ)
    (s : W₂.σ) (hs : D.ctr s = fun _ => 0) (hA : A.CallBound P n) :
    tv ((interact W₁ A (D.fg s)).map Prod.fst) ((interact W₂ A s).map Prod.fst) ≤
      pOver (M + 1) s1 n := by
  have h := tv_le_potential hD A n s hA
  rwa [hs, overPotential_zero, Fintype.card_fin] at h

end Overrun
end Rom
