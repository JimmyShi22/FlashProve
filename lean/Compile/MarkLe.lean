-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/MarkLe.lean: how many marked queries a token program makes, read off its text (words of this
library: lean/GLOSSARY.md). Generic in the family of oracles.

The lemma on deferred programming (`Rom.Spec.defer`, Rom/Defer.lean) asks for a bound M o on the
number of marked queries to each oracle o in every run in mode I.

  `MarkLe c M`     Every path of the program c makes at most M o marked queries to o, for every
                   oracle o. By recursion on the text: a marked query to o uses up one of the M o.
  `MarkLe.mono`    A larger bound.
  `MarkLe.bind`    One program after the other: the bounds add up.
  `MarkLe.virt`    The renumbering of tokens (Compile/Step1_life2_Virt.lean) changes nothing.
  `MarkLe.run`     What it means: in every run, in either mode, from every state, the number of
                   records of marked queries to o (`Compile.Disc.nEv`) grows by at most M o.
  `MarkQ c M Q`    The same, and every path ends in a result with the property Q. Inductions over a
                   program use it: how much the second of two programs does may depend on the result
                   of the first (the length of a list, say). `MarkQ.markLe` (forget Q),
                   `MarkQ.of_markLe` (Q = True).

Limits: nothing on the rules for tokens (violations), on plain queries or on the lengths of charged
tokens: for these see Compile/SpecDiscipline.lean and Compile/Batch/SpecDiscipline.lean.
-/
import Compile.Discipline
import Compile.Step1_life2_Virt

namespace Compile
open Rom
open Compile.Disc (nEv releaseAll_fst nEv_map_markDue)

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- Every path of the program makes at most M o marked queries to o. -/
def MarkLe : Step S sp α → (S.ι → ℕ) → Prop
  | .pure _, _ => True
  | .sample _ k, M => ∀ r, MarkLe (k r) M
  | .plain _ _ k, M => ∀ r, MarkLe (k r) M
  | .fresh _ k, M => ∀ t, MarkLe (k t) M
  | .marked o _ _ _ _ k, M => 0 < M o ∧ ∀ v t', MarkLe (k v t') (Function.update M o (M o - 1))
  | .reveal _ k, M => ∀ vs, MarkLe (k vs) M

namespace MarkLe

/-- a larger bound -/
theorem mono {c : Step S sp α} :
    ∀ {M M' : S.ι → ℕ}, MarkLe c M → (∀ o, M o ≤ M' o) → MarkLe c M' := by
  induction c with
  | pure a => intro _ _ _ _; trivial
  | sample n k ih => intro M M' h hM r; exact ih r (h r) hM
  | plain o q k ih => intro M M' h hM r; exact ih r (h r) hM
  | fresh ℓ k ih => intro M M' h hM t; exact ih t (h t) hM
  | marked o t us pt inj k ih =>
    intro M M' h hM
    refine ⟨lt_of_lt_of_le h.1 (hM o), fun v t' => ih v t' (h.2 v t') fun o' => ?_⟩
    by_cases ho : o' = o
    · subst ho
      simp only [Function.update_self]
      exact Nat.sub_le_sub_right (hM o') 1
    · simp only [Function.update_of_ne ho]
      exact hM o'
  | reveal ts k ih => intro M M' h hM vs; exact ih vs (h vs) hM

/-- One after the other: the bounds add up. -/
theorem bind {c : Step S sp α} {g : α → Step S sp β} {M₂ : S.ι → ℕ} (hg : ∀ a, MarkLe (g a) M₂) :
    ∀ {M₁ : S.ι → ℕ}, MarkLe c M₁ → MarkLe (c.bind g) fun o => M₁ o + M₂ o := by
  induction c with
  | pure a => intro M₁ _; exact (hg a).mono fun o => Nat.le_add_left _ _
  | sample n k ih => intro M₁ h r; exact ih r (h r)
  | plain o q k ih => intro M₁ h r; exact ih r (h r)
  | fresh ℓ k ih => intro M₁ h t; exact ih t (h t)
  | marked o t us pt inj k ih =>
    intro M₁ h
    refine ⟨Nat.add_pos_left h.1 _, fun v t' => (ih v t' (h.2 v t')).mono fun o' => ?_⟩
    by_cases ho : o' = o
    · subst ho
      simp only [Function.update_self]
      have := h.1
      omega
    · simp only [Function.update_of_ne ho]
      exact le_rfl
  | reveal ts k ih => intro M₁ h vs; exact ih vs (h vs)

/-- a program without marked queries, then another -/
theorem bind_zero {c : Step S sp α} {g : α → Step S sp β} {M : S.ι → ℕ}
    (hc : MarkLe c fun _ => 0) (hg : ∀ a, MarkLe (g a) M) : MarkLe (c.bind g) M :=
  (bind hg hc).mono fun o => by simp

/-- the renumbering of tokens changes nothing -/
theorem virt (N₀ δ : ℕ) {c : Step S sp α} :
    ∀ {M : S.ι → ℕ}, MarkLe c M → MarkLe (Life2.virt N₀ δ c) M := by
  induction c with
  | pure a => intro _ _; trivial
  | sample n k ih => intro M h r; exact ih r (h r)
  | plain o q k ih => intro M h r; exact ih r (h r)
  | fresh ℓ k ih => intro M h t; exact ih _ (h _)
  | marked o t us pt inj k ih => intro M h; exact ⟨h.1, fun v t' => ih v _ (h.2 v _)⟩
  | reveal ts k ih => intro M h vs; exact ih vs (h vs)

private theorem nEv_snoc (d : DSt S) (e : Ev S) (T : Table S) (vals : List Bits)
    (viol : Bool) (o : S.ι) :
    nEv ({ d with table := T, vals := vals, evs := d.evs ++ [e], viol := viol } : DSt S) o =
      nEv d o + if e.o = o then 1 else 0 := by
  show ((d.evs ++ [e]).filter fun v => decide (v.o = o)).length = _
  rw [List.filter_append, List.length_append]
  by_cases h : e.o = o
  · simp [nEv, h]
  · simp [nEv, h]

/-- What it means: in every run the number of records of marked queries to o grows by at most M
o. -/
theorem run (m : Bool) {c : Step S sp α} :
    ∀ {M : S.ι → ℕ} (d : DSt S),
      MarkLe c M → ∀ x ∈ (c.run m d).support, ∀ o, nEv x.2 o ≤ nEv d o + M o := by
  induction c with
  | pure a =>
    intro M d _ x hx o
    rw [Step.run, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    exact Nat.le_add_right _ _
  | sample n k ih =>
    intro M d h x hx o
    rw [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    exact ih r d (h r) x hr o
  | plain o' q k ih =>
    intro M d h x hx o
    rw [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨pr, -, hr⟩ := hx
    have h1 := ih pr.1 _ (h pr.1) x hr o
    exact h1
  | fresh ℓ k ih =>
    intro M d h x hx o
    rw [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨u, -, hr⟩ := hx
    have h1 := ih _ _ (h _) x hr o
    exact h1
  | marked o' t us pt inj k ih =>
    intro M d h x hx o
    have key : ∀ (r : S.Rng o') (T : Table S) (viol : Bool), x ∈
          ((k (sp.split o' r).1 d.vals.length).run m
            { d with
              table := T, vals := d.vals ++ [List.ofFn (sp.split o' r).2],
              evs := d.evs ++ [⟨o', pt (d.val t) (us.map d.val), r, t, us, d.vals.length, false⟩],
              viol := viol }).support →
        nEv x.2 o ≤ nEv d o + M o := by
      intro r T viol hr
      have h1 := ih _ _ _ (h.2 _ _) x hr o
      rw [nEv_snoc] at h1
      have h0 := h.1
      by_cases ho : o' = o
      · subst ho
        simp only [Function.update_self, if_true] at h1
        omega
      · have ho' : o ≠ o' := fun e => ho e.symm
        simp only [Function.update_of_ne ho', if_neg ho] at h1
        omega
    rw [Step.run] at hx
    cases m with
    | true =>
      simp only [if_true] at hx
      rw [PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hr⟩ := hx
      exact key r _ _ hr
    | false =>
      simp only [Bool.false_eq_true, if_false] at hx
      rw [PMF.mem_support_bind_iff] at hx
      obtain ⟨pr, -, hr⟩ := hx
      exact key pr.1 _ _ hr
  | reveal ts k ih =>
    intro M d h x hx o
    rw [Step.run] at hx
    simp only [releaseAll_fst] at hx
    have h1 := ih _ _ (h _) x hx o
    have e : ∀ (T : Table S) (sh : List Tok) (viol : Bool),
        nEv ({ d with
               table := T, shown := sh,
               evs := d.evs.map (Disc.markDue (d.shown ++ ts)), viol := viol } : DSt S) o =
          nEv d o :=
      fun _ _ _ => nEv_map_markDue _ _ _
    rw [e] at h1
    exact h1

end MarkLe

/-- Every path of the program makes at most M o marked queries to o and ends in a result with the
property Q. -/
def MarkQ : Step S sp α → (S.ι → ℕ) → (α → Prop) → Prop
  | .pure a, _, Q => Q a
  | .sample _ k, M, Q => ∀ r, MarkQ (k r) M Q
  | .plain _ _ k, M, Q => ∀ r, MarkQ (k r) M Q
  | .fresh _ k, M, Q => ∀ t, MarkQ (k t) M Q
  | .marked o _ _ _ _ k, M, Q => 0 < M o ∧ ∀ v t', MarkQ (k v t') (Function.update M o (M o - 1)) Q
  | .reveal _ k, M, Q => ∀ vs, MarkQ (k vs) M Q

namespace MarkQ

theorem markLe {c : Step S sp α} {Q : α → Prop} : ∀ {M : S.ι → ℕ}, MarkQ c M Q → MarkLe c M := by
  induction c with
  | pure a => intro _ _; trivial
  | sample n k ih => intro M h r; exact ih r (h r)
  | plain o q k ih => intro M h r; exact ih r (h r)
  | fresh ℓ k ih => intro M h t; exact ih t (h t)
  | marked o t us pt inj k ih => intro M h; exact ⟨h.1, fun v t' => ih v t' (h.2 v t')⟩
  | reveal ts k ih => intro M h vs; exact ih vs (h vs)

theorem of_markLe {c : Step S sp α} : ∀ {M : S.ι → ℕ}, MarkLe c M → MarkQ c M fun _ => True := by
  induction c with
  | pure a => intro _ _; trivial
  | sample n k ih => intro M h r; exact ih r (h r)
  | plain o q k ih => intro M h r; exact ih r (h r)
  | fresh ℓ k ih => intro M h t; exact ih t (h t)
  | marked o t us pt inj k ih => intro M h; exact ⟨h.1, fun v t' => ih v t' (h.2 v t')⟩
  | reveal ts k ih => intro M h vs; exact ih vs (h vs)

/-- a larger bound, a weaker property -/
theorem mono {c : Step S sp α} {Q Q' : α → Prop} (hQ : ∀ a, Q a → Q' a) :
    ∀ {M M' : S.ι → ℕ}, MarkQ c M Q → (∀ o, M o ≤ M' o) → MarkQ c M' Q' := by
  induction c with
  | pure a => intro _ _ h _; exact hQ a h
  | sample n k ih => intro M M' h hM r; exact ih r (h r) hM
  | plain o q k ih => intro M M' h hM r; exact ih r (h r) hM
  | fresh ℓ k ih => intro M M' h hM t; exact ih t (h t) hM
  | marked o t us pt inj k ih =>
    intro M M' h hM
    refine ⟨lt_of_lt_of_le h.1 (hM o), fun v t' => ih v t' (h.2 v t') fun o' => ?_⟩
    by_cases ho : o' = o
    · subst ho
      simp only [Function.update_self]
      exact Nat.sub_le_sub_right (hM o') 1
    · simp only [Function.update_of_ne ho]
      exact hM o'
  | reveal ts k ih => intro M M' h hM vs; exact ih vs (h vs) hM

/-- One after the other: the bounds add up; the second program is looked at only for results with
the property Q, which all results of the first have. -/
theorem bind {c : Step S sp α} {g : α → Step S sp β} {Q : α → Prop} {Q' : β → Prop}
    {M₂ : S.ι → ℕ} (hg : ∀ a, Q a → MarkQ (g a) M₂ Q') :
    ∀ {M₁ : S.ι → ℕ}, MarkQ c M₁ Q → MarkQ (c.bind g) (fun o => M₁ o + M₂ o) Q' := by
  induction c with
  | pure a => intro M₁ h; exact (hg a h).mono (fun _ x => x) fun o => Nat.le_add_left _ _
  | sample n k ih => intro M₁ h r; exact ih r (h r)
  | plain o q k ih => intro M₁ h r; exact ih r (h r)
  | fresh ℓ k ih => intro M₁ h t; exact ih t (h t)
  | marked o t us pt inj k ih =>
    intro M₁ h
    refine ⟨Nat.add_pos_left h.1 _,
      fun v t' => (ih v t' (h.2 v t')).mono (fun _ x => x) fun o' => ?_⟩
    by_cases ho : o' = o
    · subst ho
      simp only [Function.update_self]
      have := h.1
      omega
    · simp only [Function.update_of_ne ho]
      exact le_rfl
  | reveal ts k ih => intro M₁ h vs; exact ih vs (h vs)

/-- one after the other, with one bound for both -/
theorem bind_le {c : Step S sp α} {g : α → Step S sp β} {Q : α → Prop}
    {Q' : β → Prop} {M₁ M₂ M : S.ι → ℕ} (hc : MarkQ c M₁ Q)
    (hg : ∀ a, Q a → MarkQ (g a) M₂ Q') (hM : ∀ o, M₁ o + M₂ o ≤ M o) : MarkQ (c.bind g) M Q' :=
  (bind hg hc).mono (fun _ x => x) hM

/-- a marked query to o, then what follows -/
theorem marked {o : S.ι} {t : Tok} {us : List Tok} {pt : Bits → List Bits → S.Dom o}
    {inj : ∀ vs, Function.Injective fun v => pt v vs} {k : sp.Vis o → Tok → Step S sp α}
    {M : S.ι → ℕ} {Q : α → Prop} (h : ∀ v t', MarkQ (k v t') M Q) :
    MarkQ (.marked o t us pt inj k) (fun o' => Disc.cnt1 o 1 o' + M o') Q := by
  refine ⟨by simp [Disc.cnt1], fun v t' => (h v t').mono (fun _ x => x) fun o' => ?_⟩
  by_cases ho : o' = o
  · subst ho
    simp [Disc.cnt1]
  · simp [Function.update_of_ne ho]

end MarkQ

end Compile
