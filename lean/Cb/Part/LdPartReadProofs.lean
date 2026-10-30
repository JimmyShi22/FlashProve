-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartReadProofs.lean: the proof of the statement of Cb/Part/LdPartRead.lean
(`ldPartRead_byCol`). Every cell atom whose places lie in the shapes (`R`, `C`), in segments below
n, has the reading with one item a column (`ldPartByCol`).

But for its constant, an affine form in the shapes, in segments below n, is the sum over all places
of its coefficients times the entries (`ldPartRead_coefs`); then sums are exchanged (two tools on
sums of lists: `ldPartRead_mapRange`, `ldPartRead_flatMap`). The analogue of
Cm/TargetReadProofs.lean (`read_byCol` there). Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs. Many statements of this library are written
twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same name
outside that namespace proves it (lean/GLOSSARY.md).

Limits: what the head of Cb/Part/LdPartRead.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartRead
import Blocks.Ext

set_option autoImplicit false

namespace Cb
open Blocks Finset

variable {E : Type} [Field E]

theorem ldPartRead_mapRange {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- One term in the shapes (`h`): the sum over all places picks out the term's own place. -/
theorem ldPartRead_single (n : ℕ) (R C : ℕ → ℕ) (A : ℕ → ℕ → ℕ → E) (w : E) (q : Place)
    (h : q.1 < n ∧ q.2.1 < R q.1 ∧ q.2.2 < C q.1) :
    ∑ s ∈ range n,
        ∑ c ∈ range (C s), ∑ r ∈ range (R s), (if q = (s, r, c) then w else 0) * A s r c =
      w * A q.1 q.2.1 q.2.2 := by
  obtain ⟨q1, q2, q3⟩ := q
  obtain ⟨h1, h2, h3⟩ := h
  rw [sum_eq_single q1, sum_eq_single q3, sum_eq_single q2]
  · rw [if_pos rfl]
  · intro r _ hr
    rw [if_neg (fun e => hr (by simpa using (congrArg (fun z : Place => z.2.1) e).symm)), zero_mul]
  · intro hr
    exact absurd (mem_range.2 h2) hr
  · intro c _ hc
    refine sum_eq_zero fun r _ => ?_
    rw [if_neg (fun e => hc (by simpa using (congrArg (fun z : Place => z.2.2) e).symm)), zero_mul]
  · intro hc
    exact absurd (mem_range.2 h3) hc
  · intro s _ hs
    refine sum_eq_zero fun c _ => sum_eq_zero fun r _ => ?_
    rw [if_neg (fun e => hs (by simpa using (congrArg (fun z : Place => z.1) e).symm)), zero_mul]
  · intro hs
    exact absurd (mem_range.2 h1) hs

theorem ldPartRead_coefs (n : ℕ) (R C : ℕ → ℕ) (A : ℕ → ℕ → ℕ → E) :
    ∀ (l : List (E × Place)), (∀ t ∈ l, t.2.1 < n ∧ t.2.2.1 < R t.2.1 ∧ t.2.2.2 < C t.2.1) →
      ∑ s ∈ range n, ∑ c ∈ range (C s),
          ∑ r ∈ range (R s), (l.map fun t => if t.2 = (s, r, c) then t.1 else 0).sum * A s r c =
        (l.map fun t => t.1 * A t.2.1 t.2.2.1 t.2.2.2).sum
  | [], _ => by simp
  | t :: l, h => by
    simp only [List.map_cons, List.sum_cons, add_mul, sum_add_distrib]
    rw [ldPartRead_single n R C A t.1 t.2 (h t (List.mem_cons_self ..)),
      ldPartRead_coefs n R C A l fun t' ht' => h t' (List.mem_cons_of_mem _ ht')]

theorem ldPartRead_flatMap {α β : Type} (l : List α) (g : α → List β) (h : β → E) :
    ((l.flatMap g).map h).sum = (l.map fun a => ((g a).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem ldPartRead_byCol : Spec.ldPartRead_byCol := by
  intro E _ n R C v f hf A γ
  have hval : ∀ b < 2 ^ v, (f b).val A =
      (f b).c0 +
        ∑ s ∈ range n, ∑ c ∈ range (C s),
          ∑ r ∈ range (R s), ldPartCoefAt (f b) (s, r, c) * A s r c := fun b hb => by
    unfold CForm.val ldPartCoefAt
    rw [ldPartRead_coefs n R C A (f b).terms (hf b hb)]
  rw [ext_congr hval, ext_add]
  congr 1
  show _ = (((List.range n).flatMap fun s =>
        (List.range (C s)).map fun c =>
          (⟨s, fun γ r => ext v (fun b => ldPartCoefAt (f b) (s, r, c)) γ,
            fun _ c' => if c' = c then 1 else 0⟩ : LdPartItem E)).map
      fun t => t.val R C γ A).sum
  rw [ldPartRead_flatMap, ldPartRead_mapRange]
  unfold Blocks.ext
  rw [show (∑ X ∈ range (2 ^ v), eqN v 0 γ X *
      ∑ s ∈ range n, ∑ c ∈ range (C s), ∑ r ∈ range (R s), ldPartCoefAt (f X) (s, r, c) * A s r c)
      = ∑ s ∈ range n, ∑ X ∈ range (2 ^ v), eqN v 0 γ X *
        ∑ c ∈ range (C s), ∑ r ∈ range (R s), ldPartCoefAt (f X) (s, r, c) * A s r c by
    rw [sum_comm]
    exact sum_congr rfl fun X _ => mul_sum _ _ _]
  refine sum_congr rfl fun s _ => ?_
  rw [List.map_map, ldPartRead_mapRange]
  rw [show (∑ X ∈ range (2 ^ v),
      eqN v 0 γ X * ∑ c ∈ range (C s), ∑ r ∈ range (R s), ldPartCoefAt (f X) (s, r, c) * A s r c)
      = ∑ c ∈ range (C s), ∑ X ∈ range (2 ^ v),
        eqN v 0 γ X * ∑ r ∈ range (R s), ldPartCoefAt (f X) (s, r, c) * A s r c by
    rw [sum_comm]
    exact sum_congr rfl fun X _ => mul_sum _ _ _]
  refine sum_congr rfl fun c hc => ?_
  show _ = ∑ r ∈ range (R s), ∑ c' ∈ range (C s),
      (∑ X ∈ range (2 ^ v), eqN v 0 γ X * ldPartCoefAt (f X) (s, r, c)) *
        (if c' = c then 1 else 0) * A s r c'
  rw [show (∑ X ∈ range (2 ^ v),
      eqN v 0 γ X * ∑ r ∈ range (R s), ldPartCoefAt (f X) (s, r, c) * A s r c)
      = ∑ r ∈ range (R s),
        ∑ X ∈ range (2 ^ v), eqN v 0 γ X * (ldPartCoefAt (f X) (s, r, c) * A s r c) by
    rw [sum_comm]
    exact sum_congr rfl fun X _ => mul_sum _ _ _]
  refine sum_congr rfl fun r _ => ?_
  have hr : ∑ c' ∈ range (C s), (∑ X ∈ range (2 ^ v), eqN v 0 γ X * ldPartCoefAt (f X) (s, r, c)) *
        (if c' = c then 1 else 0) * A s r c' =
      (∑ X ∈ range (2 ^ v), eqN v 0 γ X * ldPartCoefAt (f X) (s, r, c)) * A s r c := by
    rw [sum_eq_single c]
    · rw [if_pos rfl, mul_one]
    · intro c' _ hc'
      rw [if_neg hc', mul_zero, zero_mul]
    · intro h
      exact absurd hc h
  rw [hr, sum_mul]
  exact sum_congr rfl fun X _ => (mul_assoc _ _ _).symm

end Cb
