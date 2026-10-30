-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Form.lean: affine forms, their values, masked scalars, and a segment's deferred claims.
(Words of this library: lean/GLOSSARY.md.)

Entries. N indexes the entries of vectors and pad vectors on which forms may depend, and y : N → E
gives their contents. This is the implicit part of a statement, as far as forms depend on it. A
block that sends no vector works with one fixed N. Where the set of entries grows, forms and
deferred claims are transported along a map of entries (`Form.push`, `Ledger.push`); and the value
of a form depends only on the entries at which it has a non-zero coefficient (`Form.val_congr`).

Forms. Forms are affine in values of masked scalars and in entries of vectors. The value of a masked
scalar is the scalar, which the verifier holds, minus an entry of a pad vector. So every form is an
affine function of the entries y, with coefficients and a constant term that the verifier computes;
the masked scalars enter the constant term only. So a form is given here by a coefficient for each
entry and the constant term at `none`. Forms are a module, and the value is linear in the form
(`Form.val`).

Claims. During a segment the verifier defers claims: LIN(f), the value of f is 0; and REL(f; ∑ c ·
o_i · o_j), the value of f is the sum of the products of the values of opened forms. The opened
forms of a segment are in one list, and the terms of a REL refer to them by their indices. A third
kind, OPEN(f), would be about an element ô and a challenge ς that are sent only in the closing of
the segment. So before the closing it has no truth value, and here it is not a claim: the opened
forms are listed, and the equation ô_i = ς val(f_i) + η_i is a step of the closing's soundness proof
(Blocks/ClosingBlock.lean). The deferred claims are stored as lists (`Ledger`), so that every block
can add to them and no type depends on a length.
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Blocks.Basic

set_option autoImplicit false

namespace Blocks

/-- A form: an affine function of the entries, given by its constant term (at none) and its
coefficients. -/
abbrev Form (N E : Type) : Type := Option N → E

namespace Form

variable {N E : Type} [Fintype N] [CommRing E]

/-- The value of a form, linear in the form. -/
def val (y : N → E) : Form N E →ₗ[E] E where
  toFun f := f none + ∑ n, f (some n) * y n
  map_add' f g := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum, mul_assoc]

theorem val_apply (y : N → E) (f : Form N E) : val y f = f none + ∑ n, f (some n) * y n := rfl

omit [Fintype N] in
/-- The constant form. -/
def const (c : E) : Form N E := fun o => o.elim c fun _ => 0

/-- The form whose value is one entry. -/
def ent [DecidableEq N] (n : N) : Form N E := fun o => o.elim 0 fun m => if m = n then 1 else 0

/-- The form of a masked scalar: the scalar s, whose pad is the entry p, has the value s - y p. -/
def masked [DecidableEq N] (s : E) (p : N) : Form N E := const s - ent p

@[simp] theorem val_const (y : N → E) (c : E) : val y (const c) = c := by
  simp [val_apply, const]

@[simp] theorem val_ent [DecidableEq N] (y : N → E) (n : N) : val y (ent n) = y n := by
  simp [val_apply, ent]

@[simp] theorem val_masked [DecidableEq N] (y : N → E) (s : E) (p : N) :
    val y (masked s p) = s - y p := by
  unfold masked
  rw [map_sub, val_const, val_ent]

/-- The value depends only on the entries at which the form has a coefficient other than 0. -/
theorem val_congr {y y' : N → E} {f : Form N E} (h : ∀ n, f (some n) ≠ 0 → y n = y' n) :
    val y f = val y' f := by
  rw [val_apply, val_apply]
  refine congrArg (f none + ·) (Finset.sum_congr rfl fun n _ => ?_)
  by_cases hn : f (some n) = 0
  · rw [hn, zero_mul, zero_mul]
  · rw [h n hn]

/-- A form transported along a map σ of entries: the entry n becomes σ n. -/
def push {N' : Type} [DecidableEq N'] (σ : N → N') (f : Form N E) : Form N' E :=
  fun o => o.elim (f none) fun n' => ∑ n, if σ n = n' then f (some n) else 0

/-- The transported form has on y' the value that the form has on the entries y' (σ n). -/
theorem val_push {N' : Type} [Fintype N'] [DecidableEq N'] (σ : N → N')
    (f : Form N E) (y' : N' → E) :
    val y' (push σ f) = val (fun n => y' (σ n)) f := by
  rw [val_apply, val_apply]
  refine congrArg (f none + ·) ?_
  show ∑ n', (∑ n, if σ n = n' then f (some n) else 0) * y' n' = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem push_zero {N' : Type} [DecidableEq N'] (σ : N → N') : push σ (0 : Form N E) = 0 := by
  funext o
  cases o <;> simp [push]

end Form

/-! ## Sums of products -/

section Terms

variable {E : Type} [CommRing E]

/-- ∑ c · o_i · o_j over a list of terms (c, i, j). -/
def termSum (o : ℕ → E) (ts : List (E × ℕ × ℕ)) : E := (ts.map fun t => t.1 * o t.2.1 * o t.2.2).sum

/-- ∑ c · (o_i η_j + o_j η_i): the mixed part of ∑ c · (o_i + η_i)(o_j + η_j). -/
def termCross (o η : ℕ → E) (ts : List (E × ℕ × ℕ)) : E :=
  (ts.map fun t => t.1 * (o t.2.1 * η t.2.2 + o t.2.2 * η t.2.1)).sum

/-- The polynomial of a REL: ∑ c (T o_i + η_i)(T o_j + η_j) = T² ∑ c o_i o_j + T ∑ c (o_i η_j + o_j
η_i) + ∑ c η_i η_j. -/
theorem termSum_line (T : E) (o η : ℕ → E) (ts : List (E × ℕ × ℕ)) :
    termSum (fun i => T * o i + η i) ts =
      T ^ 2 * termSum o ts + T * termCross o η ts + termSum η ts := by
  unfold termSum termCross
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem termSum_congr {o o' : ℕ → E} (h : ∀ i, o i = o' i) (ts : List (E × ℕ × ℕ)) :
    termSum o ts = termSum o' ts := by
  rw [funext h]

end Terms

/-! ## The deferred claims of a segment -/

/-- The deferred claims of a segment, as lists. -/
structure Ledger (N E : Type) where
  /-- LIN(f): the value of f is 0 -/
  lin : List (Form N E)
  /-- the opened forms -/
  opn : List (Form N E)
  /-- REL(f; terms): the value of f is ∑ c · o_i · o_j, where o_i is the value of the opened form
  number i -/
  rel : List (Form N E × List (E × ℕ × ℕ))

namespace Ledger

variable {N E : Type} [Fintype N] [CommRing E]

/-- The value of the opened form number i (0 beyond the end of the list). -/
def opv (x : Ledger N E) (y : N → E) (i : ℕ) : E := Form.val y (x.opn.getD i 0)

/-- All deferred claims are true. -/
def True (x : Ledger N E) (y : N → E) : Prop :=
  (∀ f ∈ x.lin, Form.val y f = 0) ∧ ∀ r ∈ x.rel, Form.val y r.1 = termSum (x.opv y) r.2

omit [Fintype N] [CommRing E] in
/-- No deferred claims. -/
def empty : Ledger N E := ⟨[], [], []⟩

theorem true_empty (y : N → E) : (empty : Ledger N E).True y :=
  ⟨fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (List.not_mem_nil)⟩

/-- The deferred claims transported along a map of entries. -/
def push {N' : Type} [DecidableEq N'] (σ : N → N') (x : Ledger N E) : Ledger N' E :=
  ⟨x.lin.map (Form.push σ), x.opn.map (Form.push σ), x.rel.map fun r => (Form.push σ r.1, r.2)⟩

/-- The transported claims are true on y' iff the claims are true on the entries y' (σ n). -/
theorem true_push {N' : Type} [Fintype N'] [DecidableEq N'] (σ : N → N')
    (x : Ledger N E) (y' : N' → E) :
    (x.push σ).True y' ↔ x.True fun n => y' (σ n) := by
  have hov : ∀ i, (x.push σ).opv y' i = x.opv (fun n => y' (σ n)) i := fun i => by
    show Form.val y' ((x.opn.map (Form.push σ)).getD i 0) =
      Form.val (fun n => y' (σ n)) (x.opn.getD i 0)
    rw [← Form.push_zero σ, List.getD_map, Form.val_push]
  unfold True
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun r hr => ?_⟩
    · rw [← Form.val_push]
      exact h1 _ (List.mem_map_of_mem hf)
    · rw [← Form.val_push, ← termSum_congr hov]
      exact h2 (Form.push σ r.1, r.2)
        (List.mem_map_of_mem
          (f := fun r : Form N E × List (E × ℕ × ℕ) => (Form.push σ r.1, r.2)) hr)
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun r hr => ?_⟩
    · obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
      rw [Form.val_push]
      exact h1 f' hf'
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      rw [Form.val_push, termSum_congr hov]
      exact h2 r' hr'

end Ledger

end Blocks
