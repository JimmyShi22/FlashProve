-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadFn.lean: a lookup call's key vector as a function on the call's columns.

Johnson/Road/HeadCols.lean compares the form of a lookup call of the output head's sub-proof with
any function on columns and positions that has each segment's keys in the segment's columns and the
padding key in the columns without a mark (KeyFn). This file shows that such a function exists
whenever the verifier's marking of the columns does not refuse, and that what holds of all its
values holds of every key of every segment.

Main definitions: FnInv (what the construction keeps).
Main theorems: exists_keyFn; keys_of_fn.

What is not claimed. Nothing is said about what a lookup shows. The program does not import this
file.
-/
import Johnson.Road.HeadCols

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset

section Fn

variable {K : Type}

/-- What the construction keeps. S c k says that column c has been given the keys k. Every such
column bears a mark and f has these keys there; in a column without a mark f is pad. -/
def FnInv (w : Array ℕ) (pad : ℕ → K) (S : ℕ → (ℕ → K) → Prop) (f : ℕ → ℕ → K) : Prop :=
  (∀ c k, S c k → w.getD c 0 ≠ 0 ∧ f c = k) ∧ ∀ j, w.getD j 0 = 0 → f j = pad

/-- One column more. -/
theorem fn_step {w : Array ℕ} {p m : ℕ} (hp : p < w.size) (h0 : w.getD p 1 = 0) (hm : m ≠ 0)
    {pad : ℕ → K} {S : ℕ → (ℕ → K) → Prop} {f : ℕ → ℕ → K} (I : FnInv w pad S f) (k : ℕ → K) :
    FnInv (w.set! p m) pad (fun c k' => S c k' ∨ (c = p ∧ k' = k)) (Function.update f p k) := by
  rw [Array.set!_eq_setIfInBounds]
  have h00 : w.getD p 0 = 0 := by simpa [Array.getD, hp] using h0
  refine ⟨?_, ?_⟩
  · rintro c k' (hS | ⟨rfl, rfl⟩)
    · obtain ⟨a, b⟩ := I.1 c k' hS
      have hne : c ≠ p := fun e => a (e ▸ h00)
      rw [getD_set_ne w (fun e => hne e.symm) m, Function.update_of_ne hne]
      exact ⟨a, b⟩
    · rw [getD_set_self w hp m, Function.update_self]
      exact ⟨hm, rfl⟩
  · intro j hj
    have hne : j ≠ p := by
      intro e
      rw [e, getD_set_self w hp m] at hj
      exact hm hj
    rw [getD_set_ne w (fun e => hne e.symm) m] at hj
    rw [Function.update_of_ne hne]
    exact I.2 j hj

/-- The columns pos 0, ..., pos (n - 1), one after the other. -/
theorem fold_fn (pos mk : ℕ → ℕ) (hmk : ∀ x, mk x ≠ 0) (key : ℕ → ℕ → K) (pad : ℕ → K) :
    ∀ (n : ℕ) (w w' : Array ℕ),
      (List.range n).foldlM (fun w x =>
        if pos x < w.size && w.getD (pos x) 1 == 0 then some (w.set! (pos x) (mk x)) else none)
        w = some w' →
      ∀ (S : ℕ → (ℕ → K) → Prop) (f : ℕ → ℕ → K), FnInv w pad S f →
        ∃ f', FnInv w' pad (fun c k => S c k ∨ ∃ x, x < n ∧ c = pos x ∧ k = key x) f'
  | 0, w, w', h, S, f, I => by
    have e : w = w' := by simpa using h
    subst e
    refine ⟨f, ?_, I.2⟩
    rintro c k (hS | ⟨x, hx, _⟩)
    · exact I.1 c k hS
    · exact absurd hx (Nat.not_lt_zero x)
  | n + 1, w, w', h, S, f, I => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨w1, h1, h2⟩ := bind_some h
    obtain ⟨f1, I1⟩ := fold_fn pos mk hmk key pad n w w1 h1 S f I
    rw [List.foldlM_cons] at h2
    obtain ⟨w2, h3, h4⟩ := bind_some h2
    have e2 : w2 = w' := by simpa using h4
    subst e2
    by_cases hc : (pos n < w1.size && w1.getD (pos n) 1 == 0) = true
    · rw [if_pos hc] at h3
      have e3 := Option.some.inj h3
      subst e3
      have hc' := (Bool.and_eq_true _ _ ▸ hc)
      have c1 : pos n < w1.size := of_decide_eq_true hc'.1
      have c2 : w1.getD (pos n) 1 = 0 := beq_iff_eq.mp hc'.2
      have I2 := fn_step c1 c2 (hmk n) I1 (key n)
      refine ⟨_, ?_, I2.2⟩
      rintro c k (hS | ⟨x, hx, hcx, hkx⟩)
      · exact I2.1 c k (Or.inl (Or.inl hS))
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h5 | h5
        · exact I2.1 c k (Or.inl (Or.inr ⟨x, h5, hcx, hkx⟩))
        · subst h5
          exact I2.1 c k (Or.inr ⟨hcx, hkx⟩)
    · rw [if_neg hc] at h3
      cases h3

/-- The columns of the segments of a list. -/
theorem marks_fn {R : Model.Head.Run} (kv : String → ℕ → ℕ → K) (pad : ℕ → K) :
    ∀ (l : List Model.Seg) (w w' : Array ℕ),
      l.foldlM (fun w g => Model.Head.markColumns R w g) w = some w' →
      ∀ (S : ℕ → (ℕ → K) → Prop) (f : ℕ → ℕ → K), FnInv w pad S f →
        ∃ f', FnInv w' pad
          (fun c k => S c k ∨ ∃ g ∈ l, ∃ x, x < g.n ∧ c = g.pos.getD x 0 ∧ k = kv g.name x) f'
  | [], w, w', h, S, f, I => by
    have e : w = w' := by simpa using h
    subst e
    refine ⟨f, ?_, I.2⟩
    rintro c k (hS | ⟨g, hg, _⟩)
    · exact I.1 c k hS
    · exact absurd hg List.not_mem_nil
  | g :: l, w, w', h, S, f, I => by
    rw [List.foldlM_cons] at h
    obtain ⟨w1, h1, h2⟩ := bind_some h
    obtain ⟨f1, I1⟩ := fold_fn (fun x => g.pos.getD x 0)
      (fun x => if Model.Head.perEntry g.name && Model.Head.firstEntry R.L g.name + x ≥ R.h.V
        then 2 else 1)
      (fun x => by dsimp only; split <;> decide) (kv g.name) pad g.n w w1 h1 S f I
    obtain ⟨f2, I2⟩ := marks_fn kv pad l w1 w' h2 _ f1 I1
    refine ⟨f2, ?_, I2.2⟩
    rintro c k (hS | ⟨g', hg', x, hx, hcx, hkx⟩)
    · exact I2.1 c k (Or.inl (Or.inl hS))
    · rcases List.mem_cons.mp hg' with rfl | h3
      · exact I2.1 c k (Or.inl (Or.inr ⟨x, hx, hcx, hkx⟩))
      · exact I2.1 c k (Or.inr ⟨g', h3, x, hx, hcx, hkx⟩)

/-- If the marking of a call's columns does not refuse, there is a function on columns and positions
that has each segment's keys in the segment's columns and the padding key in the columns without a
mark. -/
theorem exists_keyFn {R : Model.Head.Run} {J : ℕ} {l : List Model.Seg} {w : Array ℕ}
    (h : l.foldlM (fun w g => Model.Head.markColumns R w g) (Array.replicate J 0) = some w)
    (kv : String → ℕ → ℕ → K) (pad : K) : ∃ f, KeyFn l w J kv pad f := by
  obtain ⟨f, I⟩ := marks_fn kv (fun _ => pad) l (Array.replicate J 0) w h (fun _ _ => False)
    (fun _ _ => pad) ⟨fun _ _ hF => hF.elim, fun _ _ => rfl⟩
  exact ⟨f, fun g hg x hx => (I.1 _ _ (Or.inr ⟨g, hg, x, hx, rfl, rfl⟩)).2,
    fun j _ hj => I.2 j hj⟩

end Fn

/-- What holds of all values of a call's function holds of every key of every segment. -/
theorem keys_of_fn {K : Type} [Field K] {R : Model.Head.Run} {J : ℕ} {l : List Model.Seg}
    {w : Array ℕ}
    (h : l.foldlM (fun w g => Model.Head.markColumns R w g) (Array.replicate J 0) = some w)
    {kv : String → ℕ → ℕ → K} {pad : K} {f : ℕ → ℕ → K} (Kf : KeyFn l w J kv pad f)
    (P : K → Prop) (n : ℕ) (hin : ∀ j, j < J → ∀ i, i < n → P (f j i)) :
    ∀ g ∈ l, ∀ x, x < g.n → ∀ i, i < n → P (kv g.name x i) := by
  intro g hg x hx i hi
  obtain ⟨_, _, p⟩ := marks_sum (K := K) (J := J) (fun _ => 0) l (Array.replicate J 0) w
    (by simp) h
  rw [← Kf.seg g hg x hx]
  exact hin _ (p g hg x hx) i hi

#print axioms exists_keyFn
#print axioms keys_of_fn

end OnBytes.Road.Hd
