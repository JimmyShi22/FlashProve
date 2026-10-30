-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Discipline.lean: lemmas on the definitions of Compile/SpecDiscipline.lean (words of this
library: lean/GLOSSARY.md). "Tail" (`Ev.tail`) and the two modes are told in Rom/Defer.lean.
  Part 1  generic in the family of oracles:
          the records after a release (`releaseAll`, Rom/Defer.lean) do not depend on the mode or on
          the table (`releaseAll_fst`);
          `markDue` changes no field of a record but `released`, and so no count (`markDue_o` to
          `nEv_map_markDue`);
          the number of tokens, the records and the new token's value after a new token and after a
          marked query (`length_afterFresh` to `mem_evs_afterMark`, `val_afterFresh`,
          `val_afterMark`);
          the four kinds of action are instances of `Grows` (`Grows.ofPlain`, `Grows.ofFresh`,
          `Grows.ofMark`, `Grows.ofReveal`);
          `Grows` composes, the counts adding up (`Grows.trans`; hypotheses there)
  Part 2  `TreeNew`: all tokens of a tree are numbers from n on

Notation (all in Compile/SpecDiscipline.lean): `Grows Ch R e M d d'`, a proposition: what a run may
have added on the way from d to d'; the four kinds of action: a plain query, a new token, a marked
query, a reveal (the states after them: `afterPlain`, `afterFresh`, `afterMark`, `afterReveal`).
-/
import Compile.SpecDiscipline

namespace Compile.Disc
open Iop Rom

/-! ## Part 1. Generic -/

section Generic
variable {S : OSpec} {sp : Split S} {α β : Type} {Rl : Rules S}

/-! ### Release -/

/-- The records after a release do not depend on the mode or on the table. -/
theorem releaseAll_fst (m : Bool) (shown : List Tok) : ∀ (evs : List (Ev S)) (T : Table S),
    (releaseAll m shown evs T).1 = evs.map (markDue shown)
  | [], _ => rfl
  | e :: es, T => by
      by_cases h : (!e.released && shown.contains e.charged) = true
      · rw [releaseAll, if_pos h, List.map_cons, markDue, if_pos h]
        exact congrArg _ (releaseAll_fst m shown es _)
      · rw [releaseAll, if_neg h, List.map_cons, markDue, if_neg h]
        exact congrArg _ (releaseAll_fst m shown es _)

/-! ### Values and counts -/

theorem val_of_prefix {d d' : DSt S} (h : d.vals <+: d'.vals) {t : Tok} (ht : t < d.vals.length) :
    d'.val t = d.val t := by
  obtain ⟨l, hl⟩ := h
  unfold DSt.val
  rw [← hl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

theorem val_new (l : List Bits) (v : Bits) : (l ++ [v]).getD l.length [] = v := by
  simp [List.getD_eq_getElem?_getD]

theorem markDue_o (shown : List Tok) (e : Ev S) : (markDue shown e).o = e.o := by
  unfold markDue; split <;> rfl
theorem markDue_charged (shown : List Tok) (e : Ev S) : (markDue shown e).charged = e.charged := by
  unfold markDue; split <;> rfl
theorem markDue_tail (shown : List Tok) (e : Ev S) : (markDue shown e).tail = e.tail := by
  unfold markDue; split <;> rfl
theorem markDue_others (shown : List Tok) (e : Ev S) : (markDue shown e).others = e.others := by
  unfold markDue; split <;> rfl

theorem markDue_point (shown : List Tok) (e : Ev S) (P : ∀ o, S.Dom o → Prop) :
    P (markDue shown e).o (markDue shown e).pt ↔ P e.o e.pt := by
  by_cases h : (!e.released && shown.contains e.charged) = true
  · rw [show markDue shown e = { e with released := true } from if_pos h]
  · rw [show markDue shown e = e from if_neg h]

theorem markDue_released (shown : List Tok) (e : Ev S) :
    (markDue shown e).released = true ↔ e.released = true ∨ e.charged ∈ shown := by
  unfold markDue
  by_cases hr : e.released = true
  · simp [hr]
  · by_cases hc : e.charged ∈ shown
    · simp [hr, hc]
    · simp [hr, hc]

theorem nEv_map_markDue (shown : List Tok) (evs : List (Ev S)) (o : S.ι) :
    ((evs.map (markDue shown)).filter fun v => decide (v.o = o)).length =
      (evs.filter fun v => decide (v.o = o)).length := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
      rw [List.map_cons, List.filter_cons, List.filter_cons, markDue_o]
      split
      · rw [List.length_cons, List.length_cons, ih]
      · exact ih

/-! ### After a new token and after a marked query -/

theorem length_afterFresh (d : DSt S) (v : Bits) :
    (afterFresh d v).vals.length = d.vals.length + 1 := by
  simp [afterFresh]

theorem length_afterMark (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    (afterMark sp d o t us P r T).vals.length = d.vals.length + 1 := by
  simp [afterMark]

theorem mem_evs_afterMark {d : DSt S} {o : S.ι} {t : Tok} {us : List Tok} {P : S.Dom o}
    {r : S.Rng o} {T : Table S} {e : Ev S} (he : e ∈ (afterMark sp d o t us P r T).evs) :
    e ∈ d.evs ∨ e = ⟨o, P, r, t, us, d.vals.length, false⟩ := by
  rcases List.mem_append.mp (show e ∈ d.evs ++ [_] from he) with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_singleton.mp h)

/-! ### Grows, and the value of a new token -/

section GrowsKit
variable {Ch R Ch₂ R₂ : Tok → Prop} {e M e₁ M₁ e₂ M₂ : S.ι → ℕ} {d d' d'' : DSt S}

/-- the count n at the oracle o₀ and 0 elsewhere -/
def cnt1 (o₀ : S.ι) (n : ℕ) : S.ι → ℕ := fun o => if o = o₀ then n else 0

theorem Grows.refl (d : DSt S) : Grows Ch R e M d d where
  vals := List.prefix_refl _
  shown := fun _ ht => Or.inl ht
  evs := fun e' he' => Or.inl ⟨e', he', rfl, rfl, rfl⟩
  plain := fun _ => Nat.le_add_right _ _
  marked := fun _ => Nat.le_add_right _ _

theorem Grows.length_le (h : Grows Ch R e M d d') : d.vals.length ≤ d'.vals.length :=
  h.vals.length_le

theorem Grows.trans (h₁ : Grows Ch R e₁ M₁ d d') (h₂ : Grows Ch₂ R₂ e₂ M₂ d' d'')
    (hCh : ∀ t, Ch₂ t → Ch t ∨ d.vals.length ≤ t) (hR : ∀ t, R₂ t → R t ∨ d.vals.length ≤ t)
    (he : ∀ o, e₁ o + e₂ o ≤ e o) (hM : ∀ o, M₁ o + M₂ o ≤ M o) : Grows Ch R e M d d'' where
  vals := h₁.vals.trans h₂.vals
  shown := fun t ht => by
    rcases h₂.shown t ht with h | h | h
    · exact h₁.shown t h
    · exact Or.inr (hR t h)
    · exact Or.inr (Or.inr (le_trans h₁.length_le h))
  evs := fun e'' he'' => by
    rcases h₂.evs e'' he'' with ⟨e', he', ho, hc, ht⟩ | ⟨ht, hc⟩
    · rcases h₁.evs e' he' with ⟨e₀, he₀, ho', hc', ht'⟩ | ⟨ht', hc'⟩
      · exact Or.inl ⟨e₀, he₀, ho'.trans ho, hc'.trans hc, ht'.trans ht⟩
      · exact Or.inr ⟨ht ▸ ht', hc ▸ hc'⟩
    · refine Or.inr ⟨le_trans h₁.length_le ht, ?_⟩
      rcases hc with hc | hc
      · exact hCh _ hc
      · exact Or.inr (le_trans h₁.length_le hc)
  plain := fun o => by
    have a := h₁.plain o
    have b := h₂.plain o
    have c := he o
    omega
  marked := fun o => by
    have a := h₁.marked o
    have b := h₂.marked o
    have c := hM o
    omega

theorem Grows.mono (h : Grows Ch₂ R₂ e₂ M₂ d d') (hCh : ∀ t, Ch₂ t → Ch t ∨ d.vals.length ≤ t)
    (hR : ∀ t, R₂ t → R t ∨ d.vals.length ≤ t) (he : ∀ o, e₂ o ≤ e o) (hM : ∀ o, M₂ o ≤ M o) :
    Grows Ch R e M d d' :=
  (Grows.refl (Ch := Ch) (R := R) (e := fun _ => 0) (M := fun _ => 0) d).trans h hCh hR
    (fun o => by rw [Nat.zero_add]; exact he o) (fun o => by rw [Nat.zero_add]; exact hM o)

theorem Grows.ofPlain (d : DSt S) (o : S.ι) (T : Table S) :
    Grows Ch R (cnt1 o 1) M d (afterPlain d o T) where
  vals := List.prefix_refl _
  shown := fun _ ht => Or.inl ht
  evs := fun e' he' => Or.inl ⟨e', he', rfl, rfl, rfl⟩
  plain := fun o' => by
    show Function.update d.nPlain o (d.nPlain o + 1) o' ≤ d.nPlain o' + cnt1 o 1 o'
    unfold cnt1
    by_cases h : o' = o
    · subst h
      rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne h, if_neg h]
      exact Nat.le_add_right _ _
  marked := fun _ => Nat.le_add_right _ _

theorem Grows.ofFresh (d : DSt S) (v : Bits) : Grows Ch R e M d (afterFresh d v) where
  vals := List.prefix_append _ _
  shown := fun _ ht => Or.inl ht
  evs := fun e' he' => Or.inl ⟨e', he', rfl, rfl, rfl⟩
  plain := fun _ => Nat.le_add_right _ _
  marked := fun _ => Nat.le_add_right _ _

theorem Grows.ofMark (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Grows (fun t' => t' = t) R e (cnt1 o 1) d (afterMark sp d o t us P r T) where
  vals := List.prefix_append _ _
  shown := fun _ ht => Or.inl ht
  evs := fun e' he' => by
    rcases mem_evs_afterMark he' with h | rfl
    · exact Or.inl ⟨e', h, rfl, rfl, rfl⟩
    · exact Or.inr ⟨le_rfl, Or.inl rfl⟩
  plain := fun _ => Nat.le_add_right _ _
  marked := fun o' => by
    show ((d.evs ++ [(⟨o, P, r, t, us, d.vals.length, false⟩ : Ev S)]).filter fun v =>
        decide (v.o = o')).length ≤
      nEv d o' + cnt1 o 1 o'
    rw [List.filter_append, List.length_append]
    refine Nat.add_le_add_left ?_ _
    unfold cnt1
    by_cases h : o' = o
    · rw [if_pos h]
      exact le_trans (List.length_filter_le _ _) (le_of_eq rfl)
    · rw [if_neg h, List.filter_cons_of_neg (by simpa using fun hh : o = o' => h hh.symm)]
      exact le_rfl

theorem Grows.ofReveal (d : DSt S) (ts : List Tok) (T : Table S) :
    Grows Ch (fun t => t ∈ ts) e M d (afterReveal d ts T) where
  vals := List.prefix_refl _
  shown := fun t ht => by
    rcases List.mem_append.mp (show t ∈ d.shown ++ ts from ht) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  evs := fun e' he' => by
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map _ from he')
    exact Or.inl
      ⟨e₀, he₀, (markDue_o _ _).symm, (markDue_charged _ _).symm, (markDue_tail _ _).symm⟩
  plain := fun _ => Nat.le_add_right _ _
  marked := fun o => by
    show ((d.evs.map (markDue (d.shown ++ ts))).filter fun v => decide (v.o = o)).length ≤
      nEv d o + M o
    rw [nEv_map_markDue]
    exact Nat.le_add_right _ _

theorem val_afterFresh (d : DSt S) (v : Bits) : (afterFresh d v).val d.vals.length = v :=
  val_new _ _

theorem val_afterMark (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    (afterMark sp d o t us P r T).val d.vals.length = List.ofFn (sp.split o r).2 := val_new _ _

end GrowsKit

end Generic

/-! ## Part 2. Tokens of a tree -/

section Scheme
variable {I X : Type} {lam K : ℕ} {p : Params}

/-- all tokens of the tree are numbers from n on -/
def TreeNew (n : ℕ) (t : TreeH lam) : Prop := ∀ u, TreeTok t u → n ≤ u

end Scheme

end Compile.Disc
