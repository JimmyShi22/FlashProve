-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/FoldAll.lean: where a list of tables is made by adding tables line after line,
every record of the list is a part of a line. So the two Boolean tests on the public list, the test
on lengths and "every table lies in the third vector", follow from the lines.

All of this file is a tool: it holds for all lists of matrices and of lines, and names no
description of the protocol.

Why. The library's law of the fold (`fold_spec`, Johnson/Road/HeadReads.lean) says that each part of
each line has its record in the list. It does not say that the list holds nothing else. The test on
lengths (`lensB`, Reads/Stated.lean) and `allU3B` (Reads/Bridge.lean) speak of every record.

What is here.
  `parts_all`, `addAsk_all`, `fold_all`: a property that holds of the records in front, and of every
    record with a line's first matrix plus some q, the line's run and array, the vector 2 and any
    first entry, holds of every record behind.
  `allU3_of_fold`: every table of a fold from the empty list lies in the third vector.
  `lens_of_fold`: where each line's array has as many entries as the line's run is long, the test on
    lengths says yes.
  `blockRows_size`, `longPhi_size`: the number of a block's weights.

Of OnBytes/Model/ this file names the records `HFun`, `TMat`, `Head.Tables`, and the makers
`blockRows`, `longPhi`, `eqTab`; through Johnson/Road/HeadReads.lean the routine `Head.addFun`.

Limits. That a description's list is such a fold, and the arrays' sizes, are premises. Nothing on
soundness.


-/
import Johnson.Desc.Reads.Bridge
import Johnson.Road.HeadReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open OnBytes (E)
open OnBytes.Model (HFun TMat blockRows longPhi eqTab)
open OnBytes.Model.Head (Tables)
open OnBytes.Road (bind_some eqTab_size)
open OnBytes.Road.Hd (Ask addAsk partStep addFun_eq)

/-- The records behind n parts. -/
theorem parts_all (P : HFun → Prop) (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E)
    (funs : Array HFun) (p : ℕ) (hf : ∀ Fn ∈ funs, P Fn)
    (hnew : ∀ q st, P { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := st }) :
    ∀ n, ∀ Fn ∈ ((List.range n).foldl (partStep mats M0 Lf phi) (funs, p)).1, P Fn
  | 0 => hf
  | n + 1 => by
    have ih := parts_all P mats M0 Lf phi funs p hf hnew n
    rw [List.range_succ, List.foldl_append]
    generalize (List.range n).foldl (partStep mats M0 Lf phi) (funs, p) = r at ih ⊢
    intro Fn hFn
    have hFn' : Fn ∈ r.1.push { mat := M0 + n, len := Lf, phi := phi, tree := 2, start := r.2 } :=
      hFn
    rcases Array.mem_push.1 hFn' with h | h
    · exact ih Fn h
    · rw [h]
      exact hnew n r.2

/-- The records behind one line. -/
theorem addAsk_all (P : HFun → Prop) {mats : Array TMat} {t t' : Tables} {a : Ask}
    (h : addAsk mats t a = some t') (hf : ∀ Fn ∈ t.funs, P Fn)
    (hnew : ∀ q st,
      P { mat := a.1 + q, len := a.2.2.1, phi := a.2.2.2.1, tree := 2, start := st }) :
    ∀ Fn ∈ t'.funs, P Fn := by
  have i := parts_all P mats a.1 a.2.2.1 a.2.2.2.1 t.funs t.p hf hnew a.2.1
  unfold addAsk at h
  rw [addFun_eq] at h
  generalize (List.range a.2.1).foldl (partStep mats a.1 a.2.2.1 a.2.2.2.1) (t.funs, t.p) = r
    at i h
  by_cases hz : (r.2 == t.p) = true
  · rw [if_pos hz] at h
    cases h
  · rw [if_neg hz] at h
    have e := (Option.some.inj h).symm
    subst e
    exact i

/-- **Every record of a fold is a part of a line, or stood in front.** -/
theorem fold_all (P : HFun → Prop) (mats : Array TMat) : ∀ (asks : List Ask) (t t' : Tables),
    (∀ a ∈ asks, ∀ q st,
      P { mat := a.1 + q, len := a.2.2.1, phi := a.2.2.2.1, tree := 2, start := st }) →
    (∀ Fn ∈ t.funs, P Fn) → asks.foldlM (addAsk mats) t = some t' → ∀ Fn ∈ t'.funs, P Fn
  | [], t, t', _, hf, h => by
    have e : t' = t := (Option.some.inj h).symm
    subst e
    exact hf
  | a0 :: rest, t, t', hn, hf, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t1, h1, h2⟩ := bind_some h
    exact fold_all P mats rest t1 t' (fun a ha => hn a (List.mem_cons_of_mem _ ha))
      (addAsk_all P h1 hf (hn a0 List.mem_cons_self)) h2

/-- Every table of a fold from the empty list lies in the third vector. -/
theorem allU3_of_fold {mats : Array TMat} {asks : List Ask} {t : Tables}
    (h : asks.foldlM (addAsk mats) {} = some t) : allU3B t.funs = true := by
  unfold allU3B
  rw [List.all_eq_true]
  intro Fn hFn
  exact beq_iff_eq.2 (fold_all (fun Fn => Fn.tree = 2) mats asks {} t (fun _ _ _ _ => rfl)
    (fun _ h0 => absurd h0 (by simp)) h Fn (by simpa using hFn))

/-- Where each line's array is as long as its run, the test on lengths says yes. -/
theorem lens_of_fold {mats : Array TMat} {asks : List Ask} {t : Tables}
    (h : asks.foldlM (addAsk mats) {} = some t) (hs : ∀ a ∈ asks, a.2.2.2.1.size = a.2.2.1) :
    lensB t.funs = true := by
  unfold lensB
  rw [List.all_eq_true]
  intro Fn hFn
  have hm : Fn ∈ t.funs.toList := (List.mem_filter.1 hFn).1
  exact beq_iff_eq.2 (fold_all (fun Fn => Fn.phi.size = Fn.len) mats asks {} t
    (fun a ha _ _ => hs a ha) (fun _ h0 => absurd h0 (by simp)) h Fn (by simpa using hm))

/-- The number of a block's weights. -/
theorem blockRows_size (low tok : Array E) : (blockRows low tok).size = low.size * tok.size := by
  have key : ∀ l : List E, (l.map fun _ => tok.size).sum = l.length * tok.size := by
    intro l
    induction l with
    | nil => rw [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul]
    | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]
  obtain ⟨l⟩ := low
  have e : (blockRows ⟨l⟩ tok).size = (l.map fun _ => tok.size).sum := by
    unfold blockRows
    simp
  rw [e, key l]
  rfl

/-- A block's weights at a point of ls + lt coordinates are 2 ^ (ls + lt). -/
theorem longPhi_size (p : Array E) {ls lt : ℕ} (h : p.size = ls + lt) :
    (longPhi p ls lt).size = 2 ^ (ls + lt) := by
  unfold longPhi
  rw [blockRows_size, eqTab_size, eqTab_size, Array.size_extract, Array.size_extract, Nat.pow_add]
  congr 2 <;> omega

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.parts_all
#print axioms VerifiableInference.Reads.addAsk_all
#print axioms VerifiableInference.Reads.fold_all
#print axioms VerifiableInference.Reads.allU3_of_fold
#print axioms VerifiableInference.Reads.lens_of_fold
#print axioms VerifiableInference.Reads.blockRows_size
#print axioms VerifiableInference.Reads.longPhi_size
