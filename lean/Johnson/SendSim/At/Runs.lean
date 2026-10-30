-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Runs.lean: for entries that are within the number of coins, the value of cutAll,
which cuts the entries' runs off a value of the coins, determines the coins at the entries' numbers;
and cutAll reaches every family of runs if the entries share no number.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file proves. General lemmas, for every number of coins d and every list of entries es. No
sender, no oracle message and no location of a coin is in them, and no distribution is named. An
entry is within d if its run ends within d in both fields.
  cutAll_onto   If every entry of es is within d and no two of them share a number in either field
                (ApartAll), then every family of runs is cutAll c es for some coins c.
  cutAll_tells  If every entry of es is within d and cutAll c es = cutAll c' es, then c and c' have
                the same coin at each number of the entries. cut_tells is the same for one run.

How it fits. Johnson/SendSim/At/SpentUnif.lean uses the first two for spentUnif, so for rowsFresh
(Johnson/SendSim/At/RowsFresh.lean). Johnson/SendSim/At/FoldAnyRoad.lean uses cutAll_onto for
rowsFreshAny (Johnson/SendSim/At/FreshWideProofs.lean). Johnson/SendSim/At/WriteAll.lean uses all
but cutAll_onto and cut_tells. The proofs rest on cutAll_congr (Johnson/SendSim/At/CutProof.lean)
and cs_ext (Johnson/SendSim/At/Additive.lean).

The other names.
  writeRun      coins with one run overwritten. If the run is within d it is cut off again
                (cut_writeRun), and at the other numbers the coins are unchanged (ce_writeRun,
                cf_writeRun).
  not_mem_of_apart_e, not_mem_of_apart_f   a number of entries that share no number with e is not a
                number of e.
-/
import Johnson.SendSim.At.CutProof

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

variable {d : Due}

/-- The coins c with one run overwritten: in each field, the coins with the numbers from a on, as
many as n says, are replaced by those of x. -/
def writeRun (c : Cs d) (a n : Due) (x : Cs n) : Cs d :=
  ⟨fun i => if h : a.f ≤ i.1 ∧ i.1 < a.f + n.f then x.f ⟨i.1 - a.f, by omega⟩ else c.f i,
    fun i => if h : a.e ≤ i.1 ∧ i.1 < a.e + n.e then x.e ⟨i.1 - a.e, by omega⟩ else c.e i⟩

/-- If the run is within d, cutting it off writeRun c a n x gives x. -/
theorem cut_writeRun (c : Cs d) (a n : Due) (x : Cs n)
    (h : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e) : (writeRun c a n x).cut a n = some x := by
  unfold Cs.cut
  rw [dif_pos h]
  refine congrArg some (cs_ext _ _ (funext fun i => ?_) (funext fun i => ?_))
  · show (if h : a.f ≤ a.f + i.1 ∧ a.f + i.1 < a.f + n.f then
      x.f ⟨a.f + i.1 - a.f, by omega⟩ else _) = x.f i
    rw [dif_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _⟩]
    exact congrArg x.f (Fin.ext (Nat.add_sub_cancel_left ..))
  · show (if h : a.e ≤ a.e + i.1 ∧ a.e + i.1 < a.e + n.e then
      x.e ⟨a.e + i.1 - a.e, by omega⟩ else _) = x.e i
    rw [dif_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.2 _⟩]
    exact congrArg x.e (Fin.ext (Nat.add_sub_cancel_left ..))

/-- At a number outside the run, writeRun leaves the coin of the extension field unchanged. -/
theorem ce_writeRun (c : Cs d) (a n : Due) (x : Cs n) (N : ℕ)
    (hN : ¬ (a.e ≤ N ∧ N < a.e + n.e)) : ce (writeRun c a n x) N = ce c N := by
  unfold ce
  by_cases hlt : N < d.e
  · rw [dif_pos hlt, dif_pos hlt]
    exact dif_neg hN
  · rw [dif_neg hlt, dif_neg hlt]

/-- The same for the base field. -/
theorem cf_writeRun (c : Cs d) (a n : Due) (x : Cs n) (N : ℕ)
    (hN : ¬ (a.f ≤ N ∧ N < a.f + n.f)) : cf (writeRun c a n x) N = cf c N := by
  unfold cf
  by_cases hlt : N < d.f
  · rw [dif_pos hlt, dif_pos hlt]
    exact dif_neg hN
  · rw [dif_neg hlt, dif_neg hlt]

/-- No two entries of the list share a coin's number, in either field. -/
def ApartAll (es : List Ahead) : Prop :=
  es.Pairwise fun e e' => Disjoint (eOf e) (eOf e') ∧ Disjoint (fOf e) (fOf e')

/-- If e shares no number with any entry of es, then a number of es in the extension field is not a
number of e. -/
theorem not_mem_of_apart_e (e : Ahead) (es : List Ahead)
    (h : ∀ e' ∈ es, Disjoint (eOf e) (eOf e') ∧ Disjoint (fOf e) (fOf e')) (i : ℕ)
    (hi : i ∈ eAll es) : ¬ (e.start.e ≤ i ∧ i < e.start.e + e.count.e) := by
  induction es with
  | nil => cases hi
  | cons a l ih =>
    intro hin
    rcases Finset.mem_union.1 (show i ∈ eOf a ∪ eAll l from hi) with h1 | h1
    · exact Finset.disjoint_left.1 (h a List.mem_cons_self).1 (Finset.mem_Ico.2 hin) h1
    · exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')) h1 hin

/-- The same for the base field. -/
theorem not_mem_of_apart_f (e : Ahead) (es : List Ahead)
    (h : ∀ e' ∈ es, Disjoint (eOf e) (eOf e') ∧ Disjoint (fOf e) (fOf e')) (i : ℕ)
    (hi : i ∈ fAll es) : ¬ (e.start.f ≤ i ∧ i < e.start.f + e.count.f) := by
  induction es with
  | nil => cases hi
  | cons a l ih =>
    intro hin
    rcases Finset.mem_union.1 (show i ∈ fOf a ∪ fAll l from hi) with h1 | h1
    · exact Finset.disjoint_left.1 (h a List.mem_cons_self).2 (Finset.mem_Ico.2 hin) h1
    · exact ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')) h1 hin

/-- If every entry of es is within d and no two of them share a number (ApartAll), then every family
of runs v is cutAll c es for some coins c. -/
theorem cutAll_onto : ∀ es : List Ahead,
    (∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e) → ApartAll es →
    ∀ v : CsAll (es.map Ahead.named), ∃ c : Cs d, cutAll c es = some v
  | [], _, _, _ => ⟨default, rfl⟩
  | e :: es, hW, hA, v => by
    have hA' := List.pairwise_cons.1 hA
    obtain ⟨c0, h0⟩ := cutAll_onto es (fun e' he' => hW e' (List.mem_cons_of_mem _ he')) hA'.2
      (show Cs e.count × CsAll (es.map Ahead.named) from v).2
    refine ⟨writeRun c0 e.start e.count (show Cs e.count × CsAll (es.map Ahead.named) from v).1,
      ?_⟩
    show ((writeRun c0 e.start e.count _).cut e.start e.count).bind _ = some v
    rw [cut_writeRun _ _ _ _ (hW e List.mem_cons_self),
      cutAll_congr (writeRun c0 e.start e.count _) c0 es
        (fun i hi => cf_writeRun _ _ _ _ i (not_mem_of_apart_f e es hA'.1 i hi))
        (fun i hi => ce_writeRun _ _ _ _ i (not_mem_of_apart_e e es hA'.1 i hi)), h0]
    rfl

/-- If the run is within d and c and c' have the same cut there, then c and c' have the same coin at
each of the run's numbers, in both fields. -/
theorem cut_tells (c c' : Cs d) (a n : Due) (h : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e)
    (e : c.cut a n = c'.cut a n) :
    (∀ i, a.f ≤ i → i < a.f + n.f → cf c i = cf c' i) ∧
      ∀ i, a.e ≤ i → i < a.e + n.e → ce c i = ce c' i := by
  unfold Cs.cut at e
  rw [dif_pos h, dif_pos h] at e
  have e' := Option.some.inj e
  have ef := congrArg Cs.f e'
  have ee := congrArg Cs.e e'
  refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · have hlt : i < d.f := by have := h.1; omega
    have := congrFun ef ⟨i - a.f, by omega⟩
    simp only [Nat.add_sub_cancel' h1] at this
    unfold cf
    rw [dif_pos hlt, dif_pos hlt]
    exact this
  · have hlt : i < d.e := by have := h.2; omega
    have := congrFun ee ⟨i - a.e, by omega⟩
    simp only [Nat.add_sub_cancel' h1] at this
    unfold ce
    rw [dif_pos hlt, dif_pos hlt]
    exact this

/-- If every entry of es is within d and cutAll c es = cutAll c' es, then c and c' have the same
coin at each number of the entries, in both fields. -/
theorem cutAll_tells (c c' : Cs d) : ∀ es : List Ahead,
    (∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e) →
    cutAll c es = cutAll c' es →
    (∀ i ∈ fAll es, cf c i = cf c' i) ∧ ∀ i ∈ eAll es, ce c i = ce c' i
  | [], _, _ => ⟨fun _ h => absurd h (Finset.notMem_empty _),
      fun _ h => absurd h (Finset.notMem_empty _)⟩
  | e :: es, hW, h => by
    obtain ⟨x, hx⟩ : ∃ x, c.cut e.start e.count = some x := by
      unfold Cs.cut
      rw [dif_pos (hW e List.mem_cons_self)]
      exact ⟨_, rfl⟩
    obtain ⟨x', hx'⟩ : ∃ x, c'.cut e.start e.count = some x := by
      unfold Cs.cut
      rw [dif_pos (hW e List.mem_cons_self)]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := cutAll_some c es fun e' he' => hW e' (List.mem_cons_of_mem _ he')
    obtain ⟨y', hy'⟩ := cutAll_some c' es fun e' he' => hW e' (List.mem_cons_of_mem _ he')
    have h' : (c.cut e.start e.count).bind (fun x => (cutAll c es).map fun y => (x, y)) =
        (c'.cut e.start e.count).bind fun x => (cutAll c' es).map fun y => (x, y) := h
    rw [hx, hx', hy, hy'] at h'
    have h2 : (x, y) = (x', y') := Option.some.inj h'
    have t1 := cut_tells c c' e.start e.count (hW e List.mem_cons_self)
      (by rw [hx, hx', (Prod.mk.inj h2).1])
    have t2 := cutAll_tells c c' es (fun e' he' => hW e' (List.mem_cons_of_mem _ he'))
      (by rw [hy, hy', (Prod.mk.inj h2).2])
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases Finset.mem_union.1 (show i ∈ fOf e ∪ fAll es from hi) with h1 | h1
      · exact t1.1 i (Finset.mem_Ico.1 h1).1 (Finset.mem_Ico.1 h1).2
      · exact t2.1 i h1
    · rcases Finset.mem_union.1 (show i ∈ eOf e ∪ eAll es from hi) with h1 | h1
      · exact t1.2 i (Finset.mem_Ico.1 h1).1 (Finset.mem_Ico.1 h1).2
      · exact t2.2 i h1

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.cutAll_onto
#print axioms OnBytes.SendSim.At.cutAll_tells
