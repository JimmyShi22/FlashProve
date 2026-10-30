-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FormOnReads.lean: the code switch: A SAMPLE ROW's FORM
(RowsOrder.lean's formOn) READS AS THE ROW's OWN COEFFICIENTS ON THE MAIN TABLE, for a row without
stretches and forms that reads one message's main table alone; and the program's Send.form makes
such a row for a shape without a mask row.

The switch carries a kept member's old sample row over as a FORM on its main table (the program's
switchFormOn; formOn). The typed vector in the last join is said through that form
(KeptFormJoin.lean's slotVec … (formOn smp)); the library's reading of the program's sample row is
said through the row's coefficients (coefAt; Johnson/Pack/FormPortZF.lean). Here the two are one.
  formOn_reads   formAt (formOn row) i = coefAt row o .main i, if the row has no stretch and no form
                 and reads the main table of o alone
  form_plain     a row of Send.form has no stretch and no form; for a shape without a mask row it
                 reads the main table of its message alone
  stored_reads   the two together, at a stored sample row: Send.form's row with an answer as its
                 target
  fold_add, fold_addEntry, fold_terms, fold_units, fold_unit_keeps, readsMain_of
                 tools
LIMITS. BY READING, with stretches the like is false at a stretch of step 0 (the row's coefficient
leaves it out; formOn lays it): no lemma and no example here shows it. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hands.RowsOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice

theorem fold_add (i : ℕ) : ∀ (l : List Term) (c : Form),
    formAt (l.foldl (fun (c : Form) t => c.add t.v) c) i =
      formAt c i + (l.map fun t => readE (t.v.entry i)).sum
  | [], c => by simp
  | t :: l, c => by
    rw [List.foldl_cons, fold_add i l, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    exact Form.entry_add rdE c t.v i

theorem fold_addEntry (i : ℕ) : ∀ (l : List Single) (c : Form),
    formAt (l.foldl (fun (c : Form) u => c.addEntry u.index u.coeff) c) i =
      formAt c i + (l.map fun u => if u.index = i then readE u.coeff else 0).sum
  | [], c => by simp
  | u :: l, c => by
    rw [List.foldl_cons, fold_addEntry i l, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    exact Form.entry_addEntry rdE c u.index u.coeff i

theorem fold_terms (o i : ℕ) : ∀ (l : List Term) (s : E),
    (∀ t ∈ l, (t.oracle == o && t.part == Part.main) = true) →
    readE (l.foldl (fun s t =>
      if t.oracle == o && t.part == Part.main then addE s (t.v.entry i) else s) s) =
      readE s + (l.map fun t => readE (t.v.entry i)).sum
  | [], s, _ => by simp
  | t :: l, s, h => by
    rw [List.foldl_cons, if_pos (h t (List.mem_cons_self ..)),
      fold_terms o i l _ fun x hx => h x (List.mem_cons_of_mem _ hx), List.map_cons, List.sum_cons,
      ← add_assoc, show readE (addE s (t.v.entry i)) = readE s + readE (t.v.entry i) from
        rdE.add _ _]

theorem fold_units (o i : ℕ) : ∀ (l : List Single) (s : E),
    (∀ u ∈ l, (u.oracle == o && u.part == Part.main) = true) →
    readE (l.foldl (fun s u =>
      if u.oracle == o && u.part == Part.main && u.index == i then addE s u.coeff else s) s) =
      readE s + (l.map fun u => if u.index = i then readE u.coeff else 0).sum
  | [], s, _ => by simp
  | u :: l, s, h => by
    rw [List.foldl_cons, fold_units o i l _ fun x hx => h x (List.mem_cons_of_mem _ hx),
      List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    rw [h u (List.mem_cons_self ..), Bool.true_and]
    by_cases e : u.index = i
    · rw [if_pos e, if_pos (by simpa using e)]
      exact rdE.add s u.coeff
    · rw [if_neg e, if_neg (by simpa using e), add_zero]

/-- **The form reads as the row's coefficients on the main table.** -/
theorem formOn_reads (o : ℕ) (row : Row) (hr : row.runs = #[]) (hf : row.forms = #[])
    (h : readsMain o row = true) (i : ℕ) : formAt (formOn row) i = coefAt row o .main i := by
  unfold readsMain at h
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := h
  unfold formOn coefAt Row.coefficient
  rw [hr, hf]
  simp only [List.foldl_nil, ← Array.foldl_toList]
  rw [fold_addEntry, fold_add, fold_units o i _ _ (fun u hu => by
      simpa using h2 u (by simpa using hu)),
    fold_terms o i _ _ (fun t ht => by simpa using h1 t (by simpa using ht))]
  congr 2

theorem fold_unit_keeps (o : ℕ) (f : PadPlace → E) : ∀ (l : List PadPlace) (r : Row),
    (l.foldl (fun (r : Row) p => r.addUnit o p.part p.index (f p)) r).runs = r.runs ∧
      (l.foldl (fun (r : Row) p => r.addUnit o p.part p.index (f p)) r).forms = r.forms ∧
      (l.foldl (fun (r : Row) p => r.addUnit o p.part p.index (f p)) r).terms = r.terms ∧
      ∀ u ∈ (l.foldl (fun (r : Row) p => r.addUnit o p.part p.index (f p)) r).units.toList,
        u ∈ r.units.toList ∨ ∃ p ∈ l, u.oracle = o ∧ u.part = p.part
  | [], r => ⟨rfl, rfl, rfl, fun u hu => Or.inl hu⟩
  | p :: l, r => by
    obtain ⟨a, b, c, d⟩ := fold_unit_keeps o f l (r.addUnit o p.part p.index (f p))
    refine ⟨a, b, c, fun u hu => ?_⟩
    rcases d u hu with h | ⟨q, hq, e⟩
    · have h' : u ∈ (r.units.push ⟨o, p.part, p.index, f p⟩).toList := h
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at h'
      rcases h' with h' | rfl
      · exact Or.inl h'
      · exact Or.inr ⟨p, List.mem_cons_self .., rfl, rfl⟩
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, e⟩

theorem readsMain_of (o : ℕ) (row : Row)
    (ht : ∀ t ∈ row.terms.toList, t.oracle = o ∧ t.part = Part.main)
    (hu : ∀ u ∈ row.units.toList, u.oracle = o ∧ u.part = Part.main) (hr : row.runs = #[])
    (hf : row.forms = #[]) : readsMain o row = true := by
  unfold readsMain
  rw [hr, hf]
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem]
  refine ⟨⟨⟨fun t h => ?_, fun u h => ?_⟩, fun r h => by simp at h⟩, fun f h => by simp at h⟩
  · obtain ⟨a, b⟩ := ht t (by simpa using h)
    simp [a, b]
  · obtain ⟨a, b⟩ := hu u (by simpa using h)
    simp [a, b]

/-- **A row of Send.form**: no stretch, no form; and, for a shape without a mask row, it reads the
main table
of its message alone. -/
theorem form_plain {codes : Codes} {s : OracleShape} {o : ℕ} {seed : SampleSeed} {a : ℕ} {row : Row}
    (h : Send.form codes s o seed a = some row) :
    row.runs = #[] ∧ row.forms = #[] ∧ (s.maskRows = 0 → readsMain o row = true) := by
  unfold Send.form at h
  obtain ⟨places, hp, h⟩ := Option.bind_eq_some_iff.1 h
  have h' := Option.some.inj h
  clear h
  obtain ⟨k1, k2, k3, k4⟩ := fold_unit_keeps o
    (fun p => subE (if p.answer == a then mulE seed.beta p.basis else zeroE)
      ((if p.part == .main then
          Tensor.eq (seed.z.take (Send.cube codes s).mainBits)
            (Send.front seed.z (Send.cube codes s) (Send.cube codes s).mainBits false)
        else Tensor.eq (seed.z.take (Send.cube codes s).maskBits)
            (Send.front seed.z (Send.cube codes s) (Send.cube codes s).maskBits true)).entry
        p.index)) places { kind := .sample }
  subst h'
  refine ⟨?_, ?_, fun hm => ?_⟩
  · dsimp only
    split <;> split <;> exact k1
  · dsimp only
    split <;> split <;> exact k2
  · have hno : (Send.cube codes s).hasMask = false := by
      unfold Send.cube
      simp [hm]
    have hpart : ∀ p ∈ places, p.part = Part.main := by
      intro p hpm
      unfold Send.pad at hp
      dsimp only at hp
      simp only [hno, Bool.false_eq_true, if_false] at hp
      repeat' split at hp
      all_goals first
        | (cases hp; done)
        | (rw [← Option.some.inj hp] at hpm
           obtain ⟨i, -, hq⟩ := List.mem_flatMap.1 hpm
           obtain ⟨t, -, rfl⟩ := List.mem_map.1 hq
           rfl)
    have hu : ∀ u ∈ (places.foldl (fun (r : Row) p => r.addUnit o p.part p.index
        (subE (if p.answer == a then mulE seed.beta p.basis else zeroE)
          ((if p.part == .main then
              Tensor.eq (seed.z.take (Send.cube codes s).mainBits)
                (Send.front seed.z (Send.cube codes s) (Send.cube codes s).mainBits false)
            else Tensor.eq (seed.z.take (Send.cube codes s).maskBits)
                (Send.front seed.z (Send.cube codes s) (Send.cube codes s).maskBits true)).entry
            p.index))) ({ kind := .sample } : Row)).units.toList,
        u.oracle = o ∧ u.part = Part.main := fun u hu' => by
      rcases k4 u hu' with h0 | ⟨q, hq, e1, e2⟩
      · cases h0
      · exact ⟨e1, e2.trans (hpart q hq)⟩
    dsimp only
    rw [hno]
    simp only [Bool.false_eq_true, if_false]
    split
    · refine readsMain_of o _ (fun t ht => ?_) hu k1 k2
      have ht' : t ∈ (((places.foldl _ ({ kind := .sample } : Row)).terms).push _).toList := ht
      rw [k3, Array.toList_push, List.mem_append, List.mem_singleton] at ht'
      rcases ht' with h0 | rfl
      · cases h0
      · exact ⟨rfl, rfl⟩
    · refine readsMain_of o _ (fun t ht => ?_) hu k1 k2
      rw [k3] at ht
      cases ht

/-- **A stored sample row** (Send.form's row with an answer as its target), for a shape without a
mask row:
its form reads as Send.form's row's coefficients on the main table. -/
theorem stored_reads {codes : Codes} {s : OracleShape} {o : ℕ} {seed : SampleSeed} {a : ℕ}
    {row : Row} (h : Send.form codes s o seed a = some row) (hm : s.maskRows = 0) (y : E) (i : ℕ) :
    formAt (formOn { row with target := y }) i = coefAt row o .main i :=
  formOn_reads o row (form_plain h).1 (form_plain h).2.1 ((form_plain h).2.2 hm) i

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.stored_reads
#print axioms VerifiableInference.Desc.First.K2Hands.formOn_reads
#print axioms VerifiableInference.Desc.First.K2Hands.form_plain
