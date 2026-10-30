-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyTensorOk.lean: FOR THE KEY FILE's ROW 1.16 (batt.1.batt): THE TABLE's PROMISE FROM BORDER 17 ON ASKS «every vector of the claim's row weights is Tensor.ok»: HERE ITS ROOT, GENERAL, OVER THE PROGRAM's OWN TEXTS ALONE (OnBytes/Iop/Wf.lean · Tensor.lean; no block's text):
every weight vector of a pending row is Tensor.ok, under PUBLIC facts and the one fact on the claim that «pend» tests (the point's length). (Asked of the table of joints.)
  rowBlockBits_le · rowBlockBits_fits    the block's logarithm is at most kRow; a block of more than one row ends at or before stop
  weightsFrom_ok      **PROVED**: kRow ≤ 63 → first + (stop - start) ≤ values.size → every vector is ok
  pendingRow_ok       **PROVED**: m.kRow ≤ 63 → every run's places lie inside e → every vector of (Wf.pendingRow m l p c e).g is ok
  pendingRow_ok_at    at e := Wf.eqPlaces m c.point, from c.point.length = m.kCol + p.logPlaces and the runs' places inside 2 ^ logPlaces (KeyPubIn.pubInB's second clause)
NOT HERE: Batt.rowOf's scaling from the pile's vectors to the claim's (scale turns the scalar alone: by reading). Nothing on soundness.
-/
import OnBytes.Iop.Wf
import OnBytes.Slice.ProgMle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open OnBytes.Params (WfRun WfPart WfLookup)

theorem rowBlockBits_le (kRow start stop : Nat) : ∀ (fuel d : Nat), d ≤ kRow → Wf.rowBlockBits kRow start stop fuel d ≤ kRow
  | 0, d, h => h
  | fuel + 1, d, h => by
    unfold Wf.rowBlockBits
    split
    · rename_i c
      simp only [Bool.and_eq_true, decide_eq_true_eq] at c
      exact rowBlockBits_le kRow start stop fuel (d + 1) c.1.1
    · exact h

/-- The block that is found ends at or before stop, if the one that the search began with does. -/
theorem rowBlockBits_fits (kRow start stop : Nat) : ∀ (fuel d : Nat), start + 2 ^ d ≤ stop → start + 2 ^ Wf.rowBlockBits kRow start stop fuel d ≤ stop
  | 0, d, h => h
  | fuel + 1, d, h => by
    unfold Wf.rowBlockBits
    split
    · rename_i c
      simp only [Bool.and_eq_true, decide_eq_true_eq] at c
      exact rowBlockBits_fits kRow start stop fuel (d + 1) c.2
    · exact h

theorem length_choicePairs : ∀ (n v : Nat), (choicePairs n v).length = n
  | 0, _ => rfl
  | n + 1, v => by
    unfold choicePairs
    rw [List.length_cons, length_choicePairs n]

theorem distinct_range : ∀ (n k : Nat), distinctNats ((List.range' k n)) = true
  | 0, _ => rfl
  | n + 1, k => by
    rw [List.range'_succ]
    unfold distinctNats
    rw [distinct_range n (k + 1), Bool.and_true]
    simp [List.mem_range']
    intro x _
    omega

/-- A vector that picks one row. -/
theorem ok_choice (s : E) (kRow v : Nat) (h : kRow ≤ 63) : (({ scalar := s } : Tensor).insertChoice 0 kRow v).ok = true := by
  unfold Tensor.ok Tensor.insertChoice Tensor.vars
  simp [length_choicePairs, h, distinctNats]

/-- A vector on an aligned block of 2 ^ d rows that reads a slice. -/
theorem ok_block (s : E) (kRow d v : Nat) (values : Array E) (first : Nat) (h : kRow ≤ 63) (hd : d ≤ kRow) (hs : first + 2 ^ d ≤ values.size) :
    (((({ scalar := s } : Tensor).pushDense d).insertChoice d (kRow - d) v).setValues values first).ok = true := by
  have e1 : ((List.range d).map (· + 0)).map (fun x => if d ≤ x then x + (kRow - d) else x) = List.range d := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (List.range d)]
    refine List.map_congr_left fun x hx => ?_
    have : x < d := List.mem_range.1 hx
    simp [Nat.not_le.2 this]
  unfold Tensor.ok Tensor.setValues Tensor.insertChoice Tensor.pushDense Tensor.vars
  simp only [List.nil_append, List.length_nil, e1, List.length_range, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨?_, Or.inr hs⟩, fun x hx => ?_⟩, ?_⟩
  · simp [length_choicePairs]
    omega
  · simp [List.getElem?_append_left, hx]
  · rw [List.range_eq_range']
    exact distinct_range d 0

theorem weightsFrom_ok (kRow : Nat) (values : Array E) (scale : E) (stop : Nat) (h : kRow ≤ 63) : ∀ (fuel start first : Nat), first + (stop - start) ≤ values.size →
    ∀ t ∈ Wf.weightsFrom kRow values scale stop fuel start first, t.ok = true
  | 0, _, _, _, t, ht => by
    unfold Wf.weightsFrom at ht
    cases ht
  | fuel + 1, start, first, hs, t, ht => by
    unfold Wf.weightsFrom at ht
    split at ht
    · rename_i hlt
      have hfit : start + 2 ^ Wf.rowBlockBits kRow start stop kRow 0 ≤ stop := rowBlockBits_fits kRow start stop kRow 0 (by simpa using hlt)
      rcases List.mem_cons.1 ht with e | ht'
      · subst e
        split
        · exact ok_choice _ kRow start h
        · exact ok_block scale kRow _ _ values first h (rowBlockBits_le kRow start stop kRow 0 (Nat.zero_le _)) (by omega)
      · exact weightsFrom_ok kRow values scale stop h fuel _ _ (by omega) t ht'
    · cases ht

theorem pendingRow_ok (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (c : Lkp.Keys) (e : Array E) (h : m.kRow ≤ 63) (hr : ∀ r ∈ p.runs, r.firstPlace + r.places ≤ e.size) :
    ∀ t ∈ (Wf.pendingRow m l p c e).g, t.ok = true := by
  intro t ht
  unfold Wf.pendingRow at ht
  obtain ⟨r, hrm, ht⟩ := List.mem_flatMap.1 ht
  obtain ⟨w, _, ht⟩ := List.mem_flatMap.1 ht
  unfold Wf.weightsOnRows at ht
  exact weightsFrom_ok m.kRow e (ofF w.1) _ h r.places _ r.firstPlace (by have := hr r hrm; omega) t ht

theorem pendingRow_ok_at (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (c : Lkp.Keys) (h : m.kRow ≤ 63) (hp : c.point.length = m.kCol + p.logPlaces)
    (hr : ∀ r ∈ p.runs, r.firstPlace + r.places ≤ 2 ^ p.logPlaces) : ∀ t ∈ (Wf.pendingRow m l p c (Wf.eqPlaces m c.point)).g, t.ok = true := by
  refine pendingRow_ok m l p c _ h fun r hrm => ?_
  unfold Wf.eqPlaces
  rw [OnBytes.Slice.size_eqTable, List.length_drop, hp, Nat.add_sub_cancel_left]
  exact hr r hrm

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.weightsFrom_ok
#print axioms VerifiableInference.Desc.Key.pendingRow_ok_at
