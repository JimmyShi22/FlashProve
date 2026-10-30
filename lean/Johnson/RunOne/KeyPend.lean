-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyPend.lean: THE KEY FILE's FIRST CHAIN AT THE KEY FILE's DESCRIPTION (descriptionFromSource, Johnson/Desc/Key/Desc.lean): ONE LEMMA FOR ROW 1.16 (batt.1.batt): THE ROWS ON THE TABLE THAT THE BLOCK «pend» MAKES OF A LOOKUP's CLAIMS ON ITS KEYS (KeyTable.pendingAt: with the program's four conditions) ARE THE ROWS THAT THE TABLE OF JOINTS' READER keysAt
GIVES THE CLAIM «kclaims l» (KeyReaders.pendingOf, Johnson/RunOne/KeyReaders.lean: Wf.pendingRow ∘ Wf.eqPlaces, no condition): two functions, one row (the table's two columns, row 16).
  mapM_if        a mapM over «if p x then some (f x) else none» that returns gives the map of f
  pendingAt_is   **PROVED**: lookup by lookup
  pendingAt_ok   **PROVED**: every weight vector of every row that pendingAt returns is Tensor.ok (over KeyTensorOk.pendingRow_ok_at)
  mapM_get       what a mapM that returns holds at place i comes from the list's member at place i
  pend_law       **PROVED**: THE BLOCK's OWN TEXT (KeyOne.pend): where it says yes the state behind is the state in front with pile := rows.flatten, there are as many lists of rows as the plan has lookups, and the l-th list IS what pendingOf makes of the l-th list of claims on the keys
Nothing on soundness.
-/
import Johnson.RunOne.KeyYes
import Johnson.Desc.Key.TableRows
import Johnson.Desc.Key.KeyTensorOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params

theorem mapM_if {α β : Type} (p : α → Bool) (f : α → β) : ∀ (l : List α) (r : List β), (l.mapM fun x => if p x then some (f x) else none) = some r → r = l.map f
  | [], r, h => by
    simp at h
    exact h
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hp : p x with
    | false => simp [hp] at h
    | true =>
      simp only [hp, if_true] at h
      cases hl : (l.mapM fun x => if p x then some (f x) else none) with
      | none => simp [hl] at h
      | some r' =>
        simp [hl] at h
        rw [← h, mapM_if p f l r' hl]
        rfl

theorem pendingAt_is (one : OneTime) (l : Nat) (L : WfLookup) (hL : one.ranges.lookups[l]? = some L) (cs : List Lkp.Keys) (rows : List TensorRow)
    (h : VerifiableInference.Desc.Key.tableRowsOf (Wf.matrixOf one.lin) L cs = some rows) : KeyReaders.pendingOf one l cs = some rows := by
  unfold VerifiableInference.Desc.Key.tableRowsOf at h
  split at h
  · have e := mapM_if (fun x : WfPart × Lkp.Keys => x.2.point.length == (Wf.matrixOf one.lin).kCol + x.1.logPlaces && x.2.weights.tensors.all (·.denseVars.isEmpty) &&
        Wf.sumOfForm x.2.weights == Wf.coveredSum x.1 (Wf.eqPlaces (Wf.matrixOf one.lin) x.2.point))
      (fun x => Wf.pendingRow (Wf.matrixOf one.lin) L x.1 x.2 (Wf.eqPlaces (Wf.matrixOf one.lin) x.2.point)) (zipT L.parts cs) rows h
    unfold KeyReaders.pendingOf
    rw [hL, e, zipT_eq]
    rfl
  · cases h

theorem mapM_if_all {α β : Type} (p : α → Bool) (f : α → β) : ∀ (l : List α) (r : List β), (l.mapM fun x => if p x then some (f x) else none) = some r → ∀ x ∈ l, p x = true
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | a :: l, r, h, x, hx => by
    rw [List.mapM_cons] at h
    cases hp : p a with
    | false => simp [hp] at h
    | true =>
      simp only [hp, if_true] at h
      cases hl : (l.mapM fun x => if p x then some (f x) else none) with
      | none => simp [hl] at h
      | some r' =>
        rcases List.mem_cons.1 hx with e | e
        · rw [e]; exact hp
        · exact mapM_if_all p f l r' hl x e

/-- **EVERY WEIGHT VECTOR OF EVERY ROW THAT «pend» LAYS IS Tensor.ok**: pendingAt's own test of the point's length, with two public facts (kRow ≤ 63; the runs' places inside their parts: KeyPubIn.pubInB's second clause). The root of the table's clause «g all Tensor.ok» from border 17 on. -/
theorem pendingAt_ok (m : Wf.Matrix) (L : WfLookup) (cs : List Lkp.Keys) (rows : List TensorRow) (hk : m.kRow ≤ 63)
    (hpl : ∀ p ∈ L.parts, ∀ r ∈ p.runs, r.firstPlace + r.places ≤ 2 ^ p.logPlaces) (h : VerifiableInference.Desc.Key.tableRowsOf m L cs = some rows) : ∀ x ∈ rows, ∀ t ∈ x.g, t.ok = true := by
  unfold VerifiableInference.Desc.Key.tableRowsOf at h
  split at h
  · have e := mapM_if (fun x : WfPart × Lkp.Keys => x.2.point.length == m.kCol + x.1.logPlaces && x.2.weights.tensors.all (·.denseVars.isEmpty) &&
        Wf.sumOfForm x.2.weights == Wf.coveredSum x.1 (Wf.eqPlaces m x.2.point))
      (fun x => Wf.pendingRow m L x.1 x.2 (Wf.eqPlaces m x.2.point)) (zipT L.parts cs) rows h
    have a := mapM_if_all (fun x : WfPart × Lkp.Keys => x.2.point.length == m.kCol + x.1.logPlaces && x.2.weights.tensors.all (·.denseVars.isEmpty) &&
        Wf.sumOfForm x.2.weights == Wf.coveredSum x.1 (Wf.eqPlaces m x.2.point))
      (fun x => Wf.pendingRow m L x.1 x.2 (Wf.eqPlaces m x.2.point)) (zipT L.parts cs) rows h
    intro x hx t ht
    rw [e] at hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    have c := a q hq
    simp only [Bool.and_eq_true, beq_iff_eq] at c
    have hm : q.1 ∈ L.parts := by
      rw [zipT_eq] at hq
      exact (List.of_mem_zip (show (q.1, q.2) ∈ L.parts.zip cs from hq)).1
    exact VerifiableInference.Desc.Key.pendingRow_ok_at m L q.1 q.2 hk c.1.1 (hpl q.1 hm) t ht
  · cases h

theorem mapM_get {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β), l.mapM f = some r → r.length = l.length ∧ ∀ (i : Nat) (y : β), r[i]? = some y → ∃ x, l[i]? = some x ∧ f x = some y
  | [], r, h => by
    simp at h
    subst h
    exact ⟨rfl, fun i y hy => by simp at hy⟩
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y₀ =>
      cases hl : l.mapM f with
      | none => simp [hx, hl] at h
      | some r' =>
        simp [hx, hl] at h
        subst h
        obtain ⟨e, g⟩ := mapM_get f l r' hl
        refine ⟨by simp [e], fun i y hy => ?_⟩
        cases i with
        | zero =>
          have : y₀ = y := by simpa using hy
          exact ⟨x, rfl, this ▸ hx⟩
        | succ j => exact g j y (by simpa using hy)

theorem pend_law {β : Type} (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (s s' : VerifiableInference.Desc.Key.ChainState β) (h : VerifiableInference.Desc.Key.layPile keysOf one s = .ok s') :
    ∃ rows : List (List TensorRow), s' = { s with pile := rows.flatten } ∧ rows.length = one.ranges.lookups.length ∧
      ∀ (l : Nat) (R : List TensorRow), rows[l]? = some R → ((keysOf s.base)[l]?).bind (KeyReaders.pendingOf one l) = some R := by
  unfold VerifiableInference.Desc.Key.layPile at h
  obtain ⟨_, _, h⟩ := bindX h
  obtain ⟨_, hlen, h⟩ := bindX h
  obtain ⟨rows, hr, h⟩ := bindX h
  obtain ⟨o, _, h⟩ := bindX h
  obtain ⟨L, _, h⟩ := bindX h
  obtain ⟨_, _, h⟩ := bindX h
  cases h
  obtain ⟨e, g⟩ := mapM_get _ _ rows (namedX hr)
  have hl : one.ranges.lookups.length = (keysOf s.base).length := beq_iff_eq.1 (needX hlen)
  refine ⟨rows, rfl, ?_, fun l R hR => ?_⟩
  · rw [e, zipT_eq, List.length_zip, ← hl, Nat.min_self]
  · obtain ⟨x, hx, hp⟩ := g l R hR
    rw [zipT_eq] at hx
    obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.1 (show (one.ranges.lookups.zip (keysOf s.base))[l]? = some (x.1, x.2) from hx)
    rw [h2]
    exact pendingAt_is one l x.1 h1 x.2 R hp

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.pendingAt_is
#print axioms Johnson.RunOne.KeyRows1.pend_law
#print axioms Johnson.RunOne.KeyRows1.pendingAt_ok
