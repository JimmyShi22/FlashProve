-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FormFit.lean: TENSORS AND FORMS KEEP FITTING (`tensorInOrder`,
`formFits`, Johnson/Desc/Own/Shapes.lean) AS A CODE SWITCH CARRIES THEM TO A LARGER TABLE: by
inserted variables that pick bits. Statements and proofs.

  `lt_block`        x below m, c below k: x + c m lies below k m
  `index_insert`, `choice_length`   the index to which an inserted stretch of bits moves an entry;
                    as many pairs as inserted variables
  `inOrder_insert`  a tensor in order, with count variables inserted: in order; count variables more
  `formFits_insert` a form that fits n variables, the like: it fits n + count
  `formFits_lift`   `switchLift`: it fits the table's index bits
  `inOrder_plain`   a tensor without a written-out factor and with at most 63 variables
  `fold_add_fits`, `fold_entry_fits`   tensors, single entries, added one by one
  `formFits_on`     the form of a row without stretches and forms (`formOn`,
                    Johnson/Top/H0/K2Hands/RowsOrder.lean), whose tensors and single entries fit

Limits. Nothing on any property.

-/
import Johnson.Desc.Own.ShapesMean
import Johnson.Top.H0.K2Hands.RowsOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.First.K2Hands (formOn)

/-- x below m, c below k: x + c m lies below k m. -/
theorem lt_block (x m c k : Nat) (hx : x < m) (hc : c < k) : x + c * m < k * m :=
  calc x + c * m < m + c * m := by omega
    _ = (c + 1) * m := by rw [Nat.succ_mul, Nat.add_comm]
    _ ≤ k * m := Nat.mul_le_mul_right _ hc

/-- The index to which an inserted stretch of bits moves an entry. -/
theorem index_insert (e n pos count value : Nat) (he : e < 2 ^ n) (hp : pos ≤ n) :
    e % 2 ^ pos + (value % 2 ^ count) * 2 ^ pos + (e / 2 ^ pos) * 2 ^ (pos + count) <
      2 ^ (n + count) := by
  have h1 : e % 2 ^ pos + (value % 2 ^ count) * 2 ^ pos < 2 ^ (pos + count) := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ pos)]
    exact lt_block _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))
  have h2 : e / 2 ^ pos < 2 ^ (n - pos) := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    have : pos + (n - pos) = n := by omega
    rw [this]
    exact he
  have h3 := lt_block _ _ _ _ h1 h2
  have e4 : 2 ^ (n - pos) * 2 ^ (pos + count) = 2 ^ (n + count) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [e4] at h3
  exact h3

/-- As many pairs as variables that pick a bit. -/
theorem choice_length : ∀ n value : Nat, (choicePairs n value).length = n
  | 0, _ => rfl
  | n + 1, value => congrArg (· + 1) (choice_length n (value / 2))

/-- **A tensor in order, with count variables inserted.** -/
theorem inOrder_insert (v : Tensor) (h : Own.InOrder v) (pos count value : Nat)
    (hp : pos ≤ v.pairs.length) (h63 : v.pairs.length + count ≤ 63) :
    (v.insertChoice pos count value).pairs.length = v.pairs.length + count ∧
      Own.InOrder (v.insertChoice pos count value) := by
  obtain ⟨_, h2, h3, h4⟩ := h
  have hlen : (v.insertChoice pos count value).pairs.length = v.pairs.length + count := by
    show (v.pairs.take pos ++ choicePairs count value ++ v.pairs.drop pos).length = _
    rw [List.length_append, List.length_append, List.length_take, List.length_drop,
      choice_length]
    omega
  refine ⟨hlen, by rw [hlen]; exact h63, ?_, ?_, ?_⟩
  · rcases h2 with h2 | h2
    · left
      show v.denseVars.map _ = []
      rw [h2]
      rfl
    · right
      show v.first + 2 ^ (v.denseVars.map _).length ≤ v.values.size
      rw [List.length_map]
      exact h2
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hd'
    have hpd := h3 d hd
    have hlt : d < v.pairs.length := (List.getElem?_eq_some_iff.1 hpd).1
    show (v.pairs.take pos ++ choicePairs count value ++ v.pairs.drop pos)[
      if pos ≤ d then d + count else d]? = _
    by_cases hc : pos ≤ d
    · have hl : (v.pairs.take pos ++ choicePairs count value).length = pos + count := by
        rw [List.length_append, List.length_take, choice_length]
        omega
      rw [if_pos hc, List.getElem?_append_right (by rw [hl]; omega), hl, List.getElem?_drop,
        ← hpd]
      congr 1
      omega
    · have hl : d < (v.pairs.take pos).length := by
        rw [List.length_take]
        omega
      rw [if_neg hc, List.append_assoc, List.getElem?_append_left hl, List.getElem?_take_of_lt
        (by omega)]
      exact hpd
  · show (v.denseVars.map fun d => if pos ≤ d then d + count else d).Nodup
    refine h4.map fun a b hab => ?_
    split at hab <;> split at hab <;> omega

/-- **A form that fits n variables, with count variables inserted, fits n + count.** -/
theorem formFits_insert (f : Form) (n pos count value : Nat) (h : Own.formFits f n = true)
    (hp : pos ≤ n) (h63 : n + count ≤ 63) :
    Own.formFits (f.insertChoice pos count value) (n + count) = true := by
  obtain ⟨h1, h2⟩ := (Own.formFits_iff f n).1 h
  refine (Own.formFits_iff _ _).2 ⟨fun w hw => ?_, fun e he => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    obtain ⟨a, b⟩ := h1 v hv
    have := inOrder_insert v b pos count value (by rw [a]; exact hp) (by rw [a]; exact h63)
    rw [a] at this
    exact this
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact index_insert _ _ _ _ _ (h2 e' he') hp

/-- **`switchLift` fits the table's index bits.** -/
theorem formFits_lift (c : Form) (vars : Nat) (cut : RowCut) (R tb : Nat)
    (h : Own.formFits c vars = true) (hb : cut.bits ≤ vars) (hv : vars + (R - cut.bits) ≤ tb)
    (h63 : tb ≤ 63) : Own.formFits (switchLift c vars cut R tb) tb = true := by
  unfold switchLift
  have h1 := formFits_insert c vars cut.bits (R - cut.bits) (cut.firstRow / 2 ^ cut.bits) h hb
    (by omega)
  have h2 := formFits_insert _ (vars + (R - cut.bits)) (vars + (R - cut.bits))
    (tb - (vars + (R - cut.bits))) 0 h1 (Nat.le_refl _) (by omega)
  have e : vars + (R - cut.bits) + (tb - (vars + (R - cut.bits))) = tb := by omega
  rw [e] at h2
  exact h2

/-- A tensor without a written-out factor and with at most 63 variables is in order. -/
theorem inOrder_plain (v : Tensor) (hd : v.denseVars = []) (h63 : v.pairs.length ≤ 63) :
    Own.InOrder v :=
  ⟨h63, Or.inl hd, fun d h => by rw [hd] at h; exact absurd h List.not_mem_nil, by
    rw [hd]; exact List.nodup_nil⟩

/-- Tensors added one by one. -/
theorem fold_add_fits (n : Nat) : ∀ (l : List Term) (c : Form), Own.formFits c n = true →
    (∀ t ∈ l, t.v.pairs.length = n ∧ Own.InOrder t.v) →
    Own.formFits (l.foldl (fun (c : Form) t => c.add t.v) c) n = true
  | [], _, h, _ => h
  | t :: l, c, h, hl => by
    rw [List.foldl_cons]
    refine fold_add_fits n l _ ?_ fun x hx => hl x (List.mem_cons_of_mem _ hx)
    obtain ⟨h1, h2⟩ := (Own.formFits_iff c n).1 h
    refine (Own.formFits_iff _ _).2 ⟨fun v hv => ?_, h2⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hl t (List.mem_cons_self ..)
    · exact h1 v hv

/-- Single entries added one by one. -/
theorem fold_entry_fits (n : Nat) : ∀ (l : List Single) (c : Form), Own.formFits c n = true →
    (∀ u ∈ l, u.index < 2 ^ n) →
    Own.formFits (l.foldl (fun (c : Form) u => c.addEntry u.index u.coeff) c) n = true
  | [], _, h, _ => h
  | u :: l, c, h, hl => by
    rw [List.foldl_cons]
    refine fold_entry_fits n l _ ?_ fun x hx => hl x (List.mem_cons_of_mem _ hx)
    obtain ⟨h1, h2⟩ := (Own.formFits_iff c n).1 h
    refine (Own.formFits_iff _ _).2 ⟨h1, fun e he => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hl u (List.mem_cons_self ..)
    · exact h2 e he

/-- **The form of a row without stretches and forms.** -/
theorem formFits_on (row : OnBytes.Row) (n : Nat) (hr : row.runs = #[]) (hf : row.forms = #[])
    (ht : ∀ t ∈ row.terms.toList, t.v.pairs.length = n ∧ Own.InOrder t.v)
    (hu : ∀ u ∈ row.units.toList, u.index < 2 ^ n) : Own.formFits (formOn row) n = true := by
  unfold formOn
  rw [hr, hf]
  simp only [List.foldl_nil, ← Array.foldl_toList]
  exact fold_entry_fits n _ _ (fold_add_fits n _ _ rfl ht) hu

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.formFits_lift
#print axioms VerifiableInference.Desc.K2.Honest.Returns.formFits_on
