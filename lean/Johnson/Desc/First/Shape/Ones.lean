-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Ones.lean: "THE PAIRS AT THE WRITTEN-OUT VARIABLES ARE (1, 1)" THROUGH THE
BATCHING, THE KEPT MEMBERS' FORMS TOO: so the batched row passes the one test on values in "the
batched row fits the fold" (onesG, FoldMake.lean). General laws; nothing is evaluated.

What the library already has, and is called. It has "in order" (Tensor.InOrder,
OnBytes/Iop/FixLaws.lean:474: each written-out variable is named once and has the pair (1, 1)) and
carries it through scale,
insertChoice, add, addForm and, FOR THE FORM ON THE GROUP's MAIN ROW ALONE, through the batching
(OnBytes/Slice/BlkProxOrder.lean: OrderForm, OrderRow, combine_order). What this file adds is the
kept members' forms.

  1 `onesT_of_inOrder`, `onesF_of_order`; `OrderG`: a row on a group is in order: its form on the
    main row and each kept member's form; `onesG_of_order`.
  2 `orderForm_addEntry`, `onKept_order`, `entryInto_order`, `termInto_order`, `foldlM_keeps`,
    `runInto_order`, `formInto_order`, `ready_order`, `rowInto_order`, **`batch_order`**: the batch
    of rows in order is in order, its kept members' forms too; **`batch_ones`**.

Limits. That the rows which a chain's steps lay are in order (OrderRow) is a premise. Nothing on
the clause "the slice lies inside its vector", which is read off the make (FoldMake.lean's
tensorOrderS). Nothing on what a form is worth. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.FoldMake
import OnBytes.Slice.BlkProxOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open OnBytes.Slice.ProxRun (OrderForm OrderRow orderForm_empty orderForm_add orderForm_scale
  orderForm_addForm orderForm_insertChoice inOrder_insertChoice)

/-! ## 1 From the library's "in order" to the test on values -/

theorem onesT_of_inOrder {v : Tensor} (h : v.InOrder) : onesT v = true := by
  unfold onesT
  simp only [List.all_eq_true, beq_iff_eq]
  exact h.2

theorem onesF_of_order {f : Form} (h : OrderForm f) : onesF f = true := by
  unfold onesF
  rw [List.all_eq_true]
  exact fun v hv => onesT_of_inOrder (h v hv)

/-- A row on a group is in order: its form on the main row AND each kept member's form. -/
def OrderG (a : GroupRow) : Prop := OrderForm a.c ∧ ∀ k ∈ a.kept.toList, OrderForm k.c

theorem onesG_of_order {a : GroupRow} (h : OrderG a) : onesG a = true := by
  unfold onesG
  rw [Bool.and_eq_true, List.all_eq_true]
  exact ⟨onesF_of_order h.1, fun k hk => onesF_of_order (h.2 k hk)⟩

/-! ## 2 The kept forms through the batching -/

theorem orderForm_addEntry {f : Form} (h : OrderForm f) (i : Nat) (c : E) :
    OrderForm (f.addEntry i c) := h

theorem onKept_order {kept : Array KeptForm} (hk : ∀ k ∈ kept.toList, OrderForm k.c) (o : Nat)
    (f : Form → Form) (hf : ∀ c, OrderForm c → OrderForm (f c)) :
    ∀ k ∈ (onKept kept o f).toList, OrderForm k.c := by
  unfold onKept
  split
  · rename_i i _
    intro k hk'
    rw [Array.mem_toList_iff] at hk'
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hk'
    rw [Array.getElem_modify]
    have hj' : j < kept.size := by simpa using hj
    split
    · exact hf _ (hk _ (Array.mem_toList_iff.2 (Array.getElem_mem hj')))
    · exact hk _ (Array.mem_toList_iff.2 (Array.getElem_mem hj'))
  · intro k hk'
    simp only [Array.toList_append, Array.toList_filter, List.mem_append, List.mem_filter] at hk'
    rcases hk' with (⟨h1, -⟩ | h1) | ⟨h1, -⟩
    · exact hk k h1
    · have : k = ⟨o, f {}⟩ := by simpa using h1
      subst this
      exact hf _ orderForm_empty
    · exact hk k h1

theorem entryInto_order {S : Statement} {L : GroupLayout} {x : E} {acc acc' : GroupRow} {o : Nat}
    {part : Part} {index : Nat} {coeff : E} (ha : OrderG acc)
    (h : Own.entryInto S L x acc o part index coeff = some acc') : OrderG acc' := by
  unfold OrderG at ha ⊢
  unfold Own.entryInto at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
          exact ha
        · cases h
    · split at h
      · cases h
        exact ⟨ha.1, onKept_order ha.2 _ _ fun c hc => orderForm_addEntry hc _ _⟩
      · split at h
        · cases h
        · cases h
          exact ⟨orderForm_addEntry ha.1 _ _, ha.2⟩

theorem termInto_order {S : Statement} {L : GroupLayout} {x : E} {acc acc' : GroupRow} {t : Term}
    (ht : t.v.InOrder) (ha : OrderG acc) (h : Own.termInto S L x acc t = some acc') :
    OrderG acc' := by
  unfold OrderG at ha ⊢
  unfold Own.termInto at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · split at h
      · cases h
        exact ⟨ha.1, onKept_order ha.2 _ _ fun c hc => orderForm_add hc (ht.scale x)⟩
      · split at h
        · cases h
        · split at h
          · cases h
          · cases h
            exact ⟨orderForm_add ha.1 (inOrder_insertChoice (ht.scale x) _ _ _), ha.2⟩
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact ha

theorem foldlM_keeps {α ι : Type} (P : α → Prop) (f : α → ι → Option α) :
    ∀ (l : List ι) (a a' : α), (∀ i ∈ l, ∀ y y', P y → f y i = some y' → P y') → P a →
      l.foldlM f a = some a' → P a'
  | [], a, a', _, ha, h => by
    cases h
    exact ha
  | i :: l, a, a', hs, ha, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.1 h
    exact foldlM_keeps P f l y a' (fun j hj => hs j (List.mem_cons_of_mem _ hj))
      (hs i List.mem_cons_self a y ha hy) h

theorem runInto_order {S : Statement} {L : GroupLayout} {x : E} {acc acc' : GroupRow} {w : Run}
    (ha : OrderG acc) (h : Own.runInto S L x acc w = some acc') : OrderG acc' :=
  foldlM_keeps OrderG _ _ _ _ (fun _ _ _ _ hy hs => entryInto_order hy hs) ha h

theorem formInto_order {S : Statement} {L : GroupLayout} {x : E} {acc acc' : GroupRow}
    {f : MainForm} (hf : OrderForm f.c) (ha : OrderG acc)
    (h : Own.formInto S L x acc f = some acc') : OrderG acc' := by
  unfold OrderG at ha ⊢
  unfold Own.formInto at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
      exact ⟨ha.1, onKept_order ha.2 _ _ fun c hc => orderForm_addForm hc hf x⟩
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact ⟨orderForm_addForm ha.1 (orderForm_insertChoice hf _ _ _) x, ha.2⟩

theorem ready_order {acc : GroupRow} (ha : OrderG acc) (L : GroupLayout) :
    OrderG (acc.ready L) := by
  unfold GroupRow.ready
  split
  · exact ha
  · exact ha

theorem rowInto_order {S : Statement} {L : GroupLayout} {row : OnBytes.Row} {x : E}
    {acc acc' : GroupRow} (hr : OrderRow row) (ha : OrderG acc)
    (h : Own.rowInto S L row x acc = some acc') : OrderG acc' := by
  unfold Own.rowInto at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨a1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a2, h2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a3, h3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a4, h4, h⟩ := Option.bind_eq_some_iff.1 h
  have p1 : OrderG a1 := foldlM_keeps OrderG _ _ _ _
    (fun t ht _ _ hy hs => termInto_order (hr.1 t ht) hy hs) (ready_order ha L) h1
  have p2 : OrderG a2 := foldlM_keeps OrderG _ _ _ _
    (fun _ _ _ _ hy hs => entryInto_order hy hs) p1 h2
  have p3 : OrderG a3 := foldlM_keeps OrderG _ _ _ _
    (fun _ _ _ _ hy hs => runInto_order hy hs) p2 h3
  have p4 : OrderG a4 := foldlM_keeps OrderG _ _ _ _
    (fun f hf _ _ hy hs => formInto_order (hr.2 f hf) hy hs) p3 h4
  unfold OrderG at p4 ⊢
  cases h
  exact p4

/-- **The batch of rows in order is in order, its kept members' forms too.** -/
theorem batch_order {S : Statement} {g : Nat} {input : RunInput} {x : E} {G : GroupRow}
    (hrows : ∀ r ∈ input.rows.toList, OrderRow r) (h : Own.batch S g input x = some G) :
    OrderG G := by
  unfold Own.batch at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
  have inv : OrderG s.1 ∧ s.2.1.terms = #[] ∧ s.2.1.forms = #[] :=
    foldlM_keeps (fun s : GroupRow × OnBytes.Row × E => OrderG s.1 ∧ s.2.1.terms = #[] ∧
        s.2.1.forms = #[]) _ _ _ _
      (fun r hr y y' hy hstep => by
        obtain ⟨acc, hacc, hy'⟩ := Option.bind_eq_some_iff.1 hstep
        cases hy'
        have hpr : OrderRow { r with units := #[], runs := #[] } := hrows r hr
        refine ⟨rowInto_order hpr hy.1 hacc, ?_, ?_⟩
        · show (y.2.1.addRunsScaled _ _).terms ++ _ = #[]
          show y.2.1.terms ++ (#[] : Array Term).map _ = #[]
          rw [hy.2.1]
          simp
        · show y.2.1.forms ++ (#[] : Array MainForm).map _ = #[]
          rw [hy.2.2]
          simp)
      ⟨⟨orderForm_empty, fun _ hk => by cases hk⟩, rfl, rfl⟩ hs
  refine rowInto_order ⟨fun t ht => ?_, fun f hf => ?_⟩ inv.1 h
  · rw [inv.2.1] at ht
    exact absurd ht (by simp)
  · rw [inv.2.2] at hf
    exact absurd hf (by simp)

/-- So the batched row passes the one test on values. -/
theorem batch_ones {S : Statement} {g : Nat} {input : RunInput} {x : E} {G : GroupRow}
    (hrows : ∀ r ∈ input.rows.toList, OrderRow r) (h : Own.batch S g input x = some G) :
    onesG G = true := onesG_of_order (batch_order hrows h)

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.onesG_of_order
#print axioms VerifiableInference.Desc.First.Shape.onKept_order
#print axioms VerifiableInference.Desc.First.Shape.rowInto_order
#print axioms VerifiableInference.Desc.First.Shape.batch_order
#print axioms VerifiableInference.Desc.First.Shape.batch_ones
