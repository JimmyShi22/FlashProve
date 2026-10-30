-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxOrder.lean: the row that a code switch returns has a form whose tensors are in
order.

The law on fixing the low variables of a form (OnBytes/Iop/FixLaws.lean: Form.fixLow_val) asks that
each tensor is in order (Tensor.InOrder: no dense variable is named twice, and each has the pair
(1, 1)). Before a fold the program tests more (Form.fits). Before the base case it fixes one
variable of the batched row's form without such a test. OnBytes/Slice/BlkPlain.lean and
BlkCsPlain.lean show that the batched row's form has no written-out factor, if the old claim's form
has none. This file shows in the same way that its tensors are in order, if the old claim's are;
that is so after every fold (Form.fixLow_shape).

Main definitions.
  OrderForm, OrderRow   all tensors of a form, of a row's terms and whole vectors, are in order.
Main theorems.
  inOrder_insertChoice   inserted variables that pick bits keep a tensor in order.
  combine_order          the batch of rows in order is in order.
  csRan_order            the row that a run of the code switch returns.
  fixLaw_of_order        the law that the joint before the base case asks (FixLaw).

Not claimed. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkCsJoint
import OnBytes.Slice.BlkProxFold

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun
open Iop Prob Cb _root_.Run

/-- All tensors of the form are in order. -/
def OrderForm (f : Form) : Prop := ∀ v ∈ f.tensors, v.InOrder

/-- The tensors among the row's terms, and those of its whole coefficient vectors, are in order. -/
def OrderRow (r : Row) : Prop :=
  (∀ t ∈ r.terms.toList, t.v.InOrder) ∧ ∀ f ∈ r.forms.toList, OrderForm f.c

/-! ## Tensors -/

/-- A tensor without a written-out factor is in order. -/
theorem inOrder_of_plain {v : Tensor} (h : v.denseVars = []) : v.InOrder := by
  unfold Tensor.InOrder
  rw [h]
  exact ⟨List.nodup_nil, fun _ hd => absurd hd List.not_mem_nil⟩

/-- As many pairs as variables that pick a bit. -/
theorem length_choicePairs : ∀ n value : ℕ, (choicePairs n value).length = n
  | 0, _ => rfl
  | n + 1, value => congrArg (· + 1) (length_choicePairs n (value / 2))

/-- Inserted variables that pick bits keep a tensor in order. -/
theorem inOrder_insertChoice {v : Tensor} (h : v.InOrder) (pos count value : ℕ) :
    (v.insertChoice pos count value).InOrder := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · show (v.denseVars.map fun d => if pos ≤ d then d + count else d).Nodup
    refine h1.map fun a b hab => ?_
    split at hab <;> split at hab <;> omega
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hd'
    have hp := h2 d hd
    have hlt : d < v.pairs.length := (List.getElem?_eq_some_iff.1 hp).1
    show (v.pairs.take pos ++ choicePairs count value ++ v.pairs.drop pos)[
      if pos ≤ d then d + count else d]? = _
    by_cases hc : pos ≤ d
    · have hl : (v.pairs.take pos ++ choicePairs count value).length = pos + count := by
        rw [List.length_append, List.length_take, length_choicePairs]
        omega
      rw [if_pos hc, List.getElem?_append_right (by rw [hl]; omega), hl, List.getElem?_drop,
        ← hp]
      congr 1
      omega
    · have hl : d < (v.pairs.take pos).length := by
        rw [List.length_take]
        omega
      rw [if_neg hc, List.append_assoc, List.getElem?_append_left hl, List.getElem?_take_of_lt
        (by omega)]
      exact hp

/-! ## Forms -/

/-- A form without a written-out factor is in order. -/
theorem orderForm_of_plain {f : Form} (h : PlainForm f) : OrderForm f :=
  fun v hv => inOrder_of_plain (h v hv)

/-- A row without a written-out factor is in order. -/
theorem orderRow_of_plain {r : Row} (h : PlainRow r) : OrderRow r :=
  ⟨fun t ht => inOrder_of_plain (h.1 t ht), fun f hf => orderForm_of_plain (h.2 f hf)⟩

/-- The empty form is in order. -/
theorem orderForm_empty : OrderForm {} := fun _ h => absurd h List.not_mem_nil

/-- A tensor in order may be added. -/
theorem orderForm_add {f : Form} (hf : OrderForm f) {v : Tensor} (hv : v.InOrder) :
    OrderForm (f.add v) := fun w hw => by
  rcases List.mem_cons.1 hw with rfl | h
  · exact hv
  · exact hf w h

/-- Scaling keeps a form in order. -/
theorem orderForm_scale {f : Form} (hf : OrderForm f) (x : E) : OrderForm (f.scale x) :=
  fun w hw => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact (hf v hv).scale x

/-- A multiple of a form in order may be added. -/
theorem orderForm_addForm {f o : Form} (hf : OrderForm f) (ho : OrderForm o) (x : E) :
    OrderForm (f.addForm o x) := fun w hw => by
  rcases List.mem_append.1 hw with h | h
  · exact orderForm_scale ho x w h
  · exact hf w h

/-- Inserted variables that pick bits keep a form in order. -/
theorem orderForm_insertChoice {f : Form} (hf : OrderForm f) (pos count value : ℕ) :
    OrderForm (f.insertChoice pos count value) := fun w hw => by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
  exact inOrder_insertChoice (hf v hv) pos count value

/-! ## The four kinds of parts of a row -/

/-- A coefficient on a single entry keeps the sum in order. -/
theorem addEntryTo_order (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (o : ℕ)
    (part : Part) (index : ℕ) (coeff : E) (hp : OrderForm acc.c)
    (h : addEntryTo S L x acc o part index coeff = some acc') : OrderForm acc'.c := by
  unfold addEntryTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)

/-- A term whose tensor is in order keeps the sum in order. -/
theorem addTermTo_order (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (ht : t.v.InOrder) (hp : OrderForm acc.c) (h : addTermTo S L x acc t = some acc') :
    OrderForm acc'.c := by
  unfold addTermTo at h
  have hv : ∀ pos count value, ((t.v.scale x).insertChoice pos count value).InOrder :=
    inOrder_insertChoice (ht.scale x)
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)
    | (cases h; exact orderForm_add hp (hv _ _ _))

/-- A run of single entries keeps the sum in order. -/
theorem addRunTo_order (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (w : Run)
    (hp : OrderForm acc.c) (h : addRunTo S L x acc w = some acc') : OrderForm acc'.c :=
  foldlM_keeps (fun a : GroupRow => OrderForm a.c) _ _ acc acc'
    (fun _ _ y y' hy hstep => addEntryTo_order S L x y y' _ _ _ _ hy hstep) hp h

/-- A whole coefficient vector in order keeps the sum in order. -/
theorem addFormTo_order (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (hf : OrderForm f.c) (hp : OrderForm acc.c)
    (h : addFormTo S L x acc f = some acc') : OrderForm acc'.c := by
  unfold addFormTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)
    | (cases h; exact orderForm_addForm hp (orderForm_insertChoice hf _ _ _) x)

/-! ## A whole row, and the batch -/

/-- A row in order, carried to the group's tables and added, keeps the sum in order. -/
theorem addToGroupRow_order (S : Statement) (L : GroupLayout) (row : Row) (x : E)
    (acc acc' : GroupRow) (hr : OrderRow row) (hp : OrderForm acc.c)
    (h : addToGroupRow S L row x acc = some acc') : OrderForm acc'.c := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨a1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a2, h2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a3, h3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a4, h4, h⟩ := Option.bind_eq_some_iff.1 h
  have p0 : OrderForm (acc.ready L).c := by
    rw [ready_c]
    exact hp
  have p1 : OrderForm a1.c := foldlM_keeps (fun a : GroupRow => OrderForm a.c) _ _ _ _
    (fun t ht y y' hy hs => addTermTo_order S L x y y' t (hr.1 t ht) hy hs) p0 h1
  have p2 : OrderForm a2.c := foldlM_keeps (fun a : GroupRow => OrderForm a.c) _ _ _ _
    (fun _ _ y y' hy hs => addEntryTo_order S L x y y' _ _ _ _ hy hs) p1 h2
  have p3 : OrderForm a3.c := foldlM_keeps (fun a : GroupRow => OrderForm a.c) _ _ _ _
    (fun w _ y y' hy hs => addRunTo_order S L x y y' w hy hs) p2 h3
  have p4 : OrderForm a4.c := foldlM_keeps (fun a : GroupRow => OrderForm a.c) _ _ _ _
    (fun f hf y y' hy hs => addFormTo_order S L x y y' f (hr.2 f hf) hy hs) p3 h4
  cases h
  exact p4

/-- The batch of rows in order is in order. -/
theorem combine_order (S : Statement) (g : ℕ) (input : RunInput) (x : E) (G : GroupRow)
    (hrows : ∀ r ∈ input.rows.toList, OrderRow r) (h : Bat.combine S g input x = some G) :
    OrderForm G.c := by
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
  have inv : OrderForm s.1.c ∧ s.2.1.terms = #[] ∧ s.2.1.forms = #[] :=
    foldlM_keeps (fun s : GroupRow × Row × E => OrderForm s.1.c ∧ s.2.1.terms = #[] ∧
        s.2.1.forms = #[]) _ _ _ _
      (fun r hr y y' hy hstep => by
        obtain ⟨acc, hacc, hy'⟩ := Option.bind_eq_some_iff.1 hstep
        cases hy'
        have hw := addScaled_written y.2.1 { units := r.units, runs := r.runs } y.2.2 rfl rfl
        have hpr : OrderRow { r with units := #[], runs := #[] } := hrows r hr
        exact ⟨addToGroupRow_order S input.layout _ _ _ _ hpr hy.1 hacc,
          hw.1.trans hy.2.1, hw.2.trans hy.2.2⟩)
      ⟨orderForm_empty, rfl, rfl⟩ hs
  exact addToGroupRow_order S input.layout _ _ _ _
    (orderRow_of_plain (plainRow_of_empty _ inv.2.1 inv.2.2)) inv.1 h

/-! ## The rows of a code switch -/

/-- The carried claim is in order, if the old claim's form on the main row is. -/
theorem orderRow_carriedRow (W : SwitchFrame) (old : SingleRows) (hc : OrderForm old.c) :
    OrderRow (carriedRow W old) := by
  constructor
  · intro u hu
    have e : (carriedRow W old).terms = #[] :=
      (terms_restE _ _ _ _ _).trans (terms_restE _ _ _ _ _)
    rw [e] at hu
    exact absurd hu List.not_mem_nil
  · intro f hf
    have e : (carriedRow W old).forms = #[⟨W.g, switchLift old.c W.code.logEll W.mainCut W.rowBits
        W.tableBits⟩] := (forms_restE _ _ _ _ _).trans (forms_restE _ _ _ _ _)
    rw [e] at hf
    rw [List.mem_singleton.1 hf]
    exact orderForm_insertChoice (orderForm_insertChoice hc _ _ _) _ _ _

/-- The row that a run of the switch returns has a form in order, if the old claim has. -/
theorem csRan_order {old : SingleRows} {T : SwitchTarget} {gp : ℕ} {others : Array OracleNotice}
    {c c' : Ctx} {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}
    (h : CsRan old T gp others c c' out row lay theta D) (hkept : old.kept = #[])
    (hmasks : old.masks = 2) (hno : switchKept old = #[]) (hm : D.G.members = #[])
    (hr : D.G.rows = #[]) (hc : OrderForm old.c) : OrderForm row.c := by
  obtain ⟨W, _, hrun⟩ := h.run_rows hkept hmasks hno hm hr
  refine combine_order _ gp _ theta row (fun r hr' => ?_) h.row
  have hr2 : r ∈ (runRows (D.stR T gp others c) (D.grown c)).toList := hr'
  rw [hrun] at hr2
  unfold csRowsB at hr2
  simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hr2
  rcases hr2 with rfl | rfl | ⟨x, _, rfl | rfl | rfl⟩
  · exact orderRow_carriedRow W old hc
  · exact orderRow_of_plain (plainRow_form c.st.codes T.shape _ ⟨_, D.beta⟩ 0 D.smp h.form)
  · exact orderRow_of_plain (plainRow_genMain _ _ _)
  · exact orderRow_of_plain (plainRow_genMask _ _ _ _)
  · exact orderRow_of_plain (plainRow_genMask _ _ _ _)

/-- The form after a fold is in order, if the row has passed the program's test of its sizes. -/
theorem order_foldOutput (S : Statement) (F : FoldShape) (row : GroupRow) (o : ℕ) (eps : E)
    (gamma : List E) (claim : E) (hr : foldRowOk S F row = true) :
    OrderForm (foldOutput S F row o eps gamma claim).c := by
  intro v hv
  rw [foldOutput_c] at hv
  exact (Form.fixLow_shape row.c gamma eps _
    (fits_tensors row.c _ (fits_of_foldRowOk S F row hr)) v hv).2

/-- The law that the joint before the base case asks, of a form in order whose tensors have a
variable for each coordinate of the point. -/
theorem fixLaw_of_order (f : Form) (hf : OrderForm f) (g : List E)
    (hv : ∀ v ∈ f.tensors, g.length ≤ v.vars) : FixLaw f g := by
  intro p
  have h := Form.fixLow_val rdE f g oneE (fun v hm => ⟨hv v hm, hf v hm⟩) p
  unfold lowSum at h
  rw [sum_list_range] at h
  refine h.trans ?_
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [eqVal_eqW]; rfl

end OnBytes.Slice.ProxRun
