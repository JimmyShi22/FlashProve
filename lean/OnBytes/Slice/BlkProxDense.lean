-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxDense.lean: coefficient vectors that may have a written-out factor stay
well-formed through three operations of a proximity test, one law each: the batching, a fold, a
switch's carried row. After OnBytes/Slice/BlkProxOrder.lean, for one clause more.

Why. The program's test on a tensor (`Tensor.ok`, OnBytes/Iop/Tensor.lean) has four clauses: at
most 63 variables; THE SLICE LIES INSIDE ITS VECTOR; a written-out variable's pair is (1, 1); none
is named twice. BlkProxOrder.lean carries the last two through these operations (`Tensor.InOrder`,
`OrderForm`). Of the second, at a fold, OnBytes/Iop/FixLaws.lean says "Not shown" (at
`Form.fixLow_shape`). Where no tensor has a written-out factor (`PlainForm`,
OnBytes/Slice/BlkFoldVec.lean; `PlainRow`, BlkPlain.lean) that clause is idle. Rows with such a
factor can come: `linDotRow` (OnBytes/Iop/Lin.lean) is handed a claim's row weights as tensors,
cuts each to the matrix's rows and lays it on the table, and no test there asks that they are
plain.

Main definitions.
  `SliceIn`   the slice lies inside its vector (or there is no written-out variable).
  `DenseTensor`, `DenseForm`, `DenseRow`   `Tensor.InOrder` and `SliceIn`; of all tensors of a
      form; of a row's terms and whole coefficient vectors. ("Dense" after the program's
      `denseVars`: a tensor that MAY have written-out variables; every plain one is among them.)
Main theorems.
  `denseForm_of_plain`, `denseRow_of_plain`   plain gives dense.
  `combine_dense`   the batch of dense rows is a dense form.
  `foldedSlice_size`   WHERE THE SLICE LIES INSIDE ITS VECTOR, the folded slice has exactly one
      entry for each index on the written-out variables that are kept (beneath: `foldBit_size`,
      `slice_loop`).
  `denseForm_fixLow`, `denseForm_foldOutput`   a dense form with its lowest variables fixed is
      dense; so is the form that a fold returns (beneath: `SlicesIn`, `fixLowShared_dense`: a slice
      that tensors share is of the same length).
  `denseForm_switchLift`, `denseRow_carriedRow`   a switch's carried row.
  `fixLaw_of_dense`   the law on fixing that the joint in front of the base case asks.

By what. The batching and the carried row: the steps of `combine_order` and `orderRow_carriedRow`
once more: scaling, inserted variables and sums leave where the slice begins, its vector and the
NUMBER of written-out variables alone. The fold: shown here; the order's half by
`Tensor.fixLowWith_shape`, `Tensor.fixLow_shape`. `fixLaw_of_dense`: `fixLaw_of_order`; the slice's
clause is not spent there.

Kin. `DenseTensor` is `TOk` (Johnson/Desc/K10/Honest/RowFits.lean) with the
two halves swapped, and `DenseForm` is its `All TOk`: by reading; no theorem here ties them.
RowFits.lean has, under its own names, what
section 2 here says of scaling, inserted variables and sums (`TOk.scale`, `TOk.insertChoice`,
`All.empty`, `All.add`, `All.scale`, `All.addForm`, `All.insertChoice`), and the batch's form, kept
forms too (`combine_inv`): under premises that are heavier (the group in order, the layout, the
adding's tests, the 63) and in one point lighter: of the rows' terms it asks order on a MAIN table
alone. Neither of the two files, RowFits.lean and this one, imports the other. New in substance
here: the fold; `combine_dense`, from `DenseRow` of the rows alone; the carried row.

Not claimed. THAT A ROW WHICH THE PROXIMITY TEST TAKES IN IS A `DenseRow` IS A PREMISE HERE (of
`combine_dense` and the lemmas under it): it can be had from the verifier's tests on a tensor and on
a form (`denseRow_of_tests`, Johnson/Desc/Means/Dense.lean), from `PlainRow` (`denseRow_of_plain`),
or, for a switch's carried row, from `denseRow_carriedRow`, which asks in turn that the old claim's
form is dense; and `carriedRow` (OnBytes/Slice/BlkCsRows.lean) has two mask rows and no kept member.
Of that premise the clause on terms on a mask table and on a kept member's table is IDLE in
`combine_dense`, as `OrderRow`'s is in `combine_order`: their tensors never reach `GroupRow.c`.
Nothing on the functions that make tensors (`tensorBelow`, `VectorLay.onTable`, `Tensor.rotate`,
`Tensor.pushDense`, `Tensor.setValues`). No law on a whole run: `csRan_order` (BlkProxOrder.lean:
the row that a switch returns) has no fellow here. THE FORM ON THE GROUP's MAIN ROW ALONE
(`GroupRow.c`): a kept member's form gets tensors too, and nothing is said of it here, as in
`combine_order`. Nothing on the number of variables or on single entries. Nothing on what such a
vector's entries are. Nothing on completeness, on soundness or on what is hidden.
-/
import OnBytes.Slice.BlkProxOrder
import OnBytes.Slice.BlkCsPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Slice.ProxRun

/-! ## 1 The predicate -/

/-- The slice lies inside its vector, or the tensor has no written-out variable. -/
def SliceIn (v : Tensor) : Prop :=
  v.denseVars = [] ∨ v.first + 2 ^ v.denseVars.length ≤ v.values.size

/-- A tensor that may have a written-out factor: no written-out variable is named twice, each has
the pair (1, 1), and the slice lies inside its vector. -/
def DenseTensor (v : Tensor) : Prop := v.InOrder ∧ SliceIn v

/-- All tensors of the form are such tensors. -/
def DenseForm (f : Form) : Prop := ∀ v ∈ f.tensors, DenseTensor v

/-- The tensors among the row's terms, and those of its whole coefficient vectors, are such
tensors. -/
def DenseRow (r : OnBytes.Row) : Prop :=
  (∀ t ∈ r.terms.toList, DenseTensor t.v) ∧ ∀ f ∈ r.forms.toList, DenseForm f.c

/-- A tensor without a written-out factor is one. -/
theorem denseTensor_of_plain {v : Tensor} (h : v.denseVars = []) : DenseTensor v :=
  ⟨inOrder_of_plain h, Or.inl h⟩

/-- A form without a written-out factor is one. -/
theorem denseForm_of_plain {f : Form} (h : PlainForm f) : DenseForm f :=
  fun v hv => denseTensor_of_plain (h v hv)

/-- A row without a written-out factor is one. -/
theorem denseRow_of_plain {r : OnBytes.Row} (h : PlainRow r) : DenseRow r :=
  ⟨fun t ht => denseTensor_of_plain (h.1 t ht), fun f hf => denseForm_of_plain (h.2 f hf)⟩

/-- Such a form is in order. -/
theorem DenseForm.order {f : Form} (h : DenseForm f) : OrderForm f := fun v hv => (h v hv).1

/-! ## 2 Scaling, inserted variables, sums -/

/-- A multiple of such a tensor is one. -/
theorem DenseTensor.scale {v : Tensor} (h : DenseTensor v) (x : E) : DenseTensor (v.scale x) := by
  refine ⟨Tensor.InOrder.scale h.1 x, ?_⟩
  have e1 : (v.scale x).denseVars = v.denseVars := Tensor.denseVars_scale v x
  have e2 : (v.scale x).first = v.first := by
    unfold Tensor.scale
    rfl
  have e3 : (v.scale x).values = v.values := by
    unfold Tensor.scale
    rfl
  unfold SliceIn
  rw [e1, e2, e3]
  exact h.2

/-- Inserted variables that pick bits keep it: where the slice begins, its vector and the number of
written-out variables stay. -/
theorem DenseTensor.insertChoice {v : Tensor} (h : DenseTensor v) (pos count value : Nat) :
    DenseTensor (v.insertChoice pos count value) := by
  refine ⟨inOrder_insertChoice h.1 pos count value, ?_⟩
  rcases h.2 with h2 | h2
  · left
    show (v.denseVars.map _) = []
    rw [h2]
    rfl
  · right
    show v.first + 2 ^ (v.denseVars.map _).length ≤ v.values.size
    rw [List.length_map]
    exact h2

/-- The empty form is one: it has no tensor. -/
theorem denseForm_empty : DenseForm {} := fun _ h => absurd h List.not_mem_nil

/-- Such a tensor may be added. -/
theorem denseForm_add {f : Form} (hf : DenseForm f) {v : Tensor} (hv : DenseTensor v) :
    DenseForm (f.add v) := fun w hw => by
  rcases List.mem_cons.1 hw with rfl | h
  · exact hv
  · exact hf w h

/-- Scaling keeps it. -/
theorem denseForm_scale {f : Form} (hf : DenseForm f) (x : E) : DenseForm (f.scale x) :=
  fun w hw => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact (hf v hv).scale x

/-- A multiple of such a form may be added. -/
theorem denseForm_addForm {f o : Form} (hf : DenseForm f) (ho : DenseForm o) (x : E) :
    DenseForm (f.addForm o x) := fun w hw => by
  rcases List.mem_append.1 hw with h | h
  · exact denseForm_scale ho x w h
  · exact hf w h

/-- Inserted variables that pick bits keep it. -/
theorem denseForm_insertChoice {f : Form} (hf : DenseForm f) (pos count value : Nat) :
    DenseForm (f.insertChoice pos count value) := fun w hw => by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
  exact (hf v hv).insertChoice pos count value

/-! ## 3 The batching -/

/-- Adding a coefficient on a single entry leaves the sum's form dense: no tensor is added. -/
theorem addEntryTo_dense (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (o : Nat)
    (part : Part) (index : Nat) (coeff : E) (hp : DenseForm acc.c)
    (h : addEntryTo S L x acc o part index coeff = some acc') : DenseForm acc'.c := by
  unfold addEntryTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)

/-- A term with such a tensor keeps it. -/
theorem addTermTo_dense (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (ht : DenseTensor t.v) (hp : DenseForm acc.c) (h : addTermTo S L x acc t = some acc') :
    DenseForm acc'.c := by
  unfold addTermTo at h
  have hv : ∀ pos count value, DenseTensor ((t.v.scale x).insertChoice pos count value) :=
    (ht.scale x).insertChoice
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)
    | (cases h; exact denseForm_add hp (hv _ _ _))

/-- A run of single entries keeps it. -/
theorem addRunTo_dense (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (w : Run)
    (hp : DenseForm acc.c) (h : addRunTo S L x acc w = some acc') : DenseForm acc'.c :=
  foldlM_keeps (fun a : GroupRow => DenseForm a.c) _ _ acc acc'
    (fun _ _ y y' hy hstep => addEntryTo_dense S L x y y' _ _ _ _ hy hstep) hp h

/-- A whole coefficient vector that is such a form keeps it. -/
theorem addFormTo_dense (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (hf : DenseForm f.c) (hp : DenseForm acc.c)
    (h : addFormTo S L x acc f = some acc') : DenseForm acc'.c := by
  unfold addFormTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)
    | (cases h; exact denseForm_addForm hp (denseForm_insertChoice hf _ _ _) x)

/-- Such a row, carried to the group's tables and added, keeps it. -/
theorem addToGroupRow_dense (S : Statement) (L : GroupLayout) (row : OnBytes.Row) (x : E)
    (acc acc' : GroupRow) (hr : DenseRow row) (hp : DenseForm acc.c)
    (h : addToGroupRow S L row x acc = some acc') : DenseForm acc'.c := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨a1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a2, h2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a3, h3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a4, h4, h⟩ := Option.bind_eq_some_iff.1 h
  have p0 : DenseForm (acc.ready L).c := by
    rw [ready_c]
    exact hp
  have p1 : DenseForm a1.c := foldlM_keeps (fun a : GroupRow => DenseForm a.c) _ _ _ _
    (fun t ht y y' hy hs => addTermTo_dense S L x y y' t (hr.1 t ht) hy hs) p0 h1
  have p2 : DenseForm a2.c := foldlM_keeps (fun a : GroupRow => DenseForm a.c) _ _ _ _
    (fun _ _ y y' hy hs => addEntryTo_dense S L x y y' _ _ _ _ hy hs) p1 h2
  have p3 : DenseForm a3.c := foldlM_keeps (fun a : GroupRow => DenseForm a.c) _ _ _ _
    (fun w _ y y' hy hs => addRunTo_dense S L x y y' w hy hs) p2 h3
  have p4 : DenseForm a4.c := foldlM_keeps (fun a : GroupRow => DenseForm a.c) _ _ _ _
    (fun f hf y y' hy hs => addFormTo_dense S L x y y' f (hr.2 f hf) hy hs) p3 h4
  cases h
  exact p4

/-- **The batch of such rows is such a form.** -/
theorem combine_dense (S : Statement) (g : Nat) (input : RunInput) (x : E) (G : GroupRow)
    (hrows : ∀ r ∈ input.rows.toList, DenseRow r) (h : Bat.combine S g input x = some G) :
    DenseForm G.c := by
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
  have inv : DenseForm s.1.c ∧ s.2.1.terms = #[] ∧ s.2.1.forms = #[] :=
    foldlM_keeps (fun s : GroupRow × OnBytes.Row × E => DenseForm s.1.c ∧ s.2.1.terms = #[] ∧
        s.2.1.forms = #[]) _ _ _ _
      (fun r hr y y' hy hstep => by
        obtain ⟨acc, hacc, hy'⟩ := Option.bind_eq_some_iff.1 hstep
        cases hy'
        have hw := addScaled_written y.2.1 { units := r.units, runs := r.runs } y.2.2 rfl rfl
        have hpr : DenseRow { r with units := #[], runs := #[] } := hrows r hr
        exact ⟨addToGroupRow_dense S input.layout _ _ _ _ hpr hy.1 hacc,
          hw.1.trans hy.2.1, hw.2.trans hy.2.2⟩)
      ⟨denseForm_empty, rfl, rfl⟩ hs
  exact addToGroupRow_dense S input.layout _ _ _ _
    (denseRow_of_plain (plainRow_of_empty _ inv.2.1 inv.2.2)) inv.1 h

/-! ## 4 A switch's carried row -/

/-- **A dense form, carried to the new stage's table, is dense.** -/
theorem denseForm_switchLift {c : Form} (hc : DenseForm c) (vars : Nat) (cut : RowCut)
    (tableRowBits tableBits : Nat) : DenseForm (switchLift c vars cut tableRowBits tableBits) :=
  denseForm_insertChoice (denseForm_insertChoice hc _ _ _) _ _ _

/-- The carried claim is such a row, if the old claim's form on the main row is such a form. -/
theorem denseRow_carriedRow (W : SwitchFrame) (old : SingleRows) (hc : DenseForm old.c) :
    DenseRow (carriedRow W old) := by
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
    exact denseForm_switchLift hc _ _ _ _

/-! ## 5 A fold -/

/-- A loop that pushes one entry a turn. -/
theorem fold_push_size {α : Type} (f : Nat → α) : ∀ (n : Nat) (init : Array α),
    (Nat.fold n (fun idx _ (out : Array α) => out.push (f idx)) init).size = init.size + n
  | 0, _ => rfl
  | n + 1, init => by
    rw [Nat.fold_succ, Array.size_push, fold_push_size f n init]
    omega

/-- Folding a bit out of a stretch halves it. -/
theorem foldBit_size (a : Array E) (start size i : Nat) (x : E) :
    (foldBit a start size i x).size = size / 2 := by
  unfold foldBit
  dsimp only
  rw [fold_push_size]
  simp

/-- The loop that folds a slice: the stretch stays inside its vector, and has one entry for each
index on the written-out variables that are kept. -/
theorem slice_loop (v : Tensor) (g : List E) : ∀ (m : Nat) (s : Array E × Nat × Nat),
    m ≤ v.denseVars.length → s.2.1 + s.2.2 ≤ s.1.size →
    s.2.2 = 2 ^ (m + (keptVars g.length (v.denseVars.drop m)).length) →
    ((List.range m).reverse.foldl (sliceStep v g) s).2.1 +
        ((List.range m).reverse.foldl (sliceStep v g) s).2.2 ≤
      ((List.range m).reverse.foldl (sliceStep v g) s).1.size ∧
    ((List.range m).reverse.foldl (sliceStep v g) s).2.2 =
      2 ^ (keptVars g.length v.denseVars).length
  | 0, s, _, h1, h2 => by
    refine ⟨h1, ?_⟩
    show s.2.2 = _
    rw [h2]
    simp
  | m + 1, s, hm, h1, h2 => by
    have hlt : m < v.denseVars.length := hm
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    have hd : v.denseVars.drop m = v.denseVars[m] :: v.denseVars.drop (m + 1) :=
      List.drop_eq_getElem_cons hlt
    have hs : sliceStep v g s m =
        if v.denseVars[m] < g.length then
          (foldBit s.1 s.2.1 s.2.2 m (g.getD v.denseVars[m] zeroE), 0, s.2.2 / 2) else s := by
      unfold sliceStep
      rw [List.getElem?_eq_getElem hlt]
    rw [hs]
    by_cases hc : v.denseVars[m] < g.length
    · rw [if_pos hc]
      refine slice_loop v g m _ (Nat.le_of_lt hlt) ?_ ?_
      · show 0 + s.2.2 / 2 ≤ (foldBit _ _ _ _ _).size
        rw [foldBit_size]
        omega
      · show s.2.2 / 2 = _
        have ek : keptVars g.length (v.denseVars.drop m) =
            keptVars g.length (v.denseVars.drop (m + 1)) := by
          rw [hd]
          unfold keptVars
          rw [List.filter_cons_of_neg (by simpa using hc)]
        rw [ek, h2, show m + 1 + (keptVars g.length (v.denseVars.drop (m + 1))).length =
          (m + (keptVars g.length (v.denseVars.drop (m + 1))).length) + 1 by omega, Nat.pow_succ,
          Nat.mul_div_cancel _ (by omega)]
    · rw [if_neg hc]
      refine slice_loop v g m s (Nat.le_of_lt hlt) h1 ?_
      have ek : (keptVars g.length (v.denseVars.drop m)).length =
          (keptVars g.length (v.denseVars.drop (m + 1))).length + 1 := by
        rw [hd]
        unfold keptVars
        rw [List.filter_cons_of_pos (by simpa using hc)]
        simp
      rw [h2, ek]
      congr 1
      omega

/-- **Where the slice lies inside its vector, the folded slice has one entry for each index on the
written-out variables that are kept.** -/
theorem foldedSlice_size (v : Tensor) (g : List E)
    (h : v.first + 2 ^ v.denseVars.length ≤ v.values.size) :
    (v.foldedSlice g).size = 2 ^ (keptVars g.length v.denseVars).length := by
  obtain ⟨h1, h2⟩ := slice_loop v g v.denseVars.length (v.values, v.first, 2 ^ v.denseVars.length)
    (Nat.le_refl _) h (by simp [keptVars])
  rw [Tensor.foldedSlice_eq]
  dsimp only
  split
  · rename_i hc
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hc
    rw [hc.2, h2]
  · rw [Array.size_extract, ← h2]
    omega

/-- The tensor that `Tensor.fixLowWith` returns, handed a folded slice that is long enough: its
slice lies inside its vector. -/
theorem sliceIn_fixLowWith (v : Tensor) (g : List E) (slice : Array E)
    (hs : 2 ^ (keptVars g.length v.denseVars).length ≤ slice.size) :
    SliceIn (v.fixLowWith g slice) := by
  unfold Tensor.fixLowWith
  dsimp only
  split
  · exact Or.inl rfl
  · right
    show 0 + 2 ^ (keptVars g.length v.denseVars).length ≤ slice.size
    omega

/-- A tensor with its lowest variables fixed: its slice lies inside its vector, if the tensor's
did. -/
theorem sliceIn_fixLow (v : Tensor) (g : List E) (h : SliceIn v) : SliceIn (v.fixLow g) := by
  unfold Tensor.fixLow
  split
  · rename_i hc
    have hne := v.dense_of_cut _ hc
    rcases h with h | h
    · rw [h] at hne
      cases hne
    · exact sliceIn_fixLowWith v g _ (Nat.le_of_eq (foldedSlice_size v g h).symm)
  · dsimp only
    rcases h with h | h
    · left
      show v.denseVars.map _ = []
      rw [h]
      rfl
    · right
      show v.first + 2 ^ (v.denseVars.map _).length ≤ v.values.size
      rw [List.length_map]
      exact h

/-- What holds of the table of folded slices: each stored tensor is under its own key, with its own
slice folded, and its slice lies inside its vector. -/
def SlicesIn (g : List E) (M : Form.FoldedSlices) : Prop :=
  ∀ key (c : Tensor × Array E), M[key]? = some c → c.1.sliceKey = key ∧
    c.2 = c.1.foldedSlice g ∧ c.1.first + 2 ^ c.1.denseVars.length ≤ c.1.values.size

/-- One step of the loop of `Form.fixLow`: the table stays as asked, and one tensor is added, which
is such a tensor. A slice that is taken from the table has the length of the tensor's own: under
one key two tensors have the same written-out variables. -/
theorem fixLowShared_dense (g : List E) (s : List Tensor × Form.FoldedSlices) (v : Tensor)
    (hM : SlicesIn g s.2) (hv : DenseTensor v) :
    SlicesIn g (Form.fixLowShared g s v).2 ∧
      ∃ t, (Form.fixLowShared g s v).1 = t :: s.1 ∧ DenseTensor t := by
  unfold Form.fixLowShared
  by_cases hc : v.sliceIsCut g.length = true
  · rw [if_pos hc]
    dsimp only
    have hne := v.dense_of_cut _ hc
    have hin : v.first + 2 ^ v.denseVars.length ≤ v.values.size := by
      rcases hv.2 with h | h
      · rw [h] at hne
        cases hne
      · exact h
    have own := Nat.le_of_eq (foldedSlice_size v g hin).symm
    cases hf : s.2[v.sliceKey]? with
    | some c =>
      obtain ⟨k1, k2, k3⟩ := hM _ c hf
      refine ⟨hM, _, rfl, (Tensor.fixLowWith_shape v g _ hv.1).2, sliceIn_fixLowWith v g _ ?_⟩
      split
      · have ed : c.1.denseVars = v.denseVars := congrArg (·.2.1) k1
        rw [k2, foldedSlice_size c.1 g k3, ed]
      · exact own
    | none =>
      refine ⟨?_, _, rfl, (Tensor.fixLowWith_shape v g _ hv.1).2, sliceIn_fixLowWith v g _ own⟩
      intro key c hcm
      rw [Std.HashMap.getElem?_insertIfNew] at hcm
      split at hcm
      · rename_i hk
        have ek : v.sliceKey = key := by simpa using hk.1
        have ec : (v, v.foldedSlice g) = c := by simpa using hcm
        rw [← ec]
        exact ⟨ek, rfl, hin⟩
      · exact hM key c hcm
  · rw [if_neg hc]
    exact ⟨hM, _, rfl, (Tensor.fixLow_shape v g hv.1).2, sliceIn_fixLow v g hv.2⟩

/-- The loop of `Form.fixLow`: from dense tensors, and stored slices as `SlicesIn` asks, it gathers
dense tensors alone. -/
theorem fixLow_loop_dense (g : List E) (times : E) :
    ∀ (l : List Tensor) (s : List Tensor × Form.FoldedSlices), SlicesIn g s.2 →
    (∀ v ∈ l, DenseTensor v) → (∀ t ∈ s.1, DenseTensor t) →
    ∀ t ∈ (l.foldl (fun s v => Form.fixLowShared g s (v.scale times)) s).1, DenseTensor t
  | [], _, _, _, hs => hs
  | v :: l, s, hM, hl, hs => by
    obtain ⟨hM', t, e1, e2⟩ := fixLowShared_dense g s (v.scale times) hM
      ((hl v (by simp)).scale times)
    rw [List.foldl_cons]
    apply fixLow_loop_dense g times l _ hM' (fun w hw => hl w (by simp [hw]))
    intro u hu
    rw [e1] at hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact e2
    · exact hs u hu

/-- **A form with its lowest variables fixed is such a form again.** -/
theorem denseForm_fixLow {f : Form} (hf : DenseForm f) (g : List E) (times : E) :
    DenseForm (f.fixLow g times) := by
  intro t ht
  unfold Form.fixLow at ht
  dsimp only at ht
  have h0 : SlicesIn g ({} : Form.FoldedSlices) := by
    intro key c hc
    simp at hc
  exact fixLow_loop_dense g times f.tensors ([], {}) h0 hf (by simp) t (List.mem_reverse.1 ht)

/-- So is the form that a fold returns. -/
theorem denseForm_foldOutput (S : Statement) (F : FoldShape) (row : GroupRow) (o : Nat) (eps : E)
    (gamma : List E) (claim : E) (h : DenseForm row.c) :
    DenseForm (foldOutput S F row o eps gamma claim).c := by
  rw [foldOutput_c]
  exact denseForm_fixLow h gamma eps

/-! ## 6 The base case's law on fixing -/

/-- The law that the joint in front of the base case asks (`FixLaw`, OnBytes/Slice/BaseLast.lean),
of such a form whose tensors have a variable for each coordinate of the point. -/
theorem fixLaw_of_dense (f : Form) (hf : DenseForm f) (g : List E)
    (hv : ∀ v ∈ f.tensors, g.length ≤ v.vars) : FixLaw f g :=
  fixLaw_of_order f hf.order g hv

end OnBytes.Slice.ProxRun

#print axioms OnBytes.Slice.ProxRun.denseTensor_of_plain
#print axioms OnBytes.Slice.ProxRun.denseForm_of_plain
#print axioms OnBytes.Slice.ProxRun.denseRow_of_plain
#print axioms OnBytes.Slice.ProxRun.DenseForm.order
#print axioms OnBytes.Slice.ProxRun.DenseTensor.scale
#print axioms OnBytes.Slice.ProxRun.DenseTensor.insertChoice
#print axioms OnBytes.Slice.ProxRun.denseForm_empty
#print axioms OnBytes.Slice.ProxRun.denseForm_add
#print axioms OnBytes.Slice.ProxRun.denseForm_scale
#print axioms OnBytes.Slice.ProxRun.denseForm_addForm
#print axioms OnBytes.Slice.ProxRun.denseForm_insertChoice
#print axioms OnBytes.Slice.ProxRun.addEntryTo_dense
#print axioms OnBytes.Slice.ProxRun.addTermTo_dense
#print axioms OnBytes.Slice.ProxRun.addRunTo_dense
#print axioms OnBytes.Slice.ProxRun.addFormTo_dense
#print axioms OnBytes.Slice.ProxRun.addToGroupRow_dense
#print axioms OnBytes.Slice.ProxRun.combine_dense
#print axioms OnBytes.Slice.ProxRun.denseForm_switchLift
#print axioms OnBytes.Slice.ProxRun.denseRow_carriedRow
#print axioms OnBytes.Slice.ProxRun.fold_push_size
#print axioms OnBytes.Slice.ProxRun.foldBit_size
#print axioms OnBytes.Slice.ProxRun.slice_loop
#print axioms OnBytes.Slice.ProxRun.foldedSlice_size
#print axioms OnBytes.Slice.ProxRun.sliceIn_fixLowWith
#print axioms OnBytes.Slice.ProxRun.sliceIn_fixLow
#print axioms OnBytes.Slice.ProxRun.fixLowShared_dense
#print axioms OnBytes.Slice.ProxRun.fixLow_loop_dense
#print axioms OnBytes.Slice.ProxRun.denseForm_fixLow
#print axioms OnBytes.Slice.ProxRun.denseForm_foldOutput
#print axioms OnBytes.Slice.ProxRun.fixLaw_of_dense
