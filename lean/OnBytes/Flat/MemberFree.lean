-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/MemberFree.lean: the first part of the test on the table, in a dry run, at two lists of
rows on the table that differ in their weights alone.

States: (memberFree) `MemberFree` (OnBytes/Flat/LinksFree.lean): for every shape S, every number im
of an index-mask message, and two lists of rows that are alike row by row (`RowAlike`: equal column
points, mask forms and targets; weights with the same numbers of variables): from every dry context
`memberFirstVerify S im rows` and `memberFirstVerify S im rows'` both fail, or both return, with one
context left and with the same four numbers (`LinFirst.Alike`).
A dry context is one in which the channel is dry AND no intermediate values are kept (`Ctx.Dry`,
OnBytes/Iop/DrySizes.lean).
How, by the program's text (OnBytes/Iop/Lin.lean, Batt.lean): the tests on the rows read lengths,
numbers of variables and the mask entries' messages (memberRowsFit_eq, fits_eq); the batching's
claim and summand read column points, mask forms and targets (claimOf_eq, summandOf_eq), so the
sumcheck is one text at one argument; the row that is handed on has weights with the same numbers
of variables (rowOf_alike); the first part reads of its claim the mask entries' messages; the rest
of the claim goes to three calls that do nothing here: one that a dry channel skips
(Blk.addRowsOnView) and two that are idle where no intermediate values are kept (Blk.note,
Blk.noteBy). The frame is OnBytes/Flat/DryRel.lean's relB; that a routine leaves the two flags of a
run as they are is shown by the walk `keeps` (OnBytes/Flat/LinksKeepsTool.lean).
The small laws on `All2` are private to this file.
Not claimed: that the rounds of a first chain are the same at two requests: that follows
(plannedFirstFree_of, OnBytes/Flat/LinksFree.lean) only with further statements (LayerFree,
PendingFree, HeadFree p, and an inequality between two public numbers), none of which is shown in
this file. Two failures count as alike whatever their names. The claim that the first part passes on
DOES hang on the weights: `LinFirst.Alike` asks nothing of it. No evaluation looks at this statement
by itself. Nothing on a run on a view. For proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksFree

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Stages

/-! ## Two lists, member by member: seven more laws -/

/-- What is made of each member is the same: so are the lists laid end to end. -/
private theorem All2.flatMap_eq {α β γ : Type} {R : α → β → Prop} {f : α → List γ} {g : β → List γ}
    (h : ∀ a b, R a b → f a = g b) {l : List α} {l' : List β} (hl : All2 R l l') :
    l.flatMap f = l'.flatMap g := by
  induction hl with
  | nil => rfl
  | cons h0 _ ih => simp only [List.flatMap_cons, h _ _ h0, ih]

/-- A fold whose steps agree on members in relation. -/
private theorem All2.foldl_eq {α β γ : Type} {R : α → β → Prop} {f : γ → α → γ} {g : γ → β → γ}
    (h : ∀ c a b, R a b → f c a = g c b) {l : List α} {l' : List β} (hl : All2 R l l') (c : γ) :
    l.foldl f c = l'.foldl g c := by
  induction hl generalizing c with
  | nil => rfl
  | cons h0 _ ih => simp only [List.foldl_cons, h _ _ _ h0, ih]

/-- A test that agrees on members in relation. -/
private theorem All2.all_eq {α β : Type} {R : α → β → Prop} {f : α → Bool} {g : β → Bool}
    (h : ∀ a b, R a b → f a = g b) {l : List α} {l' : List β} (hl : All2 R l l') :
    l.all f = l'.all g := by
  induction hl with
  | nil => rfl
  | cons h0 _ ih => simp only [List.all_cons, h _ _ h0, ih]

/-- Both lists are empty, or neither. -/
private theorem All2.isEmpty_eq {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (hl : All2 R l l') : l.isEmpty = l'.isEmpty := by
  cases hl <;> rfl

/-- What is read of the first members is the same. -/
private theorem All2.head_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (h : ∀ a b, R a b → f a = g b) {l : List α} {l' : List β} (hl : All2 R l l') :
    l.head?.map f = l'.head?.map g := by
  cases hl with
  | nil => rfl
  | cons h0 _ => exact congrArg some (h _ _ h0)

/-- Paired with one list on the left. -/
private theorem All2.zip_left {α β γ : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (hl : All2 R l l') (c : List γ) :
    All2 (fun p p' => p.1 = p'.1 ∧ R p.2 p'.2) (c.zip l) (c.zip l') := by
  induction hl generalizing c with
  | nil =>
    rw [List.zip_nil_right, List.zip_nil_right]
    exact .nil
  | cons h0 _ ih =>
    cases c with
    | nil =>
      rw [List.zip_nil_left, List.zip_nil_left]
      exact .nil
    | cons x t =>
      rw [List.zip_cons_cons, List.zip_cons_cons]
      exact .cons ⟨rfl, h0⟩ (ih t)

/-- Paired with one list on the right. -/
private theorem All2.zip_right {α β γ : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (hl : All2 R l l') (c : List γ) :
    All2 (fun p p' => R p.1 p'.1 ∧ p.2 = p'.2) (l.zip c) (l'.zip c) := by
  induction hl generalizing c with
  | nil =>
    rw [List.zip_nil_left, List.zip_nil_left]
    exact .nil
  | cons h0 _ ih =>
    cases c with
    | nil =>
      rw [List.zip_nil_right, List.zip_nil_right]
      exact .nil
    | cons x t =>
      rw [List.zip_cons_cons, List.zip_cons_cons]
      exact .cons ⟨h0, rfl⟩ (ih t)

/-! ## Weights with the same numbers of variables -/

/-- Two lists of weights with one list of numbers of variables, member by member. -/
theorem vars_all2 : ∀ {l l' : List Tensor}, l.map Tensor.vars = l'.map Tensor.vars →
    All2 (fun t t' => t.vars = t'.vars) l l'
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (vars_all2 h.2)

/-- A test on the numbers of variables. -/
theorem vars_all {r r' : TensorRow} (h : RowAlike r r') (q : Nat → Bool) :
    (r.g.all fun t => q t.vars) = (r'.g.all fun t => q t.vars) :=
  (vars_all2 h.2.2.2).all_eq fun t t' e => by
    show q t.vars = q t'.vars
    rw [e]

/-! ## The tests on the rows -/

/-- The comparison of the rows with the shape reads lengths, numbers of variables and the mask
entries' messages. -/
theorem memberRowsFit_eq (st : Statement) (S : Params.LinShape) (im : Nat)
    {rows rows' : List TensorRow} (h : All2 RowAlike rows rows') :
    memberRowsFit st S im rows = memberRowsFit st S im rows' := by
  have e1 : rows.isEmpty = rows'.isEmpty := h.isEmpty_eq
  have e2 : (rows.all fun r =>
        (r.masks.all fun m => m.1.oracle == im) && r.psi.length == S.kCol &&
          r.g.all (·.vars == S.kRow)) =
      (rows'.all fun r =>
        (r.masks.all fun m => m.1.oracle == im) && r.psi.length == S.kCol &&
          r.g.all (·.vars == S.kRow)) :=
    h.all_eq fun r r' k => by
      show ((r.masks.all fun m => m.1.oracle == im) && r.psi.length == S.kCol &&
          r.g.all fun t => t.vars == S.kRow) =
        ((r'.masks.all fun m => m.1.oracle == im) && r'.psi.length == S.kCol &&
          r'.g.all fun t => t.vars == S.kRow)
      rw [k.1, k.2.1, vars_all k fun n => n == S.kRow]
  unfold memberRowsFit
  rw [e1, e2]

/-- So does the batching's test on the rows' form. -/
theorem fits_eq (kCol : Nat) {rows rows' : List TensorRow} (h : All2 RowAlike rows rows') :
    Batt.fits kCol rows = Batt.fits kCol rows' := by
  cases h with
  | nil => rfl
  | @cons r r' l l' h0 ht =>
    have hh : r.g.head?.map Tensor.vars = r'.g.head?.map Tensor.vars :=
      (vars_all2 h0.2.2.2).head_eq fun _ _ e => e
    have e2 : ((r :: l).all fun s =>
          s.psi.length == kCol && !s.g.isEmpty &&
            s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) =
        ((r' :: l').all fun s =>
          s.psi.length == kCol && !s.g.isEmpty &&
            s.g.all fun t => some t.vars == r'.g.head?.map Tensor.vars) :=
      (All2.cons h0 ht).all_eq fun s s' k => by
        have e1 : s.g.isEmpty = s'.g.isEmpty := (vars_all2 k.2.2.2).isEmpty_eq
        show (s.psi.length == kCol && !s.g.isEmpty &&
            s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) =
          (s'.psi.length == kCol && !s'.g.isEmpty &&
            s'.g.all fun t => some t.vars == r'.g.head?.map Tensor.vars)
        rw [k.1, e1, hh, vars_all k fun n => some n == r'.g.head?.map Tensor.vars]
    show (decide (1 ≤ kCol) && (r :: l).all fun s =>
          s.psi.length == kCol && !s.g.isEmpty &&
            s.g.all fun t => some t.vars == r.g.head?.map Tensor.vars) =
        (decide (1 ≤ kCol) && (r' :: l').all fun s =>
          s.psi.length == kCol && !s.g.isEmpty &&
            s.g.all fun t => some t.vars == r'.g.head?.map Tensor.vars)
    rw [e2]

/-! ## The batching's claim, summand and row -/

/-- The batching's claim reads column points' lengths, mask forms and targets. -/
theorem claimOf_eq (x : E) {rows rows' : List TensorRow} (h : All2 RowAlike rows rows') :
    Batt.claimOf rows x = Batt.claimOf rows' x := by
  have z := h.zip_left (Psc.powers oneE x rows'.length)
  have e0 : rows.head?.map (·.psi.length) = rows'.head?.map (·.psi.length) := by
    cases h with
    | nil => rfl
    | cons h0 _ => exact congrArg (fun p : List E => some p.length) h0.1
  have e1 : (((Psc.powers oneE x rows'.length).zip rows).flatMap fun p =>
        Psc.scaleForm p.1 p.2.masks) =
      (((Psc.powers oneE x rows'.length).zip rows').flatMap fun p =>
        Psc.scaleForm p.1 p.2.masks) :=
    z.flatMap_eq fun p p' k => by
      show Psc.scaleForm p.1 p.2.masks = Psc.scaleForm p'.1 p'.2.masks
      rw [k.1, k.2.2.1]
  have e2 : (((Psc.powers oneE x rows'.length).zip rows).foldl
        (fun t p => addE t (mulE p.1 p.2.target)) zeroE) =
      (((Psc.powers oneE x rows'.length).zip rows').foldl
        (fun t p => addE t (mulE p.1 p.2.target)) zeroE) :=
    z.foldl_eq (fun t p p' k => by
      show addE t (mulE p.1 p.2.target) = addE t (mulE p'.1 p'.2.target)
      rw [k.1, k.2.2.2.1]) zeroE
  unfold Batt.claimOf Batt.chiOf
  rw [h.length, zipT_eq, zipT_eq, e0, e1, e2]

/-- The batching's summand reads the column points. -/
theorem summandOf_eq (x : E) {rows rows' : List TensorRow} (h : All2 RowAlike rows rows') :
    Batt.summandOf rows x = Batt.summandOf rows' x := by
  have z := h.zip_left (Psc.powers oneE x rows'.length)
  have e : ∀ point : List E,
      (((Psc.powers oneE x rows'.length).zip rows).map fun p =>
        mulE p.1 (eqEval p.2.psi point)) =
      (((Psc.powers oneE x rows'.length).zip rows').map fun p =>
        mulE p.1 (eqEval p.2.psi point)) := fun point =>
    All2.map_eq (fun p p' k => by
      show mulE p.1 (eqEval p.2.psi point) = mulE p'.1 (eqEval p'.2.psi point)
      rw [k.1, k.2.1]) z
  unfold Batt.summandOf Batt.chiOf
  rw [h.length, zipT_eq, zipT_eq]
  simp only [e]

/-- A weight times an element has as many variables. -/
theorem vars_scale (t : Tensor) (y : E) : (t.scale y).vars = t.vars := by
  unfold Tensor.vars Tensor.scale
  rfl

/-- So have all weights of a list. -/
theorem map_scale_vars (y : E) : ∀ g : List Tensor,
    (g.map fun t => t.scale y).map Tensor.vars = g.map Tensor.vars
  | [] => rfl
  | t :: g => by
    show (t.scale y).vars :: (g.map fun t => t.scale y).map Tensor.vars =
      t.vars :: g.map Tensor.vars
    rw [vars_scale, map_scale_vars y g]

/-- The row that the batching hands on: alike again. -/
theorem rowOf_alike {rows rows' : List TensorRow} (h : All2 RowAlike rows rows') (o : Psc.Out) :
    RowAlike (Batt.rowOf rows o) (Batt.rowOf rows' o) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  have key : ∀ {m m' : List (TensorRow × E)},
      All2 (fun p p' => RowAlike p.1 p'.1 ∧ p.2 = p'.2) m m' →
      (m.flatMap fun p => p.1.g.map fun t => t.scale p.2).map Tensor.vars =
        (m'.flatMap fun p => p.1.g.map fun t => t.scale p.2).map Tensor.vars := by
    intro m m' hm
    induction hm with
    | nil => rfl
    | @cons p p' l l' k _ ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, ih]
      show List.map Tensor.vars (p.1.g.map fun t => t.scale p.2) ++ _ =
        List.map Tensor.vars (p'.1.g.map fun t => t.scale p'.2) ++ _
      rw [map_scale_vars, map_scale_vars, k.1.2.2.2]
  show ((zipT rows o.rowMaps).flatMap fun p => p.1.g.map fun t => t.scale p.2).map Tensor.vars =
    ((zipT rows' o.rowMaps).flatMap fun p => p.1.g.map fun t => t.scale p.2).map Tensor.vars
  rw [zipT_eq, zipT_eq]
  exact key (h.zip_right o.rowMaps)

/-- The batching of several rows into one. -/
theorem battVerify_rel (kCol im : Nat) {rows rows' : List TensorRow}
    (h : All2 RowAlike rows rows') :
    relB RowAlike (Batt.verify kCol rows im) (Batt.verify kCol rows' im) := by
  unfold Batt.verify
  rw [fits_eq kCol h, h.length]
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun x => ?_
  simp only [claimOf_eq x h, summandOf_eq x h]
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun fresh => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun o => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  exact relB_pure (rowOf_alike h o)

/-! ## The first part of the test on the table -/

/-- New rows that only a run on a view computes. -/
theorem addRowsOnView_rel (g : Nat) (r r' : Unit → Option (List Row)) :
    relB Eq (Blk.addRowsOnView g r) (Blk.addRowsOnView g r') := by
  unfold Blk.addRowsOnView
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  refine relB_bind (Blk.keeps_getOnView _ _ _) (relB_getOnView _ r r' _) fun l l' e => ?_
  subst e
  exact relB_refl _

/-- The request's own group and the row (Eval), at two claims with the same mask entries. -/
theorem linFirstRows_rel (S : Params.LinShape) {c c' : LinClaim} (hm : c.masks = c'.masks)
    (ids : Array Nat) : relB LinFirst.Alike (linFirstRows S c ids) (linFirstRows S c' ids) := by
  unfold linFirstRows
  rw [hm]
  by_cases hS : S.ownSplitNeeded = true <;> by_cases hA : S.masksAhead = true <;>
    simp only [hS, hA, ↓reduceIte, Bool.false_eq_true]
  all_goals
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun w => ?_
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun own => ?_
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun split => ?_
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun mask => ?_
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun st => ?_
    refine relB_bind (by show Over.K (m := Blk) _; keeps) (addRowsOnView_rel own _ _)
      fun _ _ _ => ?_
    exact relB_pure ⟨rfl, rfl, rfl, rfl⟩

/-- The first part, at two claims with the same mask entries. -/
theorem linFirstVerify_rel (S : Params.LinShape) {c c' : LinClaim} (hm : c.masks = c'.masks) :
    relB LinFirst.Alike (linFirstVerify S c) (linFirstVerify S c') := by
  unfold linFirstVerify
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun st => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun ids => ?_
  refine relB_bind (by show Over.K (m := Blk) _; keeps) (linFirstRows_rel S hm ids)
    fun out out' ho => ?_
  refine relB_bind (by show Over.K (m := Blk) _; keeps) (relB_note _ _ _) fun _ _ _ => ?_
  refine relB_bind (by show Over.K (m := Blk) _; keeps) (relB_noteBy _ _ _) fun _ _ _ => ?_
  exact relB_pure ho

/-- **In a dry run, whether the first part of the test on the table returns, the context that it
leaves and the four numbers that it passes on do not hang on the values in the rows' weights.** The
claim that it passes on does. -/
theorem memberFree : MemberFree := by
  intro S im rows rows' h
  have tail : ∀ one one' : TensorRow, RowAlike one one' →
      relB LinFirst.Alike
        (Blk.note "member: the claim's target" one.target >>= fun _ =>
          linFirstVerify S (memberClaim one))
        (Blk.note "member: the claim's target" one'.target >>= fun _ =>
          linFirstVerify S (memberClaim one')) := by
    intro one one' ho
    refine relB_bind (by show Over.K (m := Blk) _; keeps) (relB_note _ _ _) fun _ _ _ => ?_
    refine linFirstVerify_rel S ?_
    show (one.masks.map fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)).toArray =
      (one'.masks.map fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)).toArray
    rw [ho.2.1]
  have many : ∀ {l l' : List TensorRow}, All2 RowAlike l l' →
      relB LinFirst.Alike
        (Batt.verify S.kCol l im >>= fun r =>
          Blk.note "BATT: target" r.target >>= fun _ =>
          Blk.note "BATT: gamma_0" (r.psi.headD zeroE) >>= fun _ =>
          Blk.note "BATT: the first weight's scalar" ((r.g.head?.map (·.scalar)).getD zeroE) >>=
            fun _ =>
          Blk.note "BATT: coefficient of its first mask entry"
            ((r.masks.head?.map (·.2)).getD zeroE) >>= fun _ =>
          Blk.note "BATT: coefficient of the last mask term"
            ((r.masks.getLast?.map (·.2)).getD zeroE) >>= fun _ =>
          pure r >>= fun one =>
          Blk.note "member: the claim's target" one.target >>= fun _ =>
          linFirstVerify S (memberClaim one))
        (Batt.verify S.kCol l' im >>= fun r =>
          Blk.note "BATT: target" r.target >>= fun _ =>
          Blk.note "BATT: gamma_0" (r.psi.headD zeroE) >>= fun _ =>
          Blk.note "BATT: the first weight's scalar" ((r.g.head?.map (·.scalar)).getD zeroE) >>=
            fun _ =>
          Blk.note "BATT: coefficient of its first mask entry"
            ((r.masks.head?.map (·.2)).getD zeroE) >>= fun _ =>
          Blk.note "BATT: coefficient of the last mask term"
            ((r.masks.getLast?.map (·.2)).getD zeroE) >>= fun _ =>
          pure r >>= fun one =>
          Blk.note "member: the claim's target" one.target >>= fun _ =>
          linFirstVerify S (memberClaim one)) := by
    intro l l' hl
    refine relB_bind (by show Over.K (m := Blk) _; keeps) (battVerify_rel S.kCol im hl)
      fun r r' hr => ?_
    refine relB_bind (by show Over.K (m := Blk) _; keeps) (relB_note _ _ _) fun _ _ _ => ?_
    refine relB_bind (by show Over.K (m := Blk) _; keeps) (relB_note _ _ _) fun _ _ _ => ?_
    refine relB_bind (by show Over.K (m := Blk) _; keeps) (relB_note _ _ _) fun _ _ _ => ?_
    refine relB_bind (by show Over.K (m := Blk) _; keeps) (relB_note _ _ _) fun _ _ _ => ?_
    refine relB_bind (by show Over.K (m := Blk) _; keeps) (relB_note _ _ _) fun _ _ _ => ?_
    exact relB_bind (by show Over.K (m := Blk) _; keeps) (relB_pure hr) tail
  unfold memberFirstVerify
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun st => ?_
  simp only [memberRowsFit_eq st S im h]
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  cases h with
  | nil => exact many .nil
  | cons h0 ht =>
    cases ht with
    | nil => exact relB_bind (by show Over.K (m := Blk) _; keeps) (relB_pure h0) tail
    | cons h1 ht' => exact many (.cons h0 (.cons h1 ht'))

#print axioms memberFree

end OnBytes.Flat
