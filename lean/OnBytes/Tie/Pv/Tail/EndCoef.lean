-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndCoef.lean: what the routine that sets the row weights of every virtual row
(`HTailF2.coefficientsF`, OnBytes/Model/Tail.lean) keeps, and what it sets on a table's vector.

Definitions, and theorems with their proofs. The routine changes the state by steps of one kind: it
changes one virtual row of one array (`HTailF2.onRow`).

Main names:
  `coefAt F t r`: the row weights of virtual row r of array t. `hasRow F t r`: the state has that
    row.
  `coefAt_same`, `coefAt_other`, `hasRow_onRow`, `kind_onRow`: one step.
  `forIn_id_mem`, `forIn_id_set`, `id_bind_inv`: loops without effects: a property that every turn
    keeps; one that one turn sets and the others keep.
  `coefficientsF_inv`: a property of the state that every such step keeps holds after the routine.
  `coefficientsF_rest`: the routine leaves the context, and of the state all but the arrays.
  `coefficientsF_shape`: it leaves each array's kind and numbers of rows, of columns and of virtual
    rows.
  `UApart`, `coefficientsF_unit`: after the routine the first virtual row of a table's vector has
    the one row weight 1, where the vector's array is another than those of the digits, of the
    planes, of the symbols and of the lookup's pieces.

Limits: nothing on the product form of a row's weights. That the arrays' numbers differ is a
premise.


-/
import OnBytes.Tie.Pv.Tail.EndRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

/-! ## One step -/

/-- The row weights of virtual row r of array t. -/
def coefAt (F : Fork) (t r : Nat) : Array E := ((F.trees.getD t {}).rows.getD r {}).coef

/-- The state has virtual row r of array t. -/
def hasRow (F : Fork) (t r : Nat) : Prop := t < F.trees.size ∧ r < (F.trees.getD t {}).rows.size

/-- An array with one entry changed. -/
theorem getD_modify {α : Type} (a : Array α) (i j : Nat) (f : α → α) (d : α) :
    (a.modify i f).getD j d = if i = j ∧ j < a.size then f (a.getD j d) else a.getD j d := by
  by_cases hj : j < a.size
  · by_cases hij : i = j
    · subst hij
      simp [Array.getD, hj, Array.getElem_modify]
    · simp [Array.getD, hj, Array.getElem_modify, hij]
  · simp [Array.getD, hj]

/-- A step keeps the rows that are there. -/
theorem hasRow_onRow (F : Fork) (t r t' r' : Nat) (f : HRow → HRow) (h : hasRow F t r) :
    hasRow (HTailF2.onRow F t' r' f) t r := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [HTailF2.onRow, h1], ?_⟩
  show r < ((F.trees.modify t' fun X => { X with rows := X.rows.modify r' f }).getD t {}).rows.size
  rw [getD_modify]
  by_cases hc : t' = t ∧ t < F.trees.size
  · rw [if_pos hc]
    show r < ((F.trees.getD t {}).rows.modify r' f).size
    rw [Array.size_modify]
    exact h2
  · rw [if_neg hc]
    exact h2

/-- A step keeps every array's kind. -/
theorem kind_onRow (F : Fork) (t t' r' : Nat) (f : HRow → HRow) :
    ((HTailF2.onRow F t' r' f).trees.getD t {}).kind = (F.trees.getD t {}).kind := by
  show ((F.trees.modify t' fun X => { X with rows := X.rows.modify r' f }).getD t {}).kind = _
  rw [getD_modify]
  by_cases hc : t' = t ∧ t < F.trees.size
  · rw [if_pos hc]
  · rw [if_neg hc]

/-- The row that a step changes. -/
theorem coefAt_same (F : Fork) (t r : Nat) (f : HRow → HRow) (h : hasRow F t r) :
    coefAt (HTailF2.onRow F t r f) t r = (f ((F.trees.getD t {}).rows.getD r {})).coef := by
  obtain ⟨h1, h2⟩ := h
  show (((F.trees.modify t fun X => { X with rows := X.rows.modify r f }).getD t {}).rows.getD r
    {}).coef = _
  rw [getD_modify, if_pos ⟨rfl, h1⟩]
  show ((((F.trees.getD t {}).rows.modify r f)).getD r {}).coef = _
  rw [getD_modify, if_pos ⟨rfl, h2⟩]

/-- A row that a step does not change. -/
theorem coefAt_other (F : Fork) (t r t' r' : Nat) (f : HRow → HRow) (h : ¬ (t' = t ∧ r' = r)) :
    coefAt (HTailF2.onRow F t' r' f) t r = coefAt F t r := by
  show (((F.trees.modify t' fun X => { X with rows := X.rows.modify r' f }).getD t {}).rows.getD r
    {}).coef = _
  rw [getD_modify]
  by_cases hc : t' = t ∧ t < F.trees.size
  · rw [if_pos hc]
    show ((((F.trees.getD t {}).rows.modify r' f)).getD r {}).coef = _
    rw [getD_modify, if_neg (fun hh => h ⟨hc.1, hh.1⟩)]
    rfl
  · rw [if_neg hc]
    rfl

/-! ## Loops without effects -/

/-- A property that every turn of a loop keeps holds after the loop. The turn's result is written by
a match, so that the text of a loop's body reduces to it. -/
theorem forIn_id_mem {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β)) :
    ∀ (l : List α) (b : β),
      (∀ a, a ∈ l → ∀ b, P b → P (match f a b with | .yield x => x | .done x => x)) →
      P b → P (forIn l b f : Id β)
  | [], b, _, h => by simpa using h
  | a :: l, b, hf, h => by
    rw [List.forIn_cons]
    have h1 := hf a (List.mem_cons_self) b h
    show P (match f a b with | .done x => x | .yield x => (forIn l x f : Id β))
    cases e : f a b with
    | done x => rw [e] at h1; exact h1
    | yield x =>
      rw [e] at h1
      exact forIn_id_mem P f l x (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) h1

/-- A property that one turn of a loop sets and the other turns keep holds after the loop. -/
theorem forIn_id_set {α β : Type} (P Q : β → Prop) (f : α → β → Id (ForInStep β)) (a0 : α) :
    ∀ (l : List α) (b : β),
      (∀ a, a ∈ l → ∀ b, ∃ x, f a b = ForInStep.yield x) →
      (∀ a, a ∈ l → ∀ b, P b → P (match f a b with | .yield x => x | .done x => x)) →
      (∀ a, a ∈ l → ∀ b, P b → Q b → Q (match f a b with | .yield x => x | .done x => x)) →
      (∀ b, P b → Q (match f a0 b with | .yield x => x | .done x => x)) →
      a0 ∈ l → P b → Q (forIn l b f : Id β)
  | [], _, _, _, _, _, hm, _ => absurd hm (List.not_mem_nil)
  | a :: l, b, hy, hP, hQ, h0, hm, h => by
    rw [List.forIn_cons]
    obtain ⟨x, hx⟩ := hy a (List.mem_cons_self) b
    have p1 := hP a (List.mem_cons_self) b h
    show Q (match f a b with | .done x => x | .yield x => (forIn l x f : Id β))
    rw [hx] at p1 ⊢
    by_cases hl : a0 ∈ l
    · exact forIn_id_set P Q f a0 l x (fun a' ha' => hy a' (List.mem_cons_of_mem _ ha'))
        (fun a' ha' => hP a' (List.mem_cons_of_mem _ ha'))
        (fun a' ha' => hQ a' (List.mem_cons_of_mem _ ha')) h0 hl p1
    · have e : a0 = a := by
        rcases List.mem_cons.1 hm with e | e
        · exact e
        · exact absurd e hl
      subst e
      have q1 := h0 b h
      rw [hx] at q1
      exact (forIn_id_mem (fun y => P y ∧ Q y) f l x
        (fun a' ha' b' hb' => ⟨hP a' (List.mem_cons_of_mem _ ha') b' hb'.1,
          hQ a' (List.mem_cons_of_mem _ ha') b' hb'.1 hb'.2⟩) ⟨p1, q1⟩).2

/-- Two computations without effects, one after the other. -/
theorem id_bind_inv {β γ : Type} (P : β → Prop) (Q : γ → Prop) (x : Id β) (f : β → Id γ) (hx : P x)
    (hf : ∀ b, P b → Q (f b)) : Q (x >>= f) := hf x hx

/-- Changing the state by a function always succeeds and leaves the context. -/
theorem modify_ok (f : Fork → Fork) (F G : Fork) (c c' : Ctx) (u : PUnit) :
    (modify f : SubM PUnit) F c = .ok ((u, G), c') ↔ G = f F ∧ c' = c := by
  show (Except.ok ((PUnit.unit, f F), c) : Except Failure ((PUnit × Fork) × Ctx)) = _ ↔ _
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ## What the routine keeps -/

/-- A property of the state that every change of one virtual row keeps holds after the routine. -/
theorem coefficientsF_inv (P : Fork → Prop)
    (hP : ∀ (r : Fork) (t' r' : Nat) (f : HRow → HRow), P r → P (HTailF2.onRow r t' r' f))
    (tl : HTailF2) (F G : Fork) (c c' : Ctx) (h : tl.coefficientsF F c = .ok (((), G), c'))
    (h0 : P F) : P G ∧ c' = c := by
  unfold HTailF2.coefficientsF at h
  simp only [bind_ok, get_ok, modify_ok] at h
  obtain ⟨g, F1, c1, ⟨_, hF, hc⟩, hG, hc'⟩ := h
  subst hF
  refine ⟨?_, hc'.trans hc⟩
  rw [hG]
  simp only [Id.run]
  refine id_bind_inv P P _ _ ?_ (fun r1 h1 => ?_)
  · refine forIn_id_mem P _ _ _ ?_ h0
    intro n _ r hr
    cases tl.ix.U.getD n none with
    | none => exact hr
    | some t =>
      by_cases hk : ((r.trees.getD t {}).kind == HKind.table) = true
      · simp only [hk, if_true]; exact hP _ _ _ _ hr
      · simp only [hk]; exact hr
  refine id_bind_inv P P _ _ ?_ (fun r2 h2 => ?_)
  · refine forIn_id_mem P _ _ _ ?_ h1
    intro q _ r hr
    show P (forIn (tl.zOf q).pieces r _ : Id Fork)
    rw [← Array.forIn_toList]
    refine forIn_id_mem P _ _ _ ?_ hr
    intro p _ r' hr'
    exact hP _ _ _ _ hr'
  refine id_bind_inv P P _ _ ?_ (fun r3 h3 => ?_)
  · refine forIn_id_mem P _ _ _ ?_ (hP _ _ _ _ (hP _ _ _ _ h2))
    intro e _ r hr
    exact hP _ _ _ _ hr
  refine id_bind_inv P P _ _ ?_ (fun r4 h4 => h4)
  refine forIn_id_mem P _ _ _ ?_ (hP _ _ _ _ h3)
  intro mu _ r hr
  exact hP _ _ _ _ hr

/-- The routine leaves the context, and of the state all but the arrays. -/
theorem coefficientsF_rest (tl : HTailF2) (F G : Fork) (c c' : Ctx)
    (h : tl.coefficientsF F c = .ok (((), G), c')) : G = { F with trees := G.trees } ∧ c' = c :=
  coefficientsF_inv (fun r => r = { F with trees := r.trees })
    (fun r t' r' f hr => by
      show HTailF2.onRow r t' r' f = { F with trees := (HTailF2.onRow r t' r' f).trees }
      unfold HTailF2.onRow
      rw [hr]) tl F G c c' h rfl

/-- The kind and the sizes of array t. -/
def shapeAt (F : Fork) (t : Nat) : HKind × Nat × Nat × Nat :=
  ((F.trees.getD t {}).kind, (F.trees.getD t {}).R, (F.trees.getD t {}).K,
    (F.trees.getD t {}).rows.size)

/-- A step keeps every array's kind and sizes. -/
theorem shapeAt_onRow (F : Fork) (t t' r' : Nat) (f : HRow → HRow) :
    shapeAt (HTailF2.onRow F t' r' f) t = shapeAt F t := by
  unfold shapeAt
  show (((F.trees.modify t' fun X => { X with rows := X.rows.modify r' f }).getD t {}).kind,
    ((F.trees.modify t' fun X => { X with rows := X.rows.modify r' f }).getD t {}).R,
    ((F.trees.modify t' fun X => { X with rows := X.rows.modify r' f }).getD t {}).K,
    ((F.trees.modify t' fun X => { X with rows := X.rows.modify r' f }).getD t {}).rows.size) = _
  rw [getD_modify]
  by_cases hc : t' = t ∧ t < F.trees.size
  · rw [if_pos hc]
    show ((F.trees.getD t {}).kind, (F.trees.getD t {}).R, (F.trees.getD t {}).K,
      ((F.trees.getD t {}).rows.modify r' f).size) = _
    rw [Array.size_modify]
  · rw [if_neg hc]

/-- The routine leaves each array's kind and sizes, and the number of the arrays. -/
theorem coefficientsF_shape (tl : HTailF2) (F G : Fork) (c c' : Ctx)
    (h : tl.coefficientsF F c = .ok (((), G), c')) :
    (∀ t, shapeAt G t = shapeAt F t) ∧ G.trees.size = F.trees.size :=
  (coefficientsF_inv (fun r => (∀ t, shapeAt r t = shapeAt F t) ∧ r.trees.size = F.trees.size)
    (fun r t' r' f hr => ⟨fun t => (shapeAt_onRow r t t' r' f).trans (hr.1 t), by
      show (r.trees.modify t' _).size = _
      rw [Array.size_modify]
      exact hr.2⟩) tl F G c c' h ⟨fun _ => rfl, rfl⟩).1

/-! ## What the routine sets on a table's vector -/

/-- The array tU is vector number n0 of the tables, of the kind «table», with a first virtual row;
and its number is another than those of the arrays of the digits, of the planes, of the symbols and
of the lookup's pieces. -/
structure UApart (tl : HTailF2) (n0 tU : Nat) (F : Fork) : Prop where
  n0_lt : n0 < 4
  isU : tl.ix.U.getD n0 none = some tU
  row : hasRow F tU 0
  table : ((F.trees.getD tU {}).kind == HKind.table) = true
  uZZ : tl.ix.ZZ ≠ tU
  uBZ : tl.ix.BZ ≠ tU
  uS : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tU
  uP : ∀ q p, p ∈ (tl.zOf q).pieces.toList → p.tree ≠ tU

/-- After the routine the first virtual row of a table's vector has the one row weight 1. -/
theorem coefficientsF_unit (tl : HTailF2) (n0 tU : Nat) (F G : Fork) (c c' : Ctx)
    (A : UApart tl n0 tU F) (h : tl.coefficientsF F c = .ok (((), G), c')) :
    coefAt G tU 0 = #[oneE] := by
  unfold HTailF2.coefficientsF at h
  simp only [bind_ok, get_ok, modify_ok] at h
  obtain ⟨g, F1, c1, ⟨_, hF, _⟩, hG, _⟩ := h
  subst hF
  rw [hG]
  simp only [Id.run]
  let P : Fork → Prop := fun r =>
    hasRow r tU 0 ∧ ((r.trees.getD tU {}).kind == HKind.table) = true
  let Q : Fork → Prop := fun r => coefAt r tU 0 = #[oneE]
  have keepP : ∀ (r : Fork) (t' r' : Nat) (f : HRow → HRow), P r → P (HTailF2.onRow r t' r' f) :=
    fun r t' r' f hp => ⟨hasRow_onRow _ _ _ _ _ _ hp.1, by rw [kind_onRow]; exact hp.2⟩
  have keepQ : ∀ (r : Fork) (t' r' : Nat) (f : HRow → HRow), t' ≠ tU → Q r →
      Q (HTailF2.onRow r t' r' f) :=
    fun r t' r' f ht hq => (coefAt_other r tU 0 t' r' f (fun hh => ht hh.1)).trans hq
  have R : P F1 := ⟨A.row, A.table⟩
  refine id_bind_inv (fun r => P r ∧ Q r) Q _ _ ⟨?_, ?_⟩ (fun r1 h1 => ?_)
  · refine forIn_id_mem P _ _ _ ?_ R
    intro n _ r hr
    cases tl.ix.U.getD n none with
    | none => exact hr
    | some t =>
      by_cases hk : ((r.trees.getD t {}).kind == HKind.table) = true
      · simp only [hk, if_true]; exact keepP _ _ _ _ hr
      · simp only [hk]; exact hr
  · refine forIn_id_set P Q _ n0 _ _ ?_ ?_ ?_ ?_ (List.mem_range.2 A.n0_lt) R
    · intro n _ r
      cases tl.ix.U.getD n none with
      | none => exact ⟨_, rfl⟩
      | some t =>
        by_cases hk : ((r.trees.getD t {}).kind == HKind.table) = true
        · simp only [hk, if_true]; exact ⟨_, rfl⟩
        · simp only [hk]; exact ⟨_, rfl⟩
    · intro n _ r hr
      cases tl.ix.U.getD n none with
      | none => exact hr
      | some t =>
        by_cases hk : ((r.trees.getD t {}).kind == HKind.table) = true
        · simp only [hk, if_true]; exact keepP _ _ _ _ hr
        · simp only [hk]; exact hr
    · intro n _ r hr hq
      cases tl.ix.U.getD n none with
      | none => exact hq
      | some t =>
        by_cases hk : ((r.trees.getD t {}).kind == HKind.table) = true
        · simp only [hk, if_true]
          by_cases ht : t = tU
          · subst ht; exact coefAt_same r t 0 _ hr.1
          · exact keepQ r t 0 _ ht hq
        · simp only [hk]; exact hq
    · intro r hr
      simp only [A.isU, hr.2, if_true]
      exact coefAt_same r tU 0 _ hr.1
  refine id_bind_inv (fun r => P r ∧ Q r) Q _ _ ?_ (fun r2 h2 => ?_)
  · refine forIn_id_mem (fun r => P r ∧ Q r) _ _ _ ?_ h1
    intro q _ r hr
    show (fun r => P r ∧ Q r) (forIn (tl.zOf q).pieces r _ : Id Fork)
    rw [← Array.forIn_toList]
    refine forIn_id_mem (fun r => P r ∧ Q r) _ _ _ ?_ hr
    intro p hp r' hr'
    exact ⟨keepP _ _ _ _ hr'.1, keepQ r' _ _ _ (A.uP q p hp) hr'.2⟩
  refine id_bind_inv (fun r => P r ∧ Q r) Q _ _ ?_ (fun r3 h3 => ?_)
  · refine forIn_id_mem (fun r => P r ∧ Q r) _ _ _ ?_
      ⟨keepP _ _ _ _ (keepP _ _ _ _ h2.1), keepQ _ _ _ _ A.uZZ (keepQ _ _ _ _ A.uZZ h2.2)⟩
    intro e _ r hr
    exact ⟨keepP _ _ _ _ hr.1, keepQ r _ _ _ A.uBZ hr.2⟩
  refine id_bind_inv (fun r => P r ∧ Q r) Q _ _ ?_ (fun r4 h4 => h4.2)
  refine forIn_id_mem (fun r => P r ∧ Q r) _ _ _ ?_ ⟨keepP _ _ _ _ h3.1, keepQ _ _ _ _ A.uBZ h3.2⟩
  intro mu hmu r hr
  exact ⟨keepP _ _ _ _ hr.1, keepQ r _ _ _ (A.uS mu (List.mem_range.1 hmu)) hr.2⟩

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.coefficientsF_inv
#print axioms OnBytes.Tie.Pv.Tail.Port.coefficientsF_rest
#print axioms OnBytes.Tie.Pv.Tail.Port.coefficientsF_shape
#print axioms OnBytes.Tie.Pv.Tail.Port.coefficientsF_unit
