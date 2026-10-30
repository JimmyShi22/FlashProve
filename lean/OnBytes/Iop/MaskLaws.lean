-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/MaskLaws.lean: what the batching of rows does to the coefficients on mask tables.

The laws of OnBytes/Iop/RowLaws.lean for a group's main table, stated for its mask table, which a
group's row holds written out (GroupRow.d).

Main definitions: MaskBlocksOk, MaskFits, maskWeight, maskBack, Row.maskSum.
Main theorems: addToGroupRow_mask, Row.maskSum_member, Row.maskSum_none, maskWeight_rows,
combine_mask_member, combine_mask_none.

What is not claimed. MaskBlocksOk, MaskFits and RowFits are assumed, and so is that an index is in
the block of one member or of none: no theorem of this file shows them for what the program makes. x
is any element: no theorem names the blocks that draw it. Every equation is between readings, not
between the program's words. Nothing on kept members' main rows (RowLaws.lean: combine_kept).
Nothing on soundness. The program does not import this file.
-/
import OnBytes.Iop.RowLaws
import OnBytes.Iop.SpreadLaws

namespace OnBytes

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- 1 if o is a member with mask rows and the index J has the number of o's block at its bits
a .. h - 1 (a: o's row bits); else 0. For a block that is aligned and inside the table this means
that J's row is in the block (maskWeight_rows). -/
def maskWeight (S : Statement) (L : GroupLayout) (o J : Nat) : K :=
  match L.find o with
  | none => 0
  | some i =>
    match L.maskFirst.getD i none with
    | none => 0
    | some first =>
      if J / 2 ^ S.rowBits o .mask % 2 ^ (L.h - S.rowBits o .mask) =
          first / 2 ^ S.rowBits o .mask % 2 ^ (L.h - S.rowBits o .mask) then 1 else 0

/-- The index in o's mask table that belongs to the index J of the group's mask table, if J's row
is in o's block. -/
def maskBack (S : Statement) (L : GroupLayout) (o J : Nat) : Nat :=
  unshift (S.rowBits o .mask) (L.h - S.rowBits o .mask) J

/-- The blocks of the members' mask rows are aligned and are in the group's table. -/
def MaskBlocksOk (S : Statement) (L : GroupLayout) : Prop :=
  ∀ o i first, L.find o = some i → L.maskFirst.getD i none = some first →
    BlockOk (S.rowBits o .mask) first L.h

/-- A structured vector on a mask table covers all places of the group's table: it has at least as
many variables as its table's row bits and the group's place bits together. -/
def MaskFits (S : Statement) (L : GroupLayout) (row : Row) : Prop :=
  ∀ t ∈ row.terms.toList, t.part = .mask → S.rowBits t.oracle .mask + L.logEllZk ≤ t.v.vars

/-- Putting count variables in at a place pos ≤ v.vars raises the number of variables by count. -/
theorem Tensor.vars_insertChoice (v : Tensor) (pos count value : Nat) (h : pos ≤ v.vars) :
    (v.insertChoice pos count value).vars = v.vars + count := by
  unfold Tensor.vars at h ⊢
  unfold Tensor.insertChoice
  simp only [List.length_append, List.length_take, List.length_drop, choicePairs_length]
  omega

/-- What a structured vector adds at the index J of the group's mask table. -/
theorem addTermTo_mask (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (hv : S.rowBits t.oracle t.part ≤ t.v.vars)
    (hm : t.part = .mask → S.rowBits t.oracle .mask + L.logEllZk ≤ t.v.vars)
    (h : addTermTo S L x acc t = some acc') (J : Nat) (hJ : J < 2 ^ (L.h + L.logEllZk))
    (hs : acc.d.size = 2 ^ (L.h + L.logEllZk)) :
    acc'.d.size = 2 ^ (L.h + L.logEllZk) ∧
    ρ.val (acc'.d.getD J zeroE) = ρ.val (acc.d.getD J zeroE) +
      (if t.part = .mask then
        maskWeight (K := K) S L t.oracle J * ρ.val (t.v.entry (maskBack S L t.oracle J)) * ρ.val x
      else 0) := by
  unfold addTermTo at h
  unfold maskWeight maskBack
  cases hf : L.find t.oracle with
  | none => simp [hf] at h
  | some i =>
    simp only [hf] at h
    cases hp : t.part with
    | main =>
      simp only [hp] at h
      by_cases hk : L.kept.getD i false = true
      · simp only [hk, if_true, Option.some.injEq] at h
        subst h
        exact ⟨hs, by simp⟩
      · simp only [hk, Bool.false_eq_true, if_false] at h
        cases hq : L.mainFirst.getD i none with
        | none => simp [hq] at h
        | some first =>
          simp only [hq] at h
          split at h
          · cases h
          · cases h
            exact ⟨hs, by simp⟩
    | mask =>
      simp only [hp] at h hv
      have hm' := hm hp
      cases hq : L.maskFirst.getD i none with
      | none => simp [hq] at h
      | some first =>
        simp only [hq] at h
        split at h
        · cases h
        · rename_i hlt
          cases h
          have hv' : S.rowBits t.oracle .mask ≤ (t.v.scale x).vars := by
            rw [Tensor.vars_scale]
            exact hv
          have hJ2 : J < 2 ^ ((t.v.scale x).insertChoice (S.rowBits t.oracle .mask)
              (L.h - S.rowBits t.oracle .mask) (first / 2 ^ S.rowBits t.oracle .mask)).vars := by
            rw [Tensor.vars_insertChoice _ _ _ _ hv', Tensor.vars_scale]
            exact Nat.lt_of_lt_of_le hJ (Nat.pow_le_pow_right (by decide) (by omega))
          refine ⟨by rw [Tensor.addTo_size]; exact hs, ?_⟩
          rw [Tensor.addTo_val, if_pos ⟨hJ2, by rw [hs]; exact hJ⟩,
            Tensor.entry_insertChoice ρ _ _ _ _ _ hv', Tensor.entry_scale]
          simp only [if_true, hq]
          ring

/-- What a coefficient on a single entry adds at the index J of the group's mask table. -/
theorem addEntryTo_mask (S : Statement) (L : GroupLayout) (hL : MaskBlocksOk S L) (x : E)
    (acc acc' : GroupRow) (o : Nat) (part : Part) (index : Nat) (coeff : E)
    (h : addEntryTo S L x acc o part index coeff = some acc') (J : Nat)
    (hJ : J < 2 ^ (L.h + L.logEllZk)) (hs : acc.d.size = 2 ^ (L.h + L.logEllZk)) :
    acc'.d.size = 2 ^ (L.h + L.logEllZk) ∧
    ρ.val (acc'.d.getD J zeroE) = ρ.val (acc.d.getD J zeroE) +
      (if part = .mask then
        maskWeight (K := K) S L o J * (if index = maskBack S L o J then ρ.val coeff else 0) *
          ρ.val x
      else 0) := by
  unfold addEntryTo at h
  unfold maskWeight maskBack
  cases hf : L.find o with
  | none => simp [hf] at h
  | some i =>
    simp only [hf] at h
    cases part with
    | main =>
      simp only at h
      by_cases hk : L.kept.getD i false = true
      · simp only [hk, if_true, Option.some.injEq] at h
        subst h
        exact ⟨hs, by simp⟩
      · simp only [hk, Bool.false_eq_true, if_false] at h
        cases hq : L.mainFirst.getD i none with
        | none => simp [hq] at h
        | some first =>
          simp only [hq, Option.some.injEq] at h
          subst h
          exact ⟨hs, by simp⟩
    | mask =>
      simp only at h
      cases hq : L.maskFirst.getD i none with
      | none => simp [hq] at h
      | some first =>
        simp only [hq] at h
        split at h
        · cases h
          have hb := hL o i first hf hq
          have hx := shiftIn_eq_iff (S.rowBits o .mask) (L.h - S.rowBits o .mask)
            (first / 2 ^ S.rowBits o .mask) index J
          rw [← groupIndex_eq_shiftIn _ _ _ _ hb] at hx
          refine ⟨by simpa using hs, ?_⟩
          simp only [getD_modify, if_true, hq]
          have hJs : J < acc.d.size := by rw [hs]; exact hJ
          by_cases h1 : J / 2 ^ S.rowBits o .mask % 2 ^ (L.h - S.rowBits o .mask) =
              first / 2 ^ S.rowBits o .mask % 2 ^ (L.h - S.rowBits o .mask)
          · by_cases h2 : unshift (S.rowBits o .mask) (L.h - S.rowBits o .mask) J = index
            · rw [if_pos ⟨hx.2 ⟨h1, h2⟩, hJs⟩, if_pos h1, if_pos h2.symm, maddE_val]
              ring
            · have h3 : ¬ index = unshift (S.rowBits o .mask) (L.h - S.rowBits o .mask) J :=
                fun e => h2 e.symm
              have h4 : ¬ (groupIndex index (S.rowBits o .mask) first L.h = J ∧ J < acc.d.size) :=
                fun e => h2 (hx.1 e.1).2
              rw [if_neg h4, if_neg h3]
              ring
          · have h4 : ¬ (groupIndex index (S.rowBits o .mask) first L.h = J ∧ J < acc.d.size) :=
              fun e => h1 (hx.1 e.1).1
            rw [if_neg h4, if_neg h1]
            ring
        · cases h

/-- A whole coefficient vector is on a main table: it leaves the mask table as it was. -/
theorem addFormTo_mask (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (h : addFormTo S L x acc f = some acc') : acc'.d = acc.d := by
  unfold addFormTo at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h
    | (dsimp only at h; split at h <;> first | (cases h; rfl) | cases h)

/-- If each step of a fold keeps a condition and, under it, adds its effect to a measure R of the
state, the fold keeps the condition and adds the sum of the effects. -/
theorem foldlM_effect_inv {α β M : Type} [AddCommMonoid M] (P : β → Prop) (R : β → M)
    (step : β → α → Option β) (eff : α → M) : ∀ (l : List α),
    (∀ a ∈ l, ∀ b b', P b → step b a = some b' → P b' ∧ R b' = R b + eff a) →
    ∀ (b b' : β), P b → l.foldlM step b = some b' → P b' ∧ R b' = R b + (l.map eff).sum
  | [], _, b, b', hp, h => by
    have e : b = b' := by simpa using h
    subst e
    exact ⟨hp, by simp⟩
  | a :: l, hs, b, b', hp, h => by
    rw [List.foldlM_cons] at h
    cases h1 : step b a with
    | none => simp [h1] at h
    | some b1 =>
      simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨p1, e1⟩ := hs a (List.mem_cons_self) b b1 hp h1
      obtain ⟨p2, e2⟩ := foldlM_effect_inv P R step eff l
        (fun a' ha' => hs a' (List.mem_cons_of_mem _ ha')) b1 b' p1 h
      exact ⟨p2, by rw [e2, e1, List.map_cons, List.sum_cons, add_assoc]⟩

/-- What a run of coefficients adds at the index J of the group's mask table. -/
theorem addRunTo_mask (S : Statement) (L : GroupLayout) (hL : MaskBlocksOk S L) (x : E)
    (acc acc' : GroupRow) (w : Run) (hw : 0 < w.step) (h : addRunTo S L x acc w = some acc')
    (J : Nat) (hJ : J < 2 ^ (L.h + L.logEllZk)) (hs : acc.d.size = 2 ^ (L.h + L.logEllZk)) :
    acc'.d.size = 2 ^ (L.h + L.logEllZk) ∧
    ρ.val (acc'.d.getD J zeroE) = ρ.val (acc.d.getD J zeroE) +
      (if w.part = .mask then
        maskWeight (K := K) S L w.oracle J * w.val ρ (maskBack S L w.oracle J) * ρ.val x
      else 0) := by
  unfold addRunTo at h
  obtain ⟨p, e⟩ := foldlM_effect_inv (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
    (fun g : GroupRow => ρ.val (g.d.getD J zeroE)) _
    (fun j => if w.part = .mask then
        maskWeight (K := K) S L w.oracle J *
          (if w.first + w.step * j = maskBack S L w.oracle J then ρ.val (w.coeffs.get j) else 0) *
          ρ.val x
      else 0) (List.range w.coeffs.size)
    (fun j _ b b' hb hh => addEntryTo_mask ρ S L hL x b b' _ _ _ _ hh J hJ hb) acc acc' hs h
  refine ⟨p, ?_⟩
  rw [e]
  congr 1
  by_cases hp : w.part = .mask
  · simp only [hp, if_true]
    rw [← Run.sum_val ρ w hw, List.sum_map_mul_right, List.sum_map_mul_left]
  · simp [hp]

/-- What x times a row adds at the index J of the group's mask table. -/
def Row.maskSum (S : Statement) (L : GroupLayout) (x : E) (row : Row) (J : Nat) : K :=
  (row.terms.toList.map fun t =>
    if t.part = .mask then
      maskWeight (K := K) S L t.oracle J * ρ.val (t.v.entry (maskBack S L t.oracle J)) * ρ.val x
    else 0).sum +
  (row.units.toList.map fun u =>
    if u.part = .mask then
      maskWeight (K := K) S L u.oracle J *
        (if u.index = maskBack S L u.oracle J then ρ.val u.coeff else 0) * ρ.val x
    else 0).sum +
  (row.runs.toList.map fun w =>
    if w.part = .mask then
      maskWeight (K := K) S L w.oracle J * w.val ρ (maskBack S L w.oracle J) * ρ.val x
    else 0).sum

/-- The mask table of a group's row is not yet written out, or has its full length. -/
def MaskReady (L : GroupLayout) (g : GroupRow) : Prop :=
  g.d = #[] ∨ g.d.size = 2 ^ (L.h + L.logEllZk)

/-- Writing out the mask table: it has its full length, and every entry reads as before. -/
theorem GroupRow.ready_d (acc : GroupRow) (L : GroupLayout) (h : MaskReady L acc) (J : Nat) :
    (acc.ready L).d.size = 2 ^ (L.h + L.logEllZk) ∧
      ρ.val ((acc.ready L).d.getD J zeroE) = ρ.val (acc.d.getD J zeroE) := by
  unfold GroupRow.ready
  rcases h with h | h
  · simp only [h, Array.isEmpty_empty, if_true, Array.size_replicate, true_and]
    by_cases hj : J < 2 ^ (L.h + L.logEllZk) <;> simp [Array.getD, hj]
  · by_cases he : acc.d.isEmpty = true
    · simp only [he, if_true, Array.size_replicate, true_and]
      have h0 : acc.d = #[] := by simpa using he
      by_cases hj : J < 2 ^ (L.h + L.logEllZk) <;> simp [Array.getD, hj, h0]
    · simp only [he, Bool.false_eq_true, if_false]
      exact ⟨h, trivial⟩

/-- x times a row, carried to a group's row: what is added at the index J of the mask table. -/
theorem addToGroupRow_mask (S : Statement) (L : GroupLayout) (hL : MaskBlocksOk S L) (row : Row)
    (hr : RowFits S row) (hm : MaskFits S L row) (x : E) (acc acc' : GroupRow)
    (hp : MaskReady L acc) (h : addToGroupRow S L row x acc = some acc') (J : Nat)
    (hJ : J < 2 ^ (L.h + L.logEllZk)) :
    MaskReady L acc' ∧
      ρ.val (acc'.d.getD J zeroE) = ρ.val (acc.d.getD J zeroE) + row.maskSum ρ S L x J := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := h
  obtain ⟨p0, e0⟩ := GroupRow.ready_d ρ acc L hp J
  obtain ⟨p1, e1⟩ := foldlM_effect_inv (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
    (fun g : GroupRow => ρ.val (g.d.getD J zeroE)) _ _ row.terms.toList
    (fun t ht b b' hb hh => addTermTo_mask ρ S L x b b' t (hr.terms t ht) (hm t ht) hh J hJ hb)
    _ _ p0 h1
  obtain ⟨p2, e2⟩ := foldlM_effect_inv (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
    (fun g : GroupRow => ρ.val (g.d.getD J zeroE))
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff) _
    row.units.toList
    (fun u _ b b' hb hh =>
      addEntryTo_mask ρ S L hL x b b' u.oracle u.part u.index u.coeff hh J hJ hb)
    _ _ p1 h2
  obtain ⟨p3, e3⟩ := foldlM_effect_inv (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
    (fun g : GroupRow => ρ.val (g.d.getD J zeroE)) _ _ row.runs.toList
    (fun w hw b b' hb hh => addRunTo_mask ρ S L hL x b b' w (hr.runs w hw) hh J hJ hb)
    _ _ p2 h3
  have e4 := foldlM_keeps (fun g : GroupRow => g.d) _
    (fun f b b' hb => addFormTo_mask S L x b b' f hb) _ _ _ h4
  dsimp only at e1 e2 e3 e4
  refine ⟨Or.inr (by rw [e4]; exact p3), ?_⟩
  unfold Row.maskSum
  rw [e4, e3, e2, e1, e0]
  ring

/-- At an index where the weight (maskWeight) of the member o is 1 and that of every other oracle
message is 0, x times a row adds x times the row's coefficient on the entry of o that belongs to the
index. -/
theorem Row.maskSum_member (S : Statement) (L : GroupLayout) (x : E) (row : Row) (o J : Nat)
    (h1 : maskWeight (K := K) S L o J = 1) (h0 : ∀ o', o' ≠ o → maskWeight (K := K) S L o' J = 0) :
    row.maskSum ρ S L x J = ρ.val (row.coefficient o .mask (maskBack S L o J)) * ρ.val x := by
  unfold Row.maskSum
  rw [Row.coefficient_val, add_mul, add_mul, add_mul, ← List.sum_map_mul_right,
    ← List.sum_map_mul_right, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
  have hz : (row.forms.toList.map fun f : MainForm =>
      (if f.oracle = o ∧ Part.mask = Part.main then
        ρ.val (f.c.entry (maskBack S L o J)) else 0) * ρ.val x).sum = 0 := by
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨f, _, rfl⟩ := List.mem_map.1 ha
    simp
  rw [hz, add_zero]
  congr 1
  · congr 1
    · congr 1
      apply List.map_congr_left
      intro t _
      by_cases e : t.oracle = o
      · by_cases p : t.part = .mask <;> simp [e, p, h1]
      · by_cases p : t.part = .mask <;> simp [e, p, h0 _ e]
    · congr 1
      apply List.map_congr_left
      intro t _
      by_cases e : t.oracle = o
      · by_cases p : t.part = .mask <;> simp [e, p, h1]
      · by_cases p : t.part = .mask <;> simp [e, p, h0 _ e]
  · congr 1
    apply List.map_congr_left
    intro t _
    by_cases e : t.oracle = o
    · by_cases p : t.part = .mask <;> simp [e, p, h1]
    · by_cases p : t.part = .mask <;> simp [e, p, h0 _ e]

/-- At an index where every weight (maskWeight) is 0 a row adds nothing. -/
theorem Row.maskSum_none (S : Statement) (L : GroupLayout) (x : E) (row : Row) (J : Nat)
    (h0 : ∀ o, maskWeight (K := K) S L o J = 0) : row.maskSum ρ S L x J = 0 := by
  unfold Row.maskSum
  simp [h0]

/-- For a member with mask rows whose block is aligned and inside the table (BlockOk), the weight is
1 at the indices whose row is in the block and 0 at the others. -/
theorem maskWeight_rows (S : Statement) (L : GroupLayout) (o i first J : Nat)
    (hf : L.find o = some i) (hm : L.maskFirst.getD i none = some first)
    (hb : BlockOk (S.rowBits o .mask) first L.h) :
    maskWeight (K := K) S L o J =
      if first ≤ J % 2 ^ L.h ∧ J % 2 ^ L.h < first + 2 ^ S.rowBits o .mask then 1 else 0 := by
  unfold maskWeight
  simp only [hf, hm, inBlock_iff J _ first L.h hb]

/-- If Bat.combine returns a row, the layout meets MaskBlocksOk and every row meets RowFits and
MaskFits: at an index J of the mask table (J < 2^(h + logEllZk)) whose row is in the block of the
member o and of no other oracle message, the batched row's coefficient reads as the sum of x^i times
the coefficient of row number i (from 0) on the entry of o that belongs to the index. -/
theorem combine_mask_member (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MaskBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r ∧ MaskFits S input.layout r) (o J : Nat)
    (hJ : J < 2 ^ (input.layout.h + input.layout.logEllZk))
    (h1 : maskWeight (K := K) S input.layout o J = 1)
    (h0 : ∀ o', o' ≠ o → maskWeight (K := K) S input.layout o' J = 0) :
    ρ.val (out.d.getD J zeroE) = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      ρ.val (r.coefficient o .mask (maskBack S input.layout o J))) :=
  combine_read ρ S g input x out h (fun r => RowFits S r ∧ MaskFits S input.layout r)
    (fun _ a => a.1) (fun _ a => ⟨a.1.structured, a.2⟩)
    (fun _ a => ⟨a.fits, by intro t ht; simp [a.terms] at ht⟩) hr
    (MaskReady input.layout) (fun a => ρ.val (a.d.getD J zeroE))
    (fun r => ρ.val (r.coefficient o .mask (maskBack S input.layout o J)))
    (fun row y acc acc' hf hp ha => by
      obtain ⟨p, e⟩ := addToGroupRow_mask ρ S _ hL row hf.1 hf.2 y acc acc' hp ha J hJ
      refine ⟨p, ?_⟩
      dsimp only
      rw [e, Row.maskSum_member ρ S _ y row o J h1 h0])
    (fun r other y => Row.coefficient_addScaled ρ r other y _ _ _)
    (fun r => Row.coefficient_split ρ r _ _ _)
    (Or.inl rfl) (by simp [Array.getD, ρ.zero]) (by simp [Row.coefficient_val])

/-- If Bat.combine returns a row, the layout meets MaskBlocksOk and every row meets RowFits and
MaskFits: at an index J of the mask table (J < 2^(h + logEllZk)) whose row is in no member's block
the batched row's coefficient reads as 0. -/
theorem combine_mask_none (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MaskBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r ∧ MaskFits S input.layout r) (J : Nat)
    (hJ : J < 2 ^ (input.layout.h + input.layout.logEllZk))
    (h0 : ∀ o, maskWeight (K := K) S input.layout o J = 0) :
    ρ.val (out.d.getD J zeroE) = 0 := by
  have e := combine_read ρ S g input x out h (fun r => RowFits S r ∧ MaskFits S input.layout r)
    (fun _ a => a.1) (fun _ a => ⟨a.1.structured, a.2⟩)
    (fun _ a => ⟨a.fits, by intro t ht; simp [a.terms] at ht⟩) hr
    (MaskReady input.layout) (fun a => ρ.val (a.d.getD J zeroE)) (fun _ => 0)
    (fun row y acc acc' hf hp ha => by
      obtain ⟨p, e⟩ := addToGroupRow_mask ρ S _ hL row hf.1 hf.2 y acc acc' hp ha J hJ
      refine ⟨p, ?_⟩
      dsimp only
      rw [e, Row.maskSum_none ρ S _ y row J h0]
      simp)
    (fun _ _ _ => by simp) (fun _ => by simp) (Or.inl rfl) (by simp [Array.getD, ρ.zero]) rfl
  dsimp only at e
  rw [e]
  exact hornerSum_zero _ _ (by simp)

end OnBytes

#print axioms OnBytes.combine_mask_member
#print axioms OnBytes.combine_mask_none
#print axioms OnBytes.maskWeight_rows
