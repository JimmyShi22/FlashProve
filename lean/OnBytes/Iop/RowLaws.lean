-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/RowLaws.lean: what the batching of rows does to coefficients, entry by entry.

A row of the statement has a coefficient on each entry of each table of each oracle message
(Row.coefficient). A group puts its members' tables into two tables of its own. (A member may be
kept: its main table then stays apart; see GroupLayout in OnBytes/Iop/Ground.lean. The other
members' main rows are folded.) The laws say where an entry of a member goes, that no two entries of
one member go to one index, nor entries of two members whose blocks have no row in common, and what
the coefficients of a batched row read as in any commutative ring under a reading of the program's
field elements (Model.Reading, see OnBytes/Iop/TensorLaws.lean). BAT and BAT-sigma are the two forms
of the batching (OnBytes/Iop/Bat.lean).

Main definitions: BlockOk, MainBlocksOk, RowFits, mainWeight, mainBack, Row.mainSum, Run.val,
hornerSum, keptSum, keptWeight.
Main theorems. Where an entry goes: groupIndex_closed, groupIndex_row, groupIndex_place,
groupIndex_inj, groupIndex_ne, groupIndex_eq_shiftIn, unshift_groupIndex, inBlock_iff. A row's
coefficient: Row.coefficient_val, Row.coefficient_addScaled, Row.coefficient_split. One row carried
to a group: addToGroupRow_main, Row.mainSum_member, Row.mainSum_none, mainWeight_rows. BAT-sigma:
combineRows_coefficient, combineRows_target. BAT on a group, the main table:
combine_main_member, combine_main_none; the target: combine_target; a kept member: combine_kept.

What is not claimed. The conditions on a layout and on rows are assumed: MainBlocksOk, RowFits, and
that the row of an index is in the block of one member only (d in groupIndex_ne; h1 and h0 in
combine_main_member). No theorem of this file shows them for what the program makes. Every law on
addToGroupRow and on Bat.combine has the form "if the call returns a row, then": nothing is said on
when it returns one. The element x of a batching is any element: no theorem names the blocks that
draw it (batVerify, csVerify, batSigmaVerify). Every equation is between values in K. A reading need
not be one-to-one, so nothing follows on the machine words of the program's elements. A group's mask
table is in OnBytes/Iop/MaskLaws.lean. Nothing on soundness. The program does not import this file.
-/
import OnBytes.Iop.TensorLaws
import OnBytes.Iop.Bat

namespace OnBytes

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## Where an entry of a member goes -/

/-- The block of 2^a rows that begins at the row number first is aligned and is within a table of
2^k rows. -/
structure BlockOk (a first k : Nat) : Prop where
  aligned : first % 2 ^ a = 0
  inside : first + 2 ^ a ≤ 2 ^ k

/-- A block that is in the table has at most the table's number of row bits. -/
theorem BlockOk.le {a first k : Nat} (h : BlockOk a first k) : a ≤ k := by
  have h1 : 2 ^ a ≤ 2 ^ k := Nat.le_trans (Nat.le_add_left _ _) h.inside
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 h1

/-- The closed form. Entry (row i, place p) of a member's table, which has the index i + 2^a p, goes
to (row first + i, place p) of the group's table, which has the index first + i + 2^k p. -/
theorem groupIndex_closed (i p a first k : Nat) (hi : i < 2 ^ a) :
    groupIndex (i + 2 ^ a * p) a first k = first + i + 2 ^ k * p := by
  unfold groupIndex
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hi, Nat.zero_add, Nat.mul_comm]

/-- The row of the group's table to which an entry goes. -/
theorem groupIndex_row (idx a first k : Nat) (h : BlockOk a first k) :
    groupIndex idx a first k % 2 ^ k = first + idx % 2 ^ a := by
  unfold groupIndex
  rw [Nat.add_mul_mod_self_right]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt idx (Nat.two_pow_pos a)
  have := h.inside
  omega

/-- The place is kept. -/
theorem groupIndex_place (idx a first k : Nat) (h : BlockOk a first k) :
    groupIndex idx a first k / 2 ^ k = idx / 2 ^ a := by
  unfold groupIndex
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
  have h1 : (first + idx % 2 ^ a) / 2 ^ k = 0 := by
    apply Nat.div_eq_of_lt
    have := Nat.mod_lt idx (Nat.two_pow_pos a)
    have := h.inside
    omega
  rw [h1, Nat.zero_add]

/-- For a block that meets BlockOk: no two entries of one member go to one index. -/
theorem groupIndex_inj (idx idx' a first k : Nat) (h : BlockOk a first k)
    (e : groupIndex idx a first k = groupIndex idx' a first k) : idx = idx' := by
  have r := congrArg (· % 2 ^ k) e
  have p := congrArg (· / 2 ^ k) e
  simp only [groupIndex_row _ _ _ _ h, groupIndex_place _ _ _ _ h] at r p
  have a1 := Nat.mod_add_div idx (2 ^ a)
  have a2 := Nat.mod_add_div idx' (2 ^ a)
  have r' : idx % 2 ^ a = idx' % 2 ^ a := by omega
  rw [← a1, ← a2, r', p]

/-- Entries of two members whose blocks both meet BlockOk and have no row in common go to different
indices. -/
theorem groupIndex_ne (idx idx' a a' first first' k : Nat) (h : BlockOk a first k)
    (h' : BlockOk a' first' k) (d : first + 2 ^ a ≤ first' ∨ first' + 2 ^ a' ≤ first) :
    groupIndex idx a first k ≠ groupIndex idx' a' first' k := by
  intro e
  have r := congrArg (· % 2 ^ k) e
  simp only [groupIndex_row _ _ _ _ h, groupIndex_row _ _ _ _ h'] at r
  have := Nat.mod_lt idx (Nat.two_pow_pos a)
  have := Nat.mod_lt idx' (Nat.two_pow_pos a')
  omega

/-- The block's number first / 2^a is below 2^(k - a), and first is that number times 2^a. -/
theorem block_number (a first k : Nat) (h : BlockOk a first k) :
    first / 2 ^ a % 2 ^ (k - a) = first / 2 ^ a ∧ first / 2 ^ a * 2 ^ a = first := by
  have hk := h.le
  have h2 : first / 2 ^ a * 2 ^ a = first := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.aligned)
  refine ⟨?_, h2⟩
  apply Nat.mod_eq_of_lt
  have h3 : 2 ^ k = 2 ^ (k - a) * 2 ^ a := by rw [← Nat.pow_add, Nat.sub_add_cancel hk]
  have h4 : first < 2 ^ (k - a) * 2 ^ a := by
    have := h.inside
    have := Nat.two_pow_pos a
    omega
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h4)

/-- For a block that meets BlockOk: the index of an entry in the group's table is its own index with
the block's number put in between the row's bits and the place's bits. -/
theorem groupIndex_eq_shiftIn (idx a first k : Nat) (h : BlockOk a first k) :
    groupIndex idx a first k = shiftIn a (k - a) (first / 2 ^ a) idx := by
  obtain ⟨h1, h2⟩ := block_number a first k h
  unfold groupIndex shiftIn
  rw [h1, h2, Nat.add_sub_cancel' h.le]
  omega

/-- For a block that meets BlockOk: taking the block's number out of an entry's index in the group's
table gives back the entry's own index. -/
theorem unshift_groupIndex (idx a first k : Nat) (h : BlockOk a first k) :
    unshift a (k - a) (groupIndex idx a first k) = idx := by
  rw [groupIndex_eq_shiftIn _ _ _ _ h, unshift_shiftIn]

/-- For a block that meets BlockOk: an index J of the group's table has the block's number at its
bits a, .., k - 1 exactly if its row is in the block. -/
theorem inBlock_iff (J a first k : Nat) (h : BlockOk a first k) :
    J / 2 ^ a % 2 ^ (k - a) = first / 2 ^ a % 2 ^ (k - a) ↔
      first ≤ J % 2 ^ k ∧ J % 2 ^ k < first + 2 ^ a := by
  obtain ⟨h1, h2⟩ := block_number a first k h
  have h3 : 2 ^ k = 2 ^ a * 2 ^ (k - a) := by rw [← Nat.pow_add, Nat.add_sub_cancel' h.le]
  have h4 : J % 2 ^ k / 2 ^ a = J / 2 ^ a % 2 ^ (k - a) := by
    rw [h3, Nat.mod_mul_right_div_self]
  rw [h1, ← h4]
  have hp := Nat.two_pow_pos a
  constructor
  · intro e
    have a1 := Nat.mod_add_div (J % 2 ^ k) (2 ^ a)
    have a2 := Nat.mod_lt (J % 2 ^ k) hp
    rw [e, Nat.mul_comm, h2] at a1
    omega
  · rintro ⟨l, u⟩
    have l' : first / 2 ^ a ≤ J % 2 ^ k / 2 ^ a := Nat.div_le_div_right l
    have u' : J % 2 ^ k / 2 ^ a < first / 2 ^ a + 1 := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_add, Nat.mul_comm, h2]
      omega
    omega

/-! ## A fold that may fail, and what it adds up -/

/-- If each step of a fold adds its effect to a reading, the fold adds the sum of the effects. -/
theorem foldlM_effect {α β M : Type} [AddCommMonoid M] (R : β → M) (step : β → α → Option β)
    (eff : α → M) : ∀ (l : List α),
    (∀ a ∈ l, ∀ b b', step b a = some b' → R b' = R b + eff a) →
    ∀ (b b' : β), l.foldlM step b = some b' → R b' = R b + (l.map eff).sum
  | [], _, b, b', h => by
    have e : b = b' := by simpa using h
    simp [e]
  | a :: l, hs, b, b', h => by
    rw [List.foldlM_cons] at h
    cases h1 : step b a with
    | none => simp [h1] at h
    | some b1 =>
      simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
      have e1 := hs a (List.mem_cons_self) b b1 h1
      have e2 := foldlM_effect R step eff l (fun a' ha' => hs a' (List.mem_cons_of_mem _ ha'))
        b1 b' h
      rw [e2, e1, List.map_cons, List.sum_cons, add_assoc]

/-- A multiple of a tensor has the same variables. -/
theorem Tensor.vars_scale (v : Tensor) (x : E) : (v.scale x).vars = v.vars := by
  unfold Tensor.vars Tensor.scale
  rfl

/-! ## The main table of a group's row -/

/-- 1 if o is a member whose main rows are folded (it is not kept and has a block) and the index J
has the block's number at its bits a, .., k - 1; else 0. For a block that meets BlockOk this means
that J's row is in the block (mainWeight_rows). -/
def mainWeight (S : Statement) (L : GroupLayout) (o J : Nat) : K :=
  match L.find o with
  | none => 0
  | some i =>
    if L.kept.getD i false then 0
    else
      match L.mainFirst.getD i none with
      | none => 0
      | some first =>
        if J / 2 ^ S.rowBits o .main % 2 ^ (L.k - S.rowBits o .main) =
            first / 2 ^ S.rowBits o .main % 2 ^ (L.k - S.rowBits o .main) then 1 else 0

/-- The index in o's main table that belongs to the index J of the group's main table, if J's row
is in o's block. -/
def mainBack (S : Statement) (L : GroupLayout) (o J : Nat) : Nat :=
  unshift (S.rowBits o .main) (L.k - S.rowBits o .main) J

/-- What a structured vector adds at the index J of the group's main table. -/
theorem addTermTo_main (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (hv : S.rowBits t.oracle t.part ≤ t.v.vars) (h : addTermTo S L x acc t = some acc') (J : Nat) :
    ρ.val (acc'.c.entry J) = ρ.val (acc.c.entry J) +
      (if t.part = .main then
        mainWeight (K := K) S L t.oracle J * ρ.val (t.v.entry (mainBack S L t.oracle J)) * ρ.val x
      else 0) := by
  unfold addTermTo at h
  unfold mainWeight mainBack
  cases hf : L.find t.oracle with
  | none => simp [hf] at h
  | some i =>
    simp only [hf] at h
    cases hp : t.part with
    | mask =>
      simp only [hp] at h
      cases hm : L.maskFirst.getD i none with
      | none => simp [hm] at h
      | some first =>
        simp only [hm] at h
        split at h
        · cases h
        · cases h
          simp
    | main =>
      simp only [hp] at h hv
      by_cases hk : L.kept.getD i false = true
      · simp only [hk, if_true, Option.some.injEq] at h
        subst h
        simp [hk]
      · simp only [hk, Bool.false_eq_true, if_false] at h
        cases hm : L.mainFirst.getD i none with
        | none => simp [hm] at h
        | some first =>
          simp only [hm] at h
          split at h
          · cases h
          · cases h
            have hv' : S.rowBits t.oracle .main ≤ (t.v.scale x).vars := by
              rw [Tensor.vars_scale]
              exact hv
            simp only [Form.entry_add, Tensor.entry_insertChoice ρ _ _ _ _ _ hv',
              Tensor.entry_scale, hk, hm, Bool.false_eq_true, if_false, if_true]
            ring

/-- The blocks of the members' main rows are aligned and are in the group's table. -/
def MainBlocksOk (S : Statement) (L : GroupLayout) : Prop :=
  ∀ o i first, L.find o = some i → L.mainFirst.getD i none = some first →
    BlockOk (S.rowBits o .main) first L.k

/-- What a coefficient on a single entry adds at the index J of the group's main table. -/
theorem addEntryTo_main (S : Statement) (L : GroupLayout) (hL : MainBlocksOk S L) (x : E)
    (acc acc' : GroupRow) (o : Nat) (part : Part) (index : Nat) (coeff : E)
    (h : addEntryTo S L x acc o part index coeff = some acc') (J : Nat) :
    ρ.val (acc'.c.entry J) = ρ.val (acc.c.entry J) +
      (if part = .main then
        mainWeight (K := K) S L o J * (if index = mainBack S L o J then ρ.val coeff else 0) *
          ρ.val x
      else 0) := by
  unfold addEntryTo at h
  unfold mainWeight mainBack
  cases hf : L.find o with
  | none => simp [hf] at h
  | some i =>
    simp only [hf] at h
    cases part with
    | mask =>
      simp only at h
      cases hm : L.maskFirst.getD i none with
      | none => simp [hm] at h
      | some first =>
        simp only [hm] at h
        split at h
        · cases h
          simp
        · cases h
    | main =>
      simp only at h
      by_cases hk : L.kept.getD i false = true
      · simp only [hk, if_true, Option.some.injEq] at h
        subst h
        simp [hk]
      · simp only [hk, Bool.false_eq_true, if_false] at h
        cases hm : L.mainFirst.getD i none with
        | none => simp [hm] at h
        | some first =>
          simp only [hm, Option.some.injEq] at h
          subst h
          have hb := hL o i first hf hm
          have hs := shiftIn_eq_iff (S.rowBits o .main) (L.k - S.rowBits o .main)
            (first / 2 ^ S.rowBits o .main) index J
          rw [← groupIndex_eq_shiftIn _ _ _ _ hb] at hs
          simp only [Form.entry_addEntry, hk, hm, Bool.false_eq_true, if_false, if_true, ρ.mul]
          by_cases h1 : J / 2 ^ S.rowBits o .main % 2 ^ (L.k - S.rowBits o .main) =
              first / 2 ^ S.rowBits o .main % 2 ^ (L.k - S.rowBits o .main)
          · by_cases h2 : unshift (S.rowBits o .main) (L.k - S.rowBits o .main) J = index
            · rw [if_pos (hs.2 ⟨h1, h2⟩), if_pos h1, if_pos h2.symm]
              ring
            · have h3 : ¬ index = unshift (S.rowBits o .main) (L.k - S.rowBits o .main) J :=
                fun e => h2 e.symm
              have h4 : ¬ groupIndex index (S.rowBits o .main) first L.k = J :=
                fun e => h2 (hs.1 e).2
              rw [if_neg h4, if_neg h3]
              ring
          · have h4 : ¬ groupIndex index (S.rowBits o .main) first L.k = J :=
              fun e => h1 (hs.1 e).1
            rw [if_neg h4, if_neg h1]
            ring

/-- What a whole coefficient vector adds at the index J of the group's main table. -/
theorem addFormTo_main (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (hv : ∀ v ∈ f.c.tensors, S.rowBits f.oracle .main ≤ v.vars)
    (h : addFormTo S L x acc f = some acc') (J : Nat) :
    ρ.val (acc'.c.entry J) = ρ.val (acc.c.entry J) +
      mainWeight (K := K) S L f.oracle J * ρ.val (f.c.entry (mainBack S L f.oracle J)) *
        ρ.val x := by
  unfold addFormTo at h
  unfold mainWeight mainBack
  cases hf : L.find f.oracle with
  | none => simp [hf] at h
  | some i =>
    simp only [hf] at h
    by_cases hk : L.kept.getD i false = true
    · simp only [hk, if_true, Option.some.injEq] at h
      subst h
      simp [hk]
    · simp only [hk, Bool.false_eq_true, if_false] at h
      cases hm : L.mainFirst.getD i none with
      | none => simp [hm] at h
      | some first =>
        simp only [hm] at h
        split at h
        · cases h
        · cases h
          simp only [Form.entry_addForm, Form.entry_insertChoice ρ _ _ _ _ _ hv, hk, hm,
            Bool.false_eq_true, if_false]

/-! ## The coefficient of a row on an entry -/

/-- A sum over the members of a list that satisfy a condition, as a foldl adds it up. -/
theorem foldl_cond {α : Type} (l : List α) (cond : α → Bool) (val : α → E) (a : E) :
    ρ.val (l.foldl (fun s t => if cond t then addE s (val t) else s) a) =
      ρ.val a + (l.map fun t => if cond t then ρ.val (val t) else 0).sum := by
  induction l generalizing a with
  | nil => simp
  | cons t l ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    cases cond t
    · simp
    · simp only [if_true, ρ.add]
      ring

/-- What a run of coefficients reads as at an index of its table. -/
def Run.val (w : Run) (idx : Nat) : K :=
  if w.first ≤ idx ∧ 0 < w.step ∧ (idx - w.first) % w.step = 0 ∧
      (idx - w.first) / w.step < w.coeffs.size then
    ρ.val (w.coeffs.get ((idx - w.first) / w.step))
  else 0

/-- The coefficient of a row on an entry reads as the sum over the row's summands on that table. -/
theorem Row.coefficient_val (r : Row) (o : Nat) (part : Part) (idx : Nat) :
    ρ.val (r.coefficient o part idx) =
      (r.terms.toList.map fun t =>
        if t.oracle = o ∧ t.part = part then ρ.val (t.v.entry idx) else 0).sum +
      (r.units.toList.map fun u =>
        if u.oracle = o ∧ u.part = part then (if u.index = idx then ρ.val u.coeff else 0)
        else 0).sum +
      (r.runs.toList.map fun w =>
        if w.oracle = o ∧ w.part = part then w.val ρ idx else 0).sum +
      (r.forms.toList.map fun f =>
        if f.oracle = o ∧ part = .main then ρ.val (f.c.entry idx) else 0).sum := by
  unfold Row.coefficient
  simp only [← Array.foldl_toList, foldl_cond, ρ.zero, zero_add]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        apply List.map_congr_left
        intro t _
        by_cases h1 : t.oracle = o <;> by_cases h2 : t.part = part <;> simp [h1, h2]
      · congr 1
        apply List.map_congr_left
        intro u _
        by_cases h1 : u.oracle = o <;> by_cases h2 : u.part = part <;>
          by_cases h3 : u.index = idx <;> simp [h1, h2, h3]
    · congr 1
      apply List.map_congr_left
      intro w _
      unfold Run.val
      by_cases h1 : w.oracle = o <;> by_cases h2 : w.part = part <;>
        simp [h1, h2, and_assoc]
  · congr 1
    apply List.map_congr_left
    intro f _
    by_cases h1 : f.oracle = o <;> by_cases h2 : part = .main <;> simp [h1, h2]

/-! ## A run, entry by entry -/

/-- A sum over 0, .., n - 1 in which only the index j0 counts. -/
theorem sum_range_single (n j0 : Nat) (g : Nat → K) :
    ((List.range n).map fun j => if j = j0 then g j else 0).sum = if j0 < n then g j0 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases h1 : j0 < n
    · have h2 : n ≠ j0 := by omega
      have h3 : j0 < n + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : n = j0
      · subst h2
        simp
      · have h3 : ¬ j0 < n + 1 := by omega
        simp [h1, h2, h3]

/-- The entries of a run that fall on an index add up to what the run reads as there. -/
theorem Run.sum_val (w : Run) (hs : 0 < w.step) (idx : Nat) :
    ((List.range w.coeffs.size).map fun j =>
      if w.first + w.step * j = idx then ρ.val (w.coeffs.get j) else 0).sum = w.val ρ idx := by
  unfold Run.val
  by_cases h : w.first ≤ idx ∧ (idx - w.first) % w.step = 0
  · obtain ⟨h1, h2⟩ := h
    have e : ∀ j, (w.first + w.step * j = idx) ↔ j = (idx - w.first) / w.step := by
      intro j
      have d := Nat.mod_add_div (idx - w.first) w.step
      rw [h2, Nat.zero_add] at d
      constructor
      · intro e
        have e' : idx - w.first = w.step * j := by omega
        rw [e', Nat.mul_div_cancel_left _ hs]
      · intro e
        rw [e, d]
        omega
    simp only [e, sum_range_single, h1, hs, h2, true_and]
  · have e : ∀ j, ¬ (w.first + w.step * j = idx) := by
      intro j e
      apply h
      refine ⟨by omega, ?_⟩
      have e' : idx - w.first = w.step * j := by omega
      rw [e', Nat.mul_mod_right]
    have h' : ¬ (w.first ≤ idx ∧ 0 < w.step ∧ (idx - w.first) % w.step = 0 ∧
        (idx - w.first) / w.step < w.coeffs.size) := fun x => h ⟨x.1, x.2.2.1⟩
    simp [e, h']

/-- What a run of coefficients adds at the index J of the group's main table. -/
theorem addRunTo_main (S : Statement) (L : GroupLayout) (hL : MainBlocksOk S L) (x : E)
    (acc acc' : GroupRow) (w : Run) (hs : 0 < w.step) (h : addRunTo S L x acc w = some acc')
    (J : Nat) :
    ρ.val (acc'.c.entry J) = ρ.val (acc.c.entry J) +
      (if w.part = .main then
        mainWeight (K := K) S L w.oracle J * w.val ρ (mainBack S L w.oracle J) * ρ.val x
      else 0) := by
  unfold addRunTo at h
  have e := foldlM_effect (fun g : GroupRow => ρ.val (g.c.entry J)) _
    (fun j => if w.part = .main then
        mainWeight (K := K) S L w.oracle J *
          (if w.first + w.step * j = mainBack S L w.oracle J then ρ.val (w.coeffs.get j) else 0) *
          ρ.val x
      else 0) (List.range w.coeffs.size)
    (fun j _ b b' hb => addEntryTo_main ρ S L hL x b b' _ _ _ _ hb J) acc acc' h
  dsimp only at e
  rw [e]
  congr 1
  by_cases hp : w.part = .main
  · simp only [hp, if_true]
    rw [← Run.sum_val ρ w hs, List.sum_map_mul_right, List.sum_map_mul_left]
  · simp [hp]

/-! ## A whole row, carried to the group's main table -/

/-- The conditions on a row under which the laws hold: each tensor has at least as many variables as
its table has row bits, and each run has a step of at least 1. No theorem of this file shows them
for a row that the program makes. In a run on a view Blk.addRow tests more of each open row (as many
variables as the table has index bits): OnBytes/Slice/BlkStLaws.lean, rowFits_of_checked. Sample
rows do not go through Blk.addRow: for a row of Send.form see OnBytes/Slice/BlkSend.lean,
rowFits_form; Blk.sampledElsewhere copies such rows from another statement. -/
structure RowFits (S : Statement) (row : Row) : Prop where
  terms : ∀ t ∈ row.terms.toList, S.rowBits t.oracle t.part ≤ t.v.vars
  runs : ∀ w ∈ row.runs.toList, 0 < w.step
  forms : ∀ f ∈ row.forms.toList, ∀ v ∈ f.c.tensors, S.rowBits f.oracle .main ≤ v.vars

/-- What x times a row adds at the index J of the group's main table. Each summand of the row on a
main table adds x times what it reads as at the entry of its oracle message's main table that
belongs to J (mainBack), if that oracle message is a member that is not kept and J's row is in its
block (mainWeight), and else nothing. Summands on a mask table add nothing. -/
def Row.mainSum (S : Statement) (L : GroupLayout) (x : E) (row : Row) (J : Nat) : K :=
  (row.terms.toList.map fun t =>
    if t.part = .main then
      mainWeight (K := K) S L t.oracle J * ρ.val (t.v.entry (mainBack S L t.oracle J)) * ρ.val x
    else 0).sum +
  (row.units.toList.map fun u =>
    if u.part = .main then
      mainWeight (K := K) S L u.oracle J *
        (if u.index = mainBack S L u.oracle J then ρ.val u.coeff else 0) * ρ.val x
    else 0).sum +
  (row.runs.toList.map fun w =>
    if w.part = .main then
      mainWeight (K := K) S L w.oracle J * w.val ρ (mainBack S L w.oracle J) * ρ.val x
    else 0).sum +
  (row.forms.toList.map fun f =>
    mainWeight (K := K) S L f.oracle J * ρ.val (f.c.entry (mainBack S L f.oracle J)) * ρ.val x).sum

/-- Writing out the mask table leaves the main table as it was. -/
theorem GroupRow.ready_c (acc : GroupRow) (L : GroupLayout) : (acc.ready L).c = acc.c := by
  unfold GroupRow.ready
  split <;> rfl

/-- x times a row, carried to a group's row: what is added at the index J of the main table. -/
theorem addToGroupRow_main (S : Statement) (L : GroupLayout) (hL : MainBlocksOk S L) (row : Row)
    (hr : RowFits S row) (x : E) (acc acc' : GroupRow)
    (h : addToGroupRow S L row x acc = some acc') (J : Nat) :
    ρ.val (acc'.c.entry J) = ρ.val (acc.c.entry J) + row.mainSum ρ S L x J := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := h
  have e1 := foldlM_effect (fun g : GroupRow => ρ.val (g.c.entry J)) _ _ row.terms.toList
    (fun t ht b b' hb => addTermTo_main ρ S L x b b' t (hr.terms t ht) hb J) _ _ h1
  have e2 := foldlM_effect (fun g : GroupRow => ρ.val (g.c.entry J))
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff) _
    row.units.toList
    (fun u _ b b' hb => addEntryTo_main ρ S L hL x b b' u.oracle u.part u.index u.coeff hb J)
    _ _ h2
  have e3 := foldlM_effect (fun g : GroupRow => ρ.val (g.c.entry J)) _ _ row.runs.toList
    (fun w hw b b' hb => addRunTo_main ρ S L hL x b b' w (hr.runs w hw) hb J) _ _ h3
  have e4 := foldlM_effect (fun g : GroupRow => ρ.val (g.c.entry J)) _ _ row.forms.toList
    (fun f hf b b' hb => addFormTo_main ρ S L x b b' f (hr.forms f hf) hb J) _ _ h4
  dsimp only at e1 e2 e3 e4
  rw [GroupRow.ready_c] at e1
  unfold Row.mainSum
  rw [e4, e3, e2, e1]
  ring

/-- At an index where the weight (mainWeight) of the member o is 1 and that of every other oracle
message is 0, x times a row adds x times the row's coefficient on the entry of o that belongs to the
index. -/
theorem Row.mainSum_member (S : Statement) (L : GroupLayout) (x : E) (row : Row) (o J : Nat)
    (h1 : mainWeight (K := K) S L o J = 1) (h0 : ∀ o', o' ≠ o → mainWeight (K := K) S L o' J = 0) :
    row.mainSum ρ S L x J = ρ.val (row.coefficient o .main (mainBack S L o J)) * ρ.val x := by
  unfold Row.mainSum
  rw [Row.coefficient_val, add_mul, add_mul, add_mul, ← List.sum_map_mul_right,
    ← List.sum_map_mul_right, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        apply List.map_congr_left
        intro t _
        by_cases e : t.oracle = o
        · by_cases p : t.part = .main <;> simp [e, p, h1]
        · by_cases p : t.part = .main <;> simp [e, p, h0 _ e]
      · congr 1
        apply List.map_congr_left
        intro t _
        by_cases e : t.oracle = o
        · by_cases p : t.part = .main <;> simp [e, p, h1]
        · by_cases p : t.part = .main <;> simp [e, p, h0 _ e]
    · congr 1
      apply List.map_congr_left
      intro t _
      by_cases e : t.oracle = o
      · by_cases p : t.part = .main <;> simp [e, p, h1]
      · by_cases p : t.part = .main <;> simp [e, p, h0 _ e]
  · congr 1
    apply List.map_congr_left
    intro t _
    by_cases e : t.oracle = o
    · simp [e, h1]
    · simp [e, h0 _ e]

/-- At an index where every weight (mainWeight) is 0 a row adds nothing. -/
theorem Row.mainSum_none (S : Statement) (L : GroupLayout) (x : E) (row : Row) (J : Nat)
    (h0 : ∀ o, mainWeight (K := K) S L o J = 0) : row.mainSum ρ S L x J = 0 := by
  unfold Row.mainSum
  simp [h0]

/-! ## Runs: a multiple, and a sum with a multiple -/

/-- A product with an element of the base field reads as the product of the readings. -/
theorem scaleE_val (s : F) (a : E) : ρ.val (scaleE s a) = ρ.val (ofF s) * ρ.val a := by
  have e : scaleE s a = mulE (ofF s) a := by
    apply triple_inj
    rw [scaleE_triple, mulE_triple, ofF_triple, Fmt.mulE_ofF]
  rw [e, ρ.mul]

/-- a + s x reads as the sum and product of the readings. -/
theorem maddE_val (a s x : E) : ρ.val (maddE a s x) = ρ.val a + ρ.val s * ρ.val x := by
  have e : maddE a s x = addE a (mulE s x) := by
    apply triple_inj
    rw [maddE_triple, addE_triple, mulE_triple]
  rw [e, ρ.add, ρ.mul]

/-- a + s x, with s in the base field, reads as the sum and product of the readings. -/
theorem maddS_val (a : E) (s : F) (x : E) :
    ρ.val (maddS a s x) = ρ.val a + ρ.val (ofF s) * ρ.val x := by
  have e : maddS a s x = addE a (scaleE s x) := by
    apply triple_inj
    rw [maddS_triple, addE_triple, scaleE_triple]
  rw [e, ρ.add, scaleE_val]

/-- An entry of an array that is made from a function. -/
theorem getD_ofFn (n : Nat) (f : Fin n → E) (j : Nat) :
    (Array.ofFn f).getD j zeroE = if h : j < n then f ⟨j, h⟩ else zeroE := by
  by_cases h : j < n
  · simp [Array.getD, h]
  · simp [Array.getD, h]

/-- A multiple of a run has as many coefficients. -/
theorem Run.size_scaled (w : Run) (x : E) : (w.scaled x).coeffs.size = w.coeffs.size := by
  unfold Run.scaled
  cases h : w.coeffs <;> simp [Coeffs.size]

/-- A coefficient of x times a run reads as the coefficient times x. -/
theorem Run.get_scaled (w : Run) (x : E) (j : Nat) :
    ρ.val ((w.scaled x).coeffs.get j) = ρ.val (w.coeffs.get j) * ρ.val x := by
  unfold Run.scaled
  cases h : w.coeffs with
  | own c =>
    simp only [Coeffs.get]
    by_cases hj : j < c.size
    · simp [Array.getD, hj, ρ.mul, mul_comm]
    · simp [Array.getD, hj, ρ.zero]
  | stretch v start count =>
    simp only [Coeffs.get, getD_ofFn]
    by_cases hj : j < count
    · simp [hj, scaleE_val]
    · simp [hj, ρ.zero]

/-- x times a run reads, at every index, as the run times x. -/
theorem Run.val_scaled (w : Run) (x : E) (idx : Nat) :
    (w.scaled x).val ρ idx = w.val ρ idx * ρ.val x := by
  unfold Run.val
  rw [Run.size_scaled, Run.get_scaled]
  have e1 : (w.scaled x).first = w.first := rfl
  have e2 : (w.scaled x).step = w.step := rfl
  rw [e1, e2]
  split <;> simp

/-- A run plus a multiple of another has as many coefficients as the run. -/
theorem Run.size_addScaled (r other : Run) (x : E) :
    (r.addScaled other x).coeffs.size = r.coeffs.size := by
  unfold Run.addScaled
  cases h : other.coeffs <;> simp [Coeffs.size]

/-- A coefficient of a run plus x times another run. -/
theorem Run.get_addScaled (r other : Run) (x : E) (j : Nat) (hj : j < r.coeffs.size) :
    ρ.val ((r.addScaled other x).coeffs.get j) =
      ρ.val (r.coeffs.get j) + ρ.val (other.coeffs.get j) * ρ.val x := by
  unfold Run.addScaled
  cases h : other.coeffs with
  | own c =>
    show ρ.val ((Array.ofFn (n := r.coeffs.size) fun j =>
      maddE (r.coeffs.get j.val) x (c.getD j.val zeroE)).getD j zeroE) =
        ρ.val (r.coeffs.get j) + ρ.val (c.getD j zeroE) * ρ.val x
    rw [getD_ofFn, dif_pos hj, maddE_val]
    ring
  | stretch v start count =>
    show ρ.val ((Array.ofFn (n := r.coeffs.size) fun j =>
      if j.val < count then maddS (r.coeffs.get j.val) (v.getD (start + j.val) 0) x
      else r.coeffs.get j.val).getD j zeroE) =
        ρ.val (r.coeffs.get j) +
          ρ.val (if j < count then ofF (v.getD (start + j) 0) else zeroE) * ρ.val x
    rw [getD_ofFn, dif_pos hj]
    by_cases hc : j < count
    · simp only [hc, if_true, maddS_val]
    · simp [hc, ρ.zero]

/-- A run plus x times another run on the same entries reads, at every index, as the sum. -/
theorem Run.val_addScaled (r other : Run) (x : E) (idx : Nat) (hl : r.liesAs other = true) :
    (r.addScaled other x).val ρ idx = r.val ρ idx + other.val ρ idx * ρ.val x := by
  unfold Run.liesAs at hl
  simp only [Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨_, _⟩, hf⟩, hs⟩, hn⟩ := hl
  unfold Run.val
  rw [Run.size_addScaled]
  have e1 : (r.addScaled other x).first = r.first := rfl
  have e2 : (r.addScaled other x).step = r.step := rfl
  rw [e1, e2, ← hf, ← hs, ← hn]
  split
  · rename_i hc
    rw [Run.get_addScaled ρ r other x _ hc.2.2.2]
  · simp

/-! ## A row plus a multiple of another row -/

/-- If one member of a list is changed so that its value grows by δ, the sum of the values grows by
δ. -/
theorem sum_modify {α : Type} (g : α → K) (f : α → α) (δ : K) : ∀ (l : List α) (i : Nat),
    i < l.length → (∀ a, l[i]? = some a → g (f a) = g a + δ) →
    ((l.modify i f).map g).sum = (l.map g).sum + δ
  | [], i, hi, _ => by simp at hi
  | a :: l, 0, _, h => by
    have e := h a (by simp)
    simp only [List.modify_zero_cons, List.map_cons, List.sum_cons, e]
    ring
  | a :: l, i + 1, hi, h => by
    have ih := sum_modify g f δ l i (by simpa using hi) (fun b hb => h b (by simpa using hb))
    simp only [List.modify_succ_cons, List.map_cons, List.sum_cons, ih]
    ring

/-- What the runs of a list read as, together, on an entry. -/
def runsSum (o : Nat) (part : Part) (idx : Nat) (l : List Run) : K :=
  (l.map fun w => if w.oracle = o ∧ w.part = part then w.val ρ idx else 0).sum

/-- One step of Row.addRunsScaled, copied here so that it has a name. -/
def mergeRun (x : E) (runs : Array Run) (w : Run) : Array Run :=
  match runs.findIdx? (fun r : Run => r.liesAs w) with
  | some i => runs.modify i (fun r : Run => r.addScaled w x)
  | none => runs.push (w.scaled x)

/-- One step of Row.addRunsScaled adds x times the run to what the runs read as. -/
theorem runsSum_step (o : Nat) (part : Part) (idx : Nat) (runs : Array Run) (w : Run) (x : E) :
    runsSum ρ o part idx (mergeRun x runs w).toList =
      runsSum ρ o part idx runs.toList +
        (if w.oracle = o ∧ w.part = part then w.val ρ idx else 0) * ρ.val x := by
  unfold mergeRun
  cases hf : runs.findIdx? (fun r : Run => r.liesAs w) with
  | none =>
    have e1 : (w.scaled x).oracle = w.oracle := rfl
    have e2 : (w.scaled x).part = w.part := rfl
    simp only [runsSum, Array.toList_push, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, e1, e2, Run.val_scaled]
    split <;> simp
  | some i =>
    obtain ⟨hi, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.1 hf
    simp only [runsSum, Array.toList_modify]
    apply sum_modify
    · simpa using hi
    · intro a ha
      have ea : a = runs[i] := by
        have : runs.toList[i]? = some runs[i] := by simp [hi]
        rw [this] at ha
        exact (Option.some.inj ha).symm
      subst ea
      have hl : runs[i].liesAs w = true := hp
      have e1 : (runs[i].addScaled w x).oracle = runs[i].oracle := rfl
      have e2 : (runs[i].addScaled w x).part = runs[i].part := rfl
      rw [e1, e2, Run.val_addScaled ρ _ _ _ _ hl]
      have hl' := hl
      unfold Run.liesAs at hl'
      simp only [Bool.and_eq_true, beq_iff_eq] at hl'
      obtain ⟨⟨⟨⟨ho, hq⟩, _⟩, _⟩, _⟩ := hl'
      rw [ho, hq]
      split <;> ring

/-- Row.addRunsScaled adds x times the other runs to what the runs read as. -/
theorem runsSum_addRunsScaled (o : Nat) (part : Part) (idx : Nat) (x : E) :
    ∀ (others : List Run) (runs : Array Run),
    runsSum ρ o part idx (others.foldl (mergeRun x) runs).toList =
      runsSum ρ o part idx runs.toList + runsSum ρ o part idx others * ρ.val x
  | [], runs => by simp [runsSum]
  | w :: others, runs => by
    rw [List.foldl_cons, runsSum_addRunsScaled o part idx x others, runsSum_step]
    simp only [runsSum, List.map_cons, List.sum_cons]
    ring

/-- The coefficient of a row plus x times another row. -/
theorem Row.coefficient_addScaled (r other : Row) (x : E) (o : Nat) (part : Part) (idx : Nat) :
    ρ.val ((r.addScaled other x).coefficient o part idx) =
      ρ.val (r.coefficient o part idx) + ρ.val (other.coefficient o part idx) * ρ.val x := by
  have hr := runsSum_addRunsScaled ρ o part idx x other.runs.toList r.runs
  rw [Array.foldl_toList] at hr
  have hm : (r.addRunsScaled other x).runs = other.runs.foldl (mergeRun x) r.runs := rfl
  have h1 : (r.addRunsScaled other x).terms = r.terms := rfl
  have h2 : (r.addRunsScaled other x).units = r.units := rfl
  have h3 : (r.addRunsScaled other x).forms = r.forms := rfl
  unfold runsSum at hr
  simp only [Row.coefficient_val, Row.addScaled, hm, h1, h2, h3, Array.toList_append,
    Array.toList_map, List.map_append, List.sum_append, List.map_map, hr, add_mul,
    ← List.sum_map_mul_right]
  have t1 : (other.terms.toList.map ((fun t : Term =>
      if t.oracle = o ∧ t.part = part then ρ.val (t.v.entry idx) else 0) ∘
        fun t => { t with v := t.v.scale x })) =
      other.terms.toList.map fun t =>
        (if t.oracle = o ∧ t.part = part then ρ.val (t.v.entry idx) else 0) * ρ.val x := by
    apply List.map_congr_left
    intro t _
    simp only [Function.comp, Tensor.entry_scale]
    split <;> simp
  have t2 : (other.units.toList.map ((fun u : Single =>
      if u.oracle = o ∧ u.part = part then (if u.index = idx then ρ.val u.coeff else 0) else 0) ∘
        fun u => { u with coeff := mulE u.coeff x })) =
      other.units.toList.map fun u =>
        (if u.oracle = o ∧ u.part = part then (if u.index = idx then ρ.val u.coeff else 0)
          else 0) * ρ.val x := by
    apply List.map_congr_left
    intro u _
    simp only [Function.comp, ρ.mul]
    split
    · split <;> simp
    · simp
  have t3 : (other.forms.toList.map ((fun f : MainForm =>
      if f.oracle = o ∧ part = .main then ρ.val (f.c.entry idx) else 0) ∘
        fun f => { f with c := f.c.scale x })) =
      other.forms.toList.map fun f =>
        (if f.oracle = o ∧ part = .main then ρ.val (f.c.entry idx) else 0) * ρ.val x := by
    apply List.map_congr_left
    intro f _
    simp only [Function.comp, Form.entry_scale]
    split <;> simp
  rw [t1, t2, t3]
  ring

/-! ## BAT -/

/-- a_0 + y a_1 + y^2 a_2 + .. for the list a_0, a_1, a_2, .. -/
def hornerSum (y : K) : List K → K
  | [] => 0
  | a :: l => a + y * hornerSum y l

/-- hornerSum, as the sum over i of y^i times entry i of the list. -/
theorem hornerSum_eq_sum (y : K) : ∀ l : List K,
    hornerSum y l = ((List.range l.length).map fun i => y ^ i * l.getD i 0).sum
  | [] => rfl
  | a :: l => by
    rw [hornerSum, hornerSum_eq_sum y l, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.sum_cons, List.map_map, ← List.sum_map_mul_left]
    simp only [pow_zero, one_mul, List.getD_cons_zero]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
    simp only [Function.comp, List.getD_cons_succ, pow_succ]
    ring

/-- The target of a row plus x times another row. -/
theorem Row.target_addScaled (r other : Row) (x : E) :
    ρ.val (r.addScaled other x).target = ρ.val r.target + ρ.val other.target * ρ.val x := by
  have e : (r.addScaled other x).target = maddE r.target x other.target := rfl
  rw [e, maddE_val]
  ring

/-- The loop of Bat.combineRows, for any function R from rows to K that is additive (hR): started
with the row s.1 and the factor s.2, it adds to R s.1 the sum of s.2 x^i times R of row number i. -/
theorem combineRows_fold (x : E) (R : Row → K)
    (hR : ∀ r other y, R (r.addScaled other y) = R r + R other * ρ.val y) :
    ∀ (l : List Row) (s : Row × E),
    R (l.foldl (fun (s : Row × E) r => (s.1.addScaled r s.2, mulE s.2 x)) s).1 =
      R s.1 + ρ.val s.2 * hornerSum (ρ.val x) (l.map R)
  | [], s => by simp [hornerSum]
  | r :: l, s => by
    rw [List.foldl_cons, combineRows_fold x R hR l]
    simp only [hR, ρ.mul, List.map_cons, hornerSum]
    ring

/-- BAT-sigma, coefficient by coefficient: the batched row's coefficient on an entry reads as the
sum of x^i times the coefficient of row number i (from 0) on that entry. -/
theorem combineRows_coefficient (rows : Array Row) (x : E) (o : Nat) (part : Part) (idx : Nat) :
    ρ.val ((Bat.combineRows rows x).coefficient o part idx) =
      hornerSum (ρ.val x) (rows.toList.map fun r => ρ.val (r.coefficient o part idx)) := by
  unfold Bat.combineRows
  rw [← Array.foldl_toList,
    combineRows_fold ρ x (fun r => ρ.val (r.coefficient o part idx))
      (fun r other y => Row.coefficient_addScaled ρ r other y o part idx)]
  simp [Row.coefficient_val, ρ.one]

/-- BAT-sigma, the target: it reads as the sum of x^i times the target of row number i (from 0). -/
theorem combineRows_target (rows : Array Row) (x : E) :
    ρ.val (Bat.combineRows rows x).target =
      hornerSum (ρ.val x) (rows.toList.map fun r => ρ.val r.target) := by
  unfold Bat.combineRows
  rw [← Array.foldl_toList,
    combineRows_fold ρ x (fun r => ρ.val r.target)
      (fun r other y => Row.target_addScaled ρ r other y)]
  simp [ρ.one, ρ.zero]

/-! ## BAT on a group: the main table and the target -/

/-- A row's coefficient is that of its structured parts plus that of its written-out parts, as
Bat.combine splits it. -/
theorem Row.coefficient_split (r : Row) (o : Nat) (part : Part) (idx : Nat) :
    ρ.val (r.coefficient o part idx) =
      ρ.val (({ r with units := #[], runs := #[] } : Row).coefficient o part idx) +
        ρ.val (({ units := r.units, runs := r.runs } : Row).coefficient o part idx) := by
  simp only [Row.coefficient_val]
  simp
  ring

/-- The structured parts of a row that fits also fit. -/
theorem RowFits.structured {S : Statement} {r : Row} (h : RowFits S r) :
    RowFits S { r with units := #[], runs := #[] } :=
  ⟨h.terms, by simp, h.forms⟩

/-- What holds of the row in which Bat.combine gathers the written-out parts: it has no structured
part, and its runs have a step of at least 1. -/
structure Aside (r : Row) : Prop where
  terms : r.terms = #[]
  forms : r.forms = #[]
  runs : ∀ w ∈ r.runs.toList, 0 < w.step

/-- The gathering row fits. -/
theorem Aside.fits {S : Statement} {r : Row} (h : Aside r) : RowFits S r :=
  ⟨by simp [h.terms], h.runs, by simp [h.forms]⟩

/-- If a property holds of every member of a list and the change keeps it, it holds of every member
after the change. -/
theorem all_modify {α : Type} (P : α → Prop) (f : α → α) (hf : ∀ a, P a → P (f a)) :
    ∀ (l : List α) (i : Nat), (∀ a ∈ l, P a) → ∀ a ∈ l.modify i f, P a
  | [], _, _ => by simp
  | b :: l, 0, h => by
    simp only [List.modify_zero_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨hf b (h b (by simp)), fun a ha => h a (by simp [ha])⟩
  | b :: l, i + 1, h => by
    simp only [List.modify_succ_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨h b (by simp), all_modify P f hf l i (fun a ha => h a (by simp [ha]))⟩

/-- One step of Row.addRunsScaled keeps every run's step at least 1. -/
theorem mergeRun_steps (x : E) (runs : Array Run) (w : Run) (hw : 0 < w.step)
    (h : ∀ r ∈ runs.toList, 0 < r.step) : ∀ r ∈ (mergeRun x runs w).toList, 0 < r.step := by
  unfold mergeRun
  split
  · rw [Array.toList_modify]
    exact all_modify (fun r : Run => 0 < r.step) (fun r : Run => r.addScaled w x)
      (fun a ha => ha) _ _ h
  · intro r hr
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact h r hr
    · exact hw

/-- Row.addRunsScaled keeps every run's step at least 1. -/
theorem foldl_mergeRun_steps (x : E) : ∀ (others : List Run) (runs : Array Run),
    (∀ w ∈ others, 0 < w.step) → (∀ r ∈ runs.toList, 0 < r.step) →
    ∀ r ∈ (others.foldl (mergeRun x) runs).toList, 0 < r.step
  | [], _, _, h => h
  | w :: others, runs, ho, h => by
    rw [List.foldl_cons]
    exact foldl_mergeRun_steps x others _ (fun a ha => ho a (by simp [ha]))
      (mergeRun_steps x runs w (ho w (by simp)) h)

/-- The gathering row still meets Aside after the written-out summands of a row that fits are
added. -/
theorem Aside.addScaled {S : Statement} {a r : Row} (ha : Aside a) (hr : RowFits S r) (x : E) :
    Aside (a.addScaled { units := r.units, runs := r.runs } x) := by
  have hm : (a.addScaled { units := r.units, runs := r.runs } x).runs =
      r.runs.foldl (mergeRun x) a.runs := rfl
  refine ⟨?_, ?_, ?_⟩
  · show a.terms ++ (#[] : Array Term).map _ = #[]
    simp [ha.terms]
  · show a.forms ++ (#[] : Array MainForm).map _ = #[]
    simp [ha.forms]
  · rw [hm, ← Array.foldl_toList]
    exact foldl_mergeRun_steps x _ _ hr.runs ha.runs

/-- The loop of Bat.combine, seen through two functions: R on a group's row, C on a row. F is the
condition on the rows; P is a condition on the group's row that carrying a row keeps. If carrying a
row that meets F adds C of the row times the factor (hAdd), C is additive (hC) and C of a row is C
of its structured summands plus C of its written-out summands (hSplit), then R of the group's row
plus C of the gathering row grows by the sum of s.2.2 x^i times C of row number i. -/
theorem combine_fold (S : Statement) (L : GroupLayout) (x : E) (F : Row → Prop)
    (hF1 : ∀ r, F r → RowFits S r) (hF2 : ∀ r : Row, F r → F { r with units := #[], runs := #[] })
    (P : GroupRow → Prop) (R : GroupRow → K) (C : Row → K)
    (hAdd : ∀ row y acc acc', F row → P acc → addToGroupRow S L row y acc = some acc' →
      P acc' ∧ R acc' = R acc + C row * ρ.val y)
    (hC : ∀ r other y, C (r.addScaled other y) = C r + C other * ρ.val y)
    (hSplit : ∀ r : Row, C r = C { r with units := #[], runs := #[] } +
      C { units := r.units, runs := r.runs }) :
    ∀ (l : List Row) (s s' : GroupRow × Row × E), (∀ r ∈ l, F r) → Aside s.2.1 → P s.1 →
    l.foldlM (fun (s : GroupRow × Row × E) r => do
      let structured : Row := { r with units := #[], runs := #[] }
      let acc ← addToGroupRow S L structured s.2.2 s.1
      let written : Row := { units := r.units, runs := r.runs }
      pure (acc, s.2.1.addScaled written s.2.2, mulE s.2.2 x)) s = some s' →
    Aside s'.2.1 ∧ P s'.1 ∧
      R s'.1 + C s'.2.1 = R s.1 + C s.2.1 + ρ.val s.2.2 * hornerSum (ρ.val x) (l.map C)
  | [], s, s', _, ha, hp, h => by
    have e : s = s' := by simpa using h
    subst e
    exact ⟨ha, hp, by simp [hornerSum]⟩
  | r :: l, s, s', hr, ha, hp, h => by
    rw [List.foldlM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s1, ⟨acc, h1, rfl⟩, h2⟩ := h
    have fr := hr r (by simp)
    obtain ⟨p1, e1⟩ := hAdd _ _ _ _ (hF2 r fr) hp h1
    have ih := combine_fold S L x F hF1 hF2 P R C hAdd hC hSplit l _ s'
      (fun a h' => hr a (by simp [h'])) (ha.addScaled (hF1 r fr) s.2.2) p1 h2
    refine ⟨ih.1, ih.2.1, ?_⟩
    rw [ih.2.2]
    simp only [e1, hC, ρ.mul, List.map_cons, hornerSum, hSplit r]
    ring

/-- Bat.combine, read at one place: under the conditions of combine_fold, and if the empty rows read
as 0, the batched row reads as the sum of x^i times the i-th row's reading. -/
theorem combine_read (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (F : Row → Prop)
    (hF1 : ∀ r, F r → RowFits S r) (hF2 : ∀ r : Row, F r → F { r with units := #[], runs := #[] })
    (hF3 : ∀ a, Aside a → F a) (hr : ∀ r ∈ input.rows.toList, F r)
    (P : GroupRow → Prop) (R : GroupRow → K) (C : Row → K)
    (hAdd : ∀ row y acc acc', F row → P acc →
      addToGroupRow S input.layout row y acc = some acc' →
      P acc' ∧ R acc' = R acc + C row * ρ.val y)
    (hC : ∀ r other y, C (r.addScaled other y) = C r + C other * ρ.val y)
    (hSplit : ∀ r : Row, C r = C { r with units := #[], runs := #[] } +
      C { units := r.units, runs := r.runs })
    (hP0 : P { group := g }) (hR0 : R { group := g } = 0) (hC0 : C {} = 0) :
    R out = hornerSum (ρ.val x) (input.rows.toList.map C) := by
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨s, h1, h2⟩ := h
  obtain ⟨ha, hp, e⟩ := combine_fold ρ S input.layout x F hF1 hF2 P R C hAdd hC hSplit
    input.rows.toList _ s hr ⟨rfl, rfl, by simp⟩ hP0 h1
  rw [(hAdd _ _ _ _ (hF3 _ ha) hp h2).2, ρ.one, mul_one, e]
  simp only [hR0, hC0, ρ.one]
  ring

/-- The sum is 0 if every member is 0. -/
theorem hornerSum_zero (y : K) : ∀ l : List K, (∀ a ∈ l, a = 0) → hornerSum y l = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [hornerSum, h a (by simp), hornerSum_zero y l (fun b hb => h b (by simp [hb]))]
    simp

/-- If Bat.combine returns a row, the layout meets MainBlocksOk and every row meets RowFits: at an
index of the main table whose row is in the block of the member o and of no other oracle message,
the batched row's coefficient reads as the sum of x^i times the coefficient of row number i (from 0)
on the entry of o that belongs to the index. -/
theorem combine_main_member (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MainBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r) (o J : Nat)
    (h1 : mainWeight (K := K) S input.layout o J = 1)
    (h0 : ∀ o', o' ≠ o → mainWeight (K := K) S input.layout o' J = 0) :
    ρ.val (out.c.entry J) = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      ρ.val (r.coefficient o .main (mainBack S input.layout o J))) :=
  combine_read ρ S g input x out h (RowFits S) (fun _ a => a)
    (fun _ a => a.structured) (fun _ a => a.fits) hr (fun _ => True) (fun a => ρ.val (a.c.entry J))
    (fun r => ρ.val (r.coefficient o .main (mainBack S input.layout o J)))
    (fun row y acc acc' hf _ ha => by
      refine ⟨trivial, ?_⟩
      dsimp only
      rw [addToGroupRow_main ρ S _ hL row hf y acc acc' ha J,
        Row.mainSum_member ρ S _ y row o J h1 h0])
    (fun r other y => Row.coefficient_addScaled ρ r other y _ _ _)
    (fun r => Row.coefficient_split ρ r _ _ _)
    trivial (Form.entry_empty ρ J) (by simp [Row.coefficient_val])

/-- If Bat.combine returns a row, the layout meets MainBlocksOk and every row meets RowFits: at an
index of the main table whose row is in no member's block the batched row's coefficient reads as
0. -/
theorem combine_main_none (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MainBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r) (J : Nat)
    (h0 : ∀ o, mainWeight (K := K) S input.layout o J = 0) : ρ.val (out.c.entry J) = 0 := by
  have e := combine_read ρ S g input x out h (RowFits S) (fun _ a => a)
    (fun _ a => a.structured) (fun _ a => a.fits) hr (fun _ => True) (fun a => ρ.val (a.c.entry J))
    (fun _ => 0)
    (fun row y acc acc' hf _ ha => by
      refine ⟨trivial, ?_⟩
      dsimp only
      rw [addToGroupRow_main ρ S _ hL row hf y acc acc' ha J, Row.mainSum_none ρ S _ y row J h0]
      simp)
    (fun _ _ _ => by simp) (fun _ => by simp) trivial (Form.entry_empty ρ J) rfl
  dsimp only at e
  rw [e]
  exact hornerSum_zero _ _ (by simp)

/-- For a member whose main rows are folded and whose block is aligned and inside the table
(BlockOk), the weight is 1 at the indices whose row is in the block and 0 at the others. -/
theorem mainWeight_rows (S : Statement) (L : GroupLayout) (o i first J : Nat)
    (hf : L.find o = some i) (hk : L.kept.getD i false = false)
    (hm : L.mainFirst.getD i none = some first) (hb : BlockOk (S.rowBits o .main) first L.k) :
    mainWeight (K := K) S L o J =
      if first ≤ J % 2 ^ L.k ∧ J % 2 ^ L.k < first + 2 ^ S.rowBits o .main then 1 else 0 := by
  unfold mainWeight
  simp only [hf, hk, hm, Bool.false_eq_true, if_false, inBlock_iff J _ first L.k hb]

/-! ## BAT on a group: the target -/

/-- Carrying a structured vector leaves the target as it was. -/
theorem addTermTo_target (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (h : addTermTo S L x acc t = some acc') : acc'.target = acc.target := by
  unfold addTermTo at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h
    | (dsimp only at h; split at h <;> first | (cases h; rfl) | cases h)

/-- Carrying a coefficient on a single entry leaves the target as it was. -/
theorem addEntryTo_target (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (o : Nat) (part : Part) (index : Nat) (coeff : E)
    (h : addEntryTo S L x acc o part index coeff = some acc') : acc'.target = acc.target := by
  unfold addEntryTo at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h
    | (dsimp only at h; split at h <;> first | (cases h; rfl) | cases h)

/-- Carrying a whole coefficient vector leaves the target as it was. -/
theorem addFormTo_target (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (h : addFormTo S L x acc f = some acc') : acc'.target = acc.target := by
  unfold addFormTo at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h
    | (dsimp only at h; split at h <;> first | (cases h; rfl) | cases h)

/-- A fold whose steps keep a value keeps it. -/
theorem foldlM_keeps {α β γ : Type} (R : β → γ) (step : β → α → Option β)
    (hs : ∀ a b b', step b a = some b' → R b' = R b) :
    ∀ (l : List α) (b b' : β), l.foldlM step b = some b' → R b' = R b
  | [], b, b', h => by
    have e : b = b' := by simpa using h
    rw [e]
  | a :: l, b, b', h => by
    rw [List.foldlM_cons] at h
    cases h1 : step b a with
    | none => simp [h1] at h
    | some b1 =>
      simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
      rw [foldlM_keeps R step hs l b1 b' h, hs a b b1 h1]

/-- x times a row, carried to a group's row: x times the row's target is added to the target. -/
theorem addToGroupRow_target (S : Statement) (L : GroupLayout) (row : Row) (x : E)
    (acc acc' : GroupRow) (h : addToGroupRow S L row x acc = some acc') :
    ρ.val acc'.target = ρ.val acc.target + ρ.val row.target * ρ.val x := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := h
  have e1 := foldlM_keeps (fun g : GroupRow => g.target) _
    (fun t b b' hb => addTermTo_target S L x b b' t hb) _ _ _ h1
  have e2 := foldlM_keeps (fun g : GroupRow => g.target)
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff)
    (fun u b b' hb => addEntryTo_target S L x b b' _ _ _ _ hb) _ _ _ h2
  have e3 := foldlM_keeps (fun g : GroupRow => g.target) _
    (fun (w : Run) b b' hb => foldlM_keeps (fun g : GroupRow => g.target) _
      (fun j c c' hc => addEntryTo_target S L x c c' _ _ _ _ hc) _ _ _ hb) _ _ _ h3
  have e4 := foldlM_keeps (fun g : GroupRow => g.target) _
    (fun f b b' hb => addFormTo_target S L x b b' f hb) _ _ _ h4
  have e0 : (acc.ready L).target = acc.target := by
    unfold GroupRow.ready
    split <;> rfl
  dsimp only at e1 e2 e3 e4
  rw [maddE_val, e4, e3, e2, e1, e0]
  ring

/-- If Bat.combine returns a row and every row meets RowFits: the target reads as the sum of x^i
times the target of row number i (from 0). (RowFits is asked only because the proof goes through
combine_read.) -/
theorem combine_target (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hr : ∀ r ∈ input.rows.toList, RowFits S r) :
    ρ.val out.target = hornerSum (ρ.val x) (input.rows.toList.map fun r => ρ.val r.target) :=
  combine_read ρ S g input x out h (RowFits S) (fun _ a => a)
    (fun _ a => a.structured) (fun _ a => a.fits) hr (fun _ => True) (fun a => ρ.val a.target)
    (fun r => ρ.val r.target)
    (fun row y acc acc' _ _ ha => ⟨trivial, addToGroupRow_target ρ S _ row y acc acc' ha⟩)
    (fun r other y => Row.target_addScaled ρ r other y)
    (fun r => by
      show ρ.val r.target = ρ.val r.target + ρ.val zeroE
      rw [ρ.zero, add_zero])
    trivial ρ.zero ρ.zero

/-! ## BAT on a group: the kept members -/

/-- What a group's row reads as on entry idx of the main table of the kept member o. -/
def keptSum (o idx : Nat) (l : List KeptForm) : K :=
  (l.map fun kf => if kf.oracle = o then ρ.val (kf.c.entry idx) else 0).sum

/-- 1 if o is a member whose main rows are kept; else 0. -/
def keptWeight (L : GroupLayout) (o : Nat) : K :=
  match L.find o with
  | none => 0
  | some i => if L.kept.getD i false then 1 else 0

/-- If no member of a list has the number o', the sum of g over the list is the sum over the members
below o' plus the sum over those above. -/
theorem sum_filter_split (g : KeptForm → K) (o' : Nat) : ∀ l : List KeptForm,
    (∀ a ∈ l, a.oracle ≠ o') →
    ((l.filter (·.oracle < o')).map g).sum + ((l.filter (o' < ·.oracle)).map g).sum =
      (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_filter_split g o' l (fun b hb => h b (by simp [hb]))
    have ha := h a (by simp)
    by_cases h1 : a.oracle < o'
    · have h2 : ¬ o' < a.oracle := by omega
      simp only [List.filter_cons, h1, h2, decide_true, decide_false, if_true, Bool.false_eq_true,
        if_false, List.map_cons, List.sum_cons, ← ih]
      ring
    · have h2 : o' < a.oracle := by omega
      simp only [List.filter_cons, h1, h2, decide_true, decide_false, if_true, Bool.false_eq_true,
        if_false, List.map_cons, List.sum_cons, ← ih]
      ring

/-- A change of the form of the kept member o' that adds δ at the entry idx adds δ to what the row
reads as there on o', and nothing on another member. -/
theorem keptSum_onKept (kept : Array KeptForm) (o' : Nat) (f : Form → Form) (o idx : Nat) (δ : K)
    (hf : ∀ c : Form, ρ.val ((f c).entry idx) = ρ.val (c.entry idx) + δ) :
    keptSum ρ o idx (onKept kept o' f).toList =
      keptSum ρ o idx kept.toList + if o' = o then δ else 0 := by
  unfold onKept
  cases hx : kept.findIdx? (·.oracle == o') with
  | some i =>
    obtain ⟨hi, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.1 hx
    simp only [keptSum, Array.toList_modify]
    apply sum_modify
    · simpa using hi
    · intro a ha
      have ea : a = kept[i] := by
        have : kept.toList[i]? = some kept[i] := by simp [hi]
        rw [this] at ha
        exact (Option.some.inj ha).symm
      subst ea
      have ho : kept[i].oracle = o' := by simpa using hp
      simp only [ho, hf]
      split <;> simp
  | none =>
    have hn : ∀ a ∈ kept.toList, a.oracle ≠ o' := by
      intro a ha
      have := Array.findIdx?_eq_none_iff.1 hx a (by simpa using ha)
      simpa using this
    simp only [keptSum, Array.toList_append, Array.toList_filter, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hf, Form.entry_empty,
      zero_add]
    rw [← sum_filter_split _ o' kept.toList hn]
    ring

/-- What a structured vector adds on entry idx of the kept member o. -/
theorem addTermTo_kept (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (h : addTermTo S L x acc t = some acc') (o idx : Nat) :
    keptSum ρ o idx acc'.kept.toList = keptSum ρ o idx acc.kept.toList +
      (if t.oracle = o ∧ t.part = .main then
        keptWeight (K := K) L o * ρ.val (t.v.entry idx) * ρ.val x else 0) := by
  unfold addTermTo at h
  cases hf : L.find t.oracle with
  | none => simp [hf] at h
  | some i =>
    simp only [hf] at h
    cases hp : t.part with
    | mask =>
      simp only [hp] at h
      cases hm : L.maskFirst.getD i none with
      | none => simp [hm] at h
      | some first =>
        simp only [hm] at h
        split at h
        · cases h
        · cases h
          simp
    | main =>
      simp only [hp] at h
      by_cases hk : L.kept.getD i false = true
      · simp only [hk, if_true, Option.some.injEq] at h
        subst h
        rw [keptSum_onKept ρ _ _ _ o idx (ρ.val (t.v.entry idx) * ρ.val x)
          (fun c => by rw [Form.entry_add, Tensor.entry_scale])]
        by_cases e : t.oracle = o
        · subst e
          simp [keptWeight, hf, hk]
        · simp [e]
      · simp only [hk, Bool.false_eq_true, if_false] at h
        cases hm : L.mainFirst.getD i none with
        | none => simp [hm] at h
        | some first =>
          simp only [hm] at h
          split at h
          · cases h
          · cases h
            by_cases e : t.oracle = o
            · subst e
              simp [keptWeight, hf, hk]
            · simp [e]

/-- What a coefficient on a single entry adds on entry idx of the kept member o. -/
theorem addEntryTo_kept (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (o' : Nat) (part : Part) (index : Nat) (coeff : E)
    (h : addEntryTo S L x acc o' part index coeff = some acc') (o idx : Nat) :
    keptSum ρ o idx acc'.kept.toList = keptSum ρ o idx acc.kept.toList +
      (if o' = o ∧ part = .main then
        keptWeight (K := K) L o * (if index = idx then ρ.val coeff else 0) * ρ.val x else 0) := by
  unfold addEntryTo at h
  cases hf : L.find o' with
  | none => simp [hf] at h
  | some i =>
    simp only [hf] at h
    cases part with
    | mask =>
      simp only at h
      cases hm : L.maskFirst.getD i none with
      | none => simp [hm] at h
      | some first =>
        simp only [hm] at h
        split at h
        · cases h
          simp
        · cases h
    | main =>
      simp only at h
      by_cases hk : L.kept.getD i false = true
      · simp only [hk, if_true, Option.some.injEq] at h
        subst h
        rw [keptSum_onKept ρ _ _ _ o idx ((if index = idx then ρ.val coeff else 0) * ρ.val x)
          (fun c => by
            rw [Form.entry_addEntry, ρ.mul]
            split <;> ring)]
        by_cases e : o' = o
        · subst e
          simp [keptWeight, hf, hk]
        · simp [e]
      · simp only [hk, Bool.false_eq_true, if_false] at h
        cases hm : L.mainFirst.getD i none with
        | none => simp [hm] at h
        | some first =>
          simp only [hm, Option.some.injEq] at h
          subst h
          by_cases e : o' = o
          · subst e
            simp [keptWeight, hf, hk]
          · simp [e]

/-- What a whole coefficient vector adds on entry idx of the kept member o. -/
theorem addFormTo_kept (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (h : addFormTo S L x acc f = some acc') (o idx : Nat) :
    keptSum ρ o idx acc'.kept.toList = keptSum ρ o idx acc.kept.toList +
      (if f.oracle = o then
        keptWeight (K := K) L o * ρ.val (f.c.entry idx) * ρ.val x else 0) := by
  unfold addFormTo at h
  cases hf : L.find f.oracle with
  | none => simp [hf] at h
  | some i =>
    simp only [hf] at h
    by_cases hk : L.kept.getD i false = true
    · simp only [hk, if_true, Option.some.injEq] at h
      subst h
      rw [keptSum_onKept ρ _ _ _ o idx (ρ.val (f.c.entry idx) * ρ.val x)
        (fun c => by rw [Form.entry_addForm])]
      by_cases e : f.oracle = o
      · subst e
        simp [keptWeight, hf, hk]
      · simp [e]
    · simp only [hk, Bool.false_eq_true, if_false] at h
      cases hm : L.mainFirst.getD i none with
      | none => simp [hm] at h
      | some first =>
        simp only [hm] at h
        split at h
        · cases h
        · cases h
          by_cases e : f.oracle = o
          · subst e
            simp [keptWeight, hf, hk]
          · simp [e]

/-- What a run of coefficients adds on entry idx of the kept member o. -/
theorem addRunTo_kept (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (w : Run)
    (hs : 0 < w.step) (h : addRunTo S L x acc w = some acc') (o idx : Nat) :
    keptSum ρ o idx acc'.kept.toList = keptSum ρ o idx acc.kept.toList +
      (if w.oracle = o ∧ w.part = .main then
        keptWeight (K := K) L o * w.val ρ idx * ρ.val x else 0) := by
  unfold addRunTo at h
  have e := foldlM_effect (fun g : GroupRow => keptSum ρ o idx g.kept.toList) _
    (fun j => if w.oracle = o ∧ w.part = .main then
        keptWeight (K := K) L o *
          (if w.first + w.step * j = idx then ρ.val (w.coeffs.get j) else 0) * ρ.val x
      else 0) (List.range w.coeffs.size)
    (fun j _ b b' hb => addEntryTo_kept ρ S L x b b' _ _ _ _ hb o idx) acc acc' h
  dsimp only at e
  rw [e]
  congr 1
  by_cases hp : w.oracle = o ∧ w.part = .main
  · simp only [hp, and_self, if_true]
    rw [← Run.sum_val ρ w hs, List.sum_map_mul_right, List.sum_map_mul_left]
  · simp [hp]

/-- x times a row, carried to a group's row: on entry idx of a kept member o, x times the row's
coefficient on that entry is added; on an oracle message that is no kept member, nothing. -/
theorem addToGroupRow_kept (S : Statement) (L : GroupLayout) (row : Row) (hr : RowFits S row)
    (x : E) (acc acc' : GroupRow) (h : addToGroupRow S L row x acc = some acc') (o idx : Nat) :
    keptSum ρ o idx acc'.kept.toList = keptSum ρ o idx acc.kept.toList +
      keptWeight (K := K) L o * ρ.val (row.coefficient o .main idx) * ρ.val x := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := h
  have e1 := foldlM_effect (fun g : GroupRow => keptSum ρ o idx g.kept.toList) _ _
    row.terms.toList (fun t _ b b' hb => addTermTo_kept ρ S L x b b' t hb o idx) _ _ h1
  have e2 := foldlM_effect (fun g : GroupRow => keptSum ρ o idx g.kept.toList)
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff) _
    row.units.toList
    (fun u _ b b' hb => addEntryTo_kept ρ S L x b b' u.oracle u.part u.index u.coeff hb o idx)
    _ _ h2
  have e3 := foldlM_effect (fun g : GroupRow => keptSum ρ o idx g.kept.toList) _ _
    row.runs.toList (fun w hw b b' hb => addRunTo_kept ρ S L x b b' w (hr.runs w hw) hb o idx)
    _ _ h3
  have e4 := foldlM_effect (fun g : GroupRow => keptSum ρ o idx g.kept.toList) _ _
    row.forms.toList (fun f _ b b' hb => addFormTo_kept ρ S L x b b' f hb o idx) _ _ h4
  have e0 : (acc.ready L).kept = acc.kept := by
    unfold GroupRow.ready
    split <;> rfl
  dsimp only at e1 e2 e3 e4
  rw [e4, e3, e2, e1, e0, Row.coefficient_val, mul_add, mul_add, mul_add, add_mul, add_mul,
    add_mul, ← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
    ← List.sum_map_mul_left, ← List.sum_map_mul_right, ← List.sum_map_mul_right,
    ← List.sum_map_mul_right, ← List.sum_map_mul_right]
  have t1 : ∀ (c : Prop) [Decidable c] (a : K),
      (if c then keptWeight (K := K) L o * a * ρ.val x else 0) =
        keptWeight (K := K) L o * (if c then a else 0) * ρ.val x := by
    intro c _ a
    split <;> simp
  simp only [t1, and_true]
  ring

/-- If Bat.combine returns a row and every row meets RowFits: on entry idx of the main table of a
kept member o the batched row reads as the sum of x^i times the coefficient of row number i (from 0)
on that entry. -/
theorem combine_kept (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hr : ∀ r ∈ input.rows.toList, RowFits S r)
    (o idx : Nat) (h1 : keptWeight (K := K) input.layout o = 1) :
    keptSum ρ o idx out.kept.toList = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      ρ.val (r.coefficient o .main idx)) :=
  combine_read ρ S g input x out h (RowFits S) (fun _ a => a)
    (fun _ a => a.structured) (fun _ a => a.fits) hr (fun _ => True)
    (fun a => keptSum ρ o idx a.kept.toList) (fun r => ρ.val (r.coefficient o .main idx))
    (fun row y acc acc' hf _ ha => by
      refine ⟨trivial, ?_⟩
      dsimp only
      rw [addToGroupRow_kept ρ S _ row hf y acc acc' ha o idx, h1, one_mul])
    (fun r other y => Row.coefficient_addScaled ρ r other y _ _ _)
    (fun r => Row.coefficient_split ρ r _ _ _)
    trivial (by simp [keptSum]) (by simp [Row.coefficient_val])

end OnBytes

#print axioms OnBytes.combineRows_coefficient
#print axioms OnBytes.combine_main_member
#print axioms OnBytes.combine_main_none
#print axioms OnBytes.combine_target
#print axioms OnBytes.combine_kept
