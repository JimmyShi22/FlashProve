-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/KeptLaw3.lean: proofs of the four statements L-3 of KeptSpec.lean,
on which of its random values the rows of a member made by `memOfSending` (JobShared.lean) read.

  `spot_reads`   proves `Spec.spot_reads`: at a place with a number the entry of `laid` is the value
                 of that number; at another place the entry does not depend on the values
  `spots_tab`    proves `Spec.spots_tab`: `rowsOfLaid` tabulates the entries at the places of
                 `spotsOf`, in their order
  `mem_reads`    proves `Spec.mem_reads`: a member's rows depend on its random values below `dueOf`
                 alone. No premise on the shape
  `spot_perm`    proves `Spec.spot_perm`: under `msgShapeFits` the numbers at the tabulated places
                 are a rearrangement of 0 to `dueOf` - 1
  `spot_perm_sent`   the same at each message of the two sendings that is no fresh table, under
                 `sendingsFit`
  The other lemmas are on lists and numbers; each has a docstring. `grid_succ` and `grid_map` are
  those of KeptLaw2.lean.

By what. `coinOf` repeats the conditions and offsets of the arm of `laid` for a message that is no
fresh table: a case distinction on the place. The numbers fall into four stretches, one for each
table. The mask rows' entries are numbered entry by entry while the places run row by row, and at a
shape with main rows alone the pad's numbers come before the main tails' in the list of places: so
the two lists are rearrangements of each other, not equal. Of `msgShapeFits` the proof of
`spot_perm` uses the third clause alone, and of it: no mask row, a main row and at most as many
answers as the message is long; or no main row and a mask row. `StagesOk` is not used.

Limits. On numbers of random values alone: from which numbers the tabulated entries are read. None
of the statements says that values are distinct, or how they are sampled. A message that is a fresh
table is not treated. `spot_perm_sent` stands at the two sendings as `sendingsFit` has them
(`atPoint` 0). No theorem here carries a member's rows into the first stage's rows of a run. Nothing
on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.KeptLaw2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape)
open OnBytes.Slice (GE ofE)
open ProofFile.Honest.K14 (Laid laid dueOf MsgSort SendJob Ask)

/-! ## 1 The entry at a place -/

/-- Proves `Spec.spot_reads`. -/
theorem spot_reads : Spec.spot_reads := by
  intro codes s v cs high x
  cases x with
  | main r j =>
    by_cases h : (s.maskRows == 0 && r + 1 == s.mainRows &&
        decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
        decide (j < (codes.base.getD s.code default).ell)) = true
    · simp only [ProofFile.Honest.K14.Laid.read, laid, coinOf, if_pos h]
    · simp only [ProofFile.Honest.K14.Laid.read, laid, coinOf, if_neg h]
  | mainTail r t => rfl
  | mask r j => rfl
  | maskTail r t => rfl

/-! ## 2 What is tabulated -/

/-- The rows of a table, in a row. -/
theorem tabE_flatten (r n : ℕ) (f : ℕ → ℕ → OnBytes.E) :
    (tabE r n f).flatten = grid r n fun i j => (f i j).triple := rfl

/-- Proves `Spec.spots_tab`. -/
theorem spots_tab : Spec.spots_tab := by
  intro codes s L
  simp only [rowsOfLaid, spotsOf, tabE_flatten, List.map_append, grid_map,
    ProofFile.Honest.K14.Laid.read]

/-! ## 3 On lists and numbers -/

/-- Where g yields a value at every member, `filterMap` is `map`. -/
theorem some_of {α β : Type} (g : α → Option β) (h : α → β) :
    ∀ l : List α, (∀ a ∈ l, g a = some (h a)) → l.filterMap g = l.map h
  | [], _ => rfl
  | a :: l, H => by
    rw [List.filterMap_cons_some (H a List.mem_cons_self), List.map_cons,
      some_of g h l fun x hx => H x (List.mem_cons_of_mem _ hx)]

/-- Where g yields none at every member, `filterMap` is empty. -/
theorem none_of {α β : Type} (g : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, g a = none) → l.filterMap g = []
  | [], _ => rfl
  | a :: l, H => by
    rw [List.filterMap_cons_none (H a List.mem_cons_self),
      none_of g l fun x hx => H x (List.mem_cons_of_mem _ hx)]

/-- A grid at all of whose places g yields a value. -/
theorem grid_some {α β : Type} (g : α → Option β) (m : ℕ) (f : ℕ → ℕ → α) (h : ℕ → ℕ → β)
    (H : ∀ b n, g (f b n) = some (h b n)) : ∀ r : ℕ, (grid r m f).filterMap g = grid r m h
  | 0 => rfl
  | r + 1 => by
    rw [grid_succ, grid_succ, List.filterMap_append, grid_some g m f h H r, List.filterMap_map,
      some_of (g ∘ f r) (h r) _ fun n _ => H r n]

/-- A grid at none of whose places g yields a value. -/
theorem grid_none {α β : Type} (g : α → Option β) (m : ℕ) (f : ℕ → ℕ → α) :
    ∀ r : ℕ, (∀ b < r, ∀ n, g (f b n) = none) → (grid r m f).filterMap g = []
  | 0, _ => rfl
  | r + 1, H => by
    rw [grid_succ, List.filterMap_append,
      grid_none g m f r fun b hb n => H b (Nat.lt_succ_of_lt hb) n, List.filterMap_map,
      none_of (g ∘ f r) _ fun n _ => H r (Nat.lt_succ_self r) n]
    rfl

/-- **A grid numbered row by row lists a stretch of numbers in order.** -/
theorem grid_range (a m : ℕ) : ∀ r : ℕ,
    (grid r m fun b n => a + b * m + n) = (List.range (r * m)).map (a + ·)
  | 0 => by
    rw [Nat.zero_mul]
    rfl
  | r + 1 => by
    rw [grid_succ, grid_range a m r, Nat.succ_mul, List.range_add, List.map_append, List.map_map]
    congr 1
    refine List.map_congr_left fun n _ => ?_
    show a + r * m + n = a + (r * m + n)
    rw [Nat.add_assoc]

/-- A list of appended pairs is a rearrangement of the two lists. -/
theorem flatMap_split {α β : Type} (f g : α → List β) :
    ∀ l : List α, (l.flatMap fun x => f x ++ g x).Perm (l.flatMap f ++ l.flatMap g)
  | [] => List.Perm.refl _
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons, List.append_assoc,
      List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine ((flatMap_split f g l).append_left _).trans ?_
    exact List.perm_append_comm_assoc _ _ _

/-- **Rows and entries exchanged: a rearrangement.** -/
theorem grid_swap {α : Type} (m : ℕ) (f : ℕ → ℕ → α) : ∀ r : ℕ,
    (grid r m f).Perm (grid m r fun n b => f b n)
  | 0 => by
    have e : (grid m 0 fun n b => f b n) = [] := by
      unfold grid
      exact List.flatMap_eq_nil_iff.2 fun _ _ => rfl
    rw [e]
    exact List.Perm.refl _
  | r + 1 => by
    have e : (grid m (r + 1) fun n b => f b n) =
        (List.range m).flatMap fun n => (List.range r).map (fun b => f b n) ++ [f r n] := by
      unfold grid
      refine congrArg (fun F => List.flatMap F (List.range m)) (funext fun n => ?_)
      rw [List.range_succ, List.map_append]
      rfl
    have e2 : ((List.range m).flatMap fun n => [f r n]) = (List.range m).map (f r) := by
      rw [List.flatMap_def]
      induction List.range m with
      | nil => rfl
      | cons a l ih => rw [List.map_cons, List.flatten_cons, ih, List.map_cons]; rfl
    rw [grid_succ, e]
    refine List.Perm.trans ?_ (flatMap_split _ _ _).symm
    rw [e2]
    exact (grid_swap m f r).append_right _

/-- A number in row b of r rows of m numbers lies below r * m. -/
theorem below {b r n m : ℕ} (hb : b < r) (hn : n < m) : b * m + n < r * m :=
  calc b * m + n < b * m + m := Nat.add_lt_add_left hn _
    _ = (b + 1) * m := (Nat.succ_mul b m).symm
    _ ≤ r * m := Nat.mul_le_mul_right m hb

/-- Two tables with the same entries within the counts are equal. -/
theorem tabE_congr (r n : ℕ) (f g : ℕ → ℕ → OnBytes.E) (H : ∀ i < r, ∀ j < n, f i j = g i j) :
    tabE r n f = tabE r n g := by
  unfold tabE
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  rw [H i (List.mem_range.1 hi) j (List.mem_range.1 hj)]

/-! ## 4 A member's rows read below `dueOf` alone -/

/-- The tabulated rows of a message that is no fresh table, at two families of values that agree
below `dueOf`. -/
theorem laid_congr (codes : Codes) (s : OracleShape) (v cs cs' : ℕ → OnBytes.E) (high : Bool)
    (H : ∀ i < dueOf codes s (.plain high), cs i = cs' i) :
    rowsOfLaid codes s (laid codes s v cs (.plain high)) =
      rowsOfLaid codes s (laid codes s v cs' (.plain high)) := by
  have hd : dueOf codes s (.plain high) =
      s.mainRows * (codes.base.getD s.code default).r + (if s.maskRows == 0 then s.answers else 0) +
        s.maskRows * (codes.mask.getD s.maskCode default).ell +
        s.maskRows * (codes.mask.getD s.maskCode default).r := rfl
  rw [hd] at H
  have h1 : tabE s.mainRows (codes.base.getD s.code default).ell
      (laid codes s v cs (.plain high)).main =
      tabE s.mainRows (codes.base.getD s.code default).ell
        (laid codes s v cs' (.plain high)).main := by
    refine tabE_congr _ _ _ _ fun r _ j _ => ?_
    by_cases h : (s.maskRows == 0 && r + 1 == s.mainRows &&
        decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
        decide (j < (codes.base.getD s.code default).ell)) = true
    · simp only [laid, if_pos h]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine H _ ?_
      rw [if_pos h.1.1.1]
      have a1 := h.1.2
      have a2 := h.2
      omega
    · simp only [laid, if_neg h]
  have h2 : tabE s.mainRows (codes.base.getD s.code default).r
      (laid codes s v cs (.plain high)).mainTail =
      tabE s.mainRows (codes.base.getD s.code default).r
        (laid codes s v cs' (.plain high)).mainTail := by
    refine tabE_congr _ _ _ _ fun r hr t ht => ?_
    have a := below hr ht
    exact H _ (by omega)
  have h3 : tabE s.maskRows (codes.mask.getD s.maskCode default).ell
      (laid codes s v cs (.plain high)).mask =
      tabE s.maskRows (codes.mask.getD s.maskCode default).ell
        (laid codes s v cs' (.plain high)).mask := by
    refine tabE_congr _ _ _ _ fun r hr j hj => ?_
    have a := below hj hr
    rw [Nat.mul_comm (codes.mask.getD s.maskCode default).ell s.maskRows] at a
    exact H _ (by omega)
  have h4 : tabE s.maskRows (codes.mask.getD s.maskCode default).r
      (laid codes s v cs (.plain high)).maskTail =
      tabE s.maskRows (codes.mask.getD s.maskCode default).r
        (laid codes s v cs' (.plain high)).maskTail := by
    refine tabE_congr _ _ _ _ fun r hr t ht => ?_
    have a := below hr ht
    exact H _ (by omega)
  unfold rowsOfLaid
  simp only [h1, h2, h3, h4]

/-- Proves `Spec.mem_reads`. -/
theorem mem_reads : Spec.mem_reads := by
  intro W X J at_ k fs ask v? w fr c c' high hs hc
  show rowsOfLaid J.Q.codes _ (laid J.Q.codes _ _ (fun i => OnBytes.E.ofTriple (ofE (c.e i)))
      (J.sort k)) =
    rowsOfLaid J.Q.codes _ (laid J.Q.codes _ _ (fun i => OnBytes.E.ofTriple (ofE (c'.e i)))
      (J.sort k))
  rw [hs] at hc ⊢
  exact laid_congr _ _ _ _ _ high fun i hi =>
    congrArg (fun x => OnBytes.E.ofTriple (ofE x)) (hc i hi)

/-! ## 5 The numbers at the tabulated places -/

/-- The last a of l entries of a row, numbered from p. -/
theorem pad_row (p a l : ℕ) (ha : a ≤ l) (g : ℕ → Option ℕ)
    (H : ∀ j, g j = if (decide (l - a ≤ j) && decide (j < l)) = true then some (p + (j - (l - a)))
      else none) :
    (List.range l).filterMap g = (List.range a).map (p + ·) := by
  obtain ⟨d, rfl⟩ : ∃ d, l = d + a := ⟨l - a, (Nat.sub_add_cancel ha).symm⟩
  rw [List.range_add, List.filterMap_append, List.filterMap_map,
    none_of g _ fun j hj => by
      rw [H j, if_neg]
      have := List.mem_range.1 hj
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega,
    some_of (g ∘ (d + ·)) (p + ·) _ fun i hi => by
      have := List.mem_range.1 hi
      show g (d + i) = some (p + i)
      rw [H (d + i), if_pos]
      · congr 2
        omega
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega]
  rfl

/-- **The numbers at the tabulated places are a rearrangement of a stretch from 0**, for any g that
has the four forms of `coinOf`, at a shape with main rows alone or mask rows alone. -/
theorem perm_core (R l cr a mR zl zr : ℕ) (g : Spot → Option ℕ)
    (hm : ∀ r j, g (.main r j) =
      if (mR == 0 && r + 1 == R && decide (l - a ≤ j) && decide (j < l)) = true then
        some (R * cr + (j - (l - a))) else none)
    (ht : ∀ r t, g (.mainTail r t) = some (r * cr + t))
    (hk : ∀ r j, g (.mask r j) = some (R * cr + (if mR == 0 then a else 0) + j * mR + r))
    (hs : ∀ r t, g (.maskTail r t) =
      some (R * cr + (if mR == 0 then a else 0) + mR * zl + r * zr + t))
    (hsh : (mR = 0 ∧ 0 < R ∧ a ≤ l) ∨ (R = 0 ∧ 0 < mR)) :
    ((grid R l Spot.main ++ grid R cr Spot.mainTail ++ grid mR zl Spot.mask ++
      grid mR zr Spot.maskTail).filterMap g).Perm
      (List.range (R * cr + (if mR == 0 then a else 0) + mR * zl + mR * zr)) := by
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append,
    grid_some g cr Spot.mainTail (fun r t => 0 + r * cr + t)
      (fun r t => by
        rw [ht]
        show some (r * cr + t) = some (0 + r * cr + t)
        rw [Nat.zero_add]) R,
    grid_some g zl Spot.mask _ hk mR, grid_some g zr Spot.maskTail _ hs mR, grid_range,
    grid_range]
  rcases hsh with ⟨rfl, hR, ha⟩ | ⟨rfl, hM⟩
  · obtain ⟨R, rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, (Nat.sub_add_cancel hR).symm⟩
    have e1 : (grid (R + 1) l Spot.main).filterMap g =
        (List.range a).map ((R + 1) * cr + ·) := by
      rw [grid_succ, List.filterMap_append,
        grid_none g l Spot.main R fun b hb n => by
          rw [hm, if_neg]
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          omega,
        List.filterMap_map, List.nil_append]
      exact pad_row _ a l ha _ fun j => by
        show g (.main R j) = _
        rw [hm]
        simp only [beq_self_eq_true, Bool.true_and]
    rw [e1]
    simp only [beq_self_eq_true, if_true, Nat.zero_mul, Nat.add_zero, List.range_zero,
      List.map_nil, List.append_nil]
    have e2 : (grid 0 zl fun b n => (R + 1) * cr + a + n * 0 + b) = [] := rfl
    rw [e2, List.append_nil, List.range_add]
    have e3 : (List.range ((R + 1) * cr)).map (0 + ·) = List.range ((R + 1) * cr) := by
      conv => rhs; rw [← List.map_id (List.range ((R + 1) * cr))]
      exact List.map_congr_left fun n _ => Nat.zero_add n
    rw [e3]
    exact List.perm_append_comm
  · have hne : (mR == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp only [hne, Nat.zero_mul, Nat.zero_add, Nat.add_zero, List.range_zero, List.map_nil,
      Bool.false_eq_true, if_false]
    have e0 : (grid 0 l Spot.main).filterMap g = [] := rfl
    rw [e0, List.nil_append, List.nil_append, List.range_add]
    refine List.Perm.append ?_ (List.Perm.refl _)
    refine (grid_swap zl (fun b n => n * mR + b) mR).trans ?_
    have e4 : (grid zl mR fun n b => n * mR + b) = grid zl mR fun n b => 0 + n * mR + b := by
      unfold grid
      refine congrArg (fun F => List.flatMap F (List.range zl))
        (funext fun n => List.map_congr_left fun b _ => ?_)
      show n * mR + b = 0 + n * mR + b
      rw [Nat.zero_add]
    rw [e4, grid_range, Nat.mul_comm zl mR]
    have e5 : (List.range (mR * zl)).map (0 + ·) = List.range (mR * zl) := by
      conv => rhs; rw [← List.map_id (List.range (mR * zl))]
      exact List.map_congr_left fun n _ => Nat.zero_add n
    rw [e5]

/-- Proves `Spec.spot_perm`. -/
theorem spot_perm : Spec.spot_perm := by
  intro codes s high h
  simp only [ProofFile.Honest.K14.msgShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  exact perm_core s.mainRows (codes.base.getD s.code default).ell
    (codes.base.getD s.code default).r s.answers s.maskRows
    (codes.mask.getD s.maskCode default).ell (codes.mask.getD s.maskCode default).r
    (coinOf codes s) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (h.2.elim (fun a => Or.inl ⟨a.1.1.1.1, a.1.1.1.2, a.1.2⟩) fun a => Or.inr ⟨a.1, a.2⟩)

/-- **The same at each message of the two sendings that is no fresh table**, under
`sendingsFit`. -/
theorem spot_perm_sent (Q : Desc.K14.P14) (h : ProofFile.Honest.K14.sendingsFit Q = true) (J : SendJob)
    (hJ : J = ProofFile.Honest.K14.jobU ⟨Q, 0⟩ ∨ J = ProofFile.Honest.K14.jobOmega ⟨Q, 0⟩) (k : ℕ)
    (hk : k < J.Q.sent.size) (high : Bool) (hs : J.sort k = .plain high) :
    ((spotsOf J.Q.codes (J.Q.sent.getD k default).shape).filterMap
      (coinOf J.Q.codes (J.Q.sent.getD k default).shape)).Perm
      (List.range (dueOf J.Q.codes (J.Q.sent.getD k default).shape (.plain high))) := by
  have hf : ProofFile.Honest.K14.sendShapeFits J = true := by
    simp only [ProofFile.Honest.K14.sendingsFit, Bool.and_eq_true] at h
    rcases hJ with rfl | rfl
    · exact h.1.1.1.2
    · exact h.1.1.2
  simp only [ProofFile.Honest.K14.sendShapeFits, Bool.and_eq_true, List.all_eq_true] at hf
  have hm := hf.2 k (List.mem_range.2 hk)
  rw [hs] at hm
  exact spot_perm _ _ high hm

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.spot_reads
#print axioms ProofFile.Honest.K12.Light.tabE_flatten
#print axioms ProofFile.Honest.K12.Light.spots_tab
#print axioms ProofFile.Honest.K12.Light.some_of
#print axioms ProofFile.Honest.K12.Light.none_of
#print axioms ProofFile.Honest.K12.Light.grid_some
#print axioms ProofFile.Honest.K12.Light.grid_none
#print axioms ProofFile.Honest.K12.Light.grid_range
#print axioms ProofFile.Honest.K12.Light.flatMap_split
#print axioms ProofFile.Honest.K12.Light.grid_swap
#print axioms ProofFile.Honest.K12.Light.below
#print axioms ProofFile.Honest.K12.Light.tabE_congr
#print axioms ProofFile.Honest.K12.Light.laid_congr
#print axioms ProofFile.Honest.K12.Light.mem_reads
#print axioms ProofFile.Honest.K12.Light.pad_row
#print axioms ProofFile.Honest.K12.Light.perm_core
#print axioms ProofFile.Honest.K12.Light.spot_perm
#print axioms ProofFile.Honest.K12.Light.spot_perm_sent
