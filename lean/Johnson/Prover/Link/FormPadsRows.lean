-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormPadsRows.lean: THE FORM's HALF: the three kinds of rows that the link lays
((eq_phi), Johnson/Desc/K15/K15.lean; (rec_gamma) and (loc_x), Johnson/Desc/K14/Text.lean) HAVE THE
COEFFICIENT 0, AS WORDS, on every mask table, on every message but the folds that they name, and on
a fold from the end of their written support on; and the public places of a message's pad on its
main table lie beyond the room that a vector is given there.

Main names.
  placed_zero     vectors on an aligned stretch, cut below a length: 0 from the stretch's cut on.
  eqPhi_beyond    (eq_phi): from the cut on.
  recGamma_beyond (rec_gamma): from the table's message length on.
  locX_beyond     (loc_x): from the entry S.tailFirst + S.index.code.r on.
  pad_beyond      the places of Send.pad (OnBytes/Iop/Send.lean) on a main table are Beyond
    vectorRoom (OnBytes/Iop/Foldeq.lean).

How. By values: the library's laws on what a coefficient reads as (coefficient_addLaid,
coefficient_foldl_units, Johnson/Desc/K14/Law/; entry_onTable, OnBytes/Slice/BlkForm.lean;
tensorBelow_val), read at the library's field, then isZero_of_val (FormPads.lean).

Limits. For all draws: no premise on phi, on a seed's point, on a column or on the weights but a
length. Not here: that a record's message has Send.pad's places as its pad, its layout and its
shape: so RowClauses.pads (Johnson/Desc/First/Batch/Law/DoorTests.lean) at a record is not said
here. Johnson/Prover/Link/FormRowsLaws.lean has PadsFar from these three as premises (padsFar_of),
and the rows' RowClauses from FoldSeat, which holds PadsFar, as a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormPads
import Johnson.Desc.K15.K15
import OnBytes.Slice.BlkCross
import Johnson.Desc.K14.Law.Placed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open OnBytes.Model (Reading)
open Desc.K14.Law (coefficient_addLaid coefficient_empty coefficient_foldl_units tensorBelow_mem
  tensorBelow_val recGamma_inv locX_inv recRow padList recCoeff)

theorem vars_eq (z : List E) (s : E) : (Tensor.eq z s).vars = z.length := by
  simp [Tensor.eq, Tensor.vars]

/-- **(eq_phi).** -/
theorem eqPhi_beyond (S : LinkShape) (phi : List E) (o0 o1 : FoldedRow) (row : Row)
    (h : Desc.K15.eqPhi S phi o0 o1 = some row) (h0 : S.entryBits ≤ o0.lay.bits)
    (h1 : S.entryBits ≤ o1.lay.bits) (o : Nat) (pt : Part) (i : Nat)
    (b0 : pt = .main → o = o0.oracle → Beyond o0.lay S.cut i)
    (b1 : pt = .main → o = o1.oracle → Beyond o1.lay S.cut i) :
    isZeroE (row.coefficient o pt i) = true := by
  unfold Desc.K15.eqPhi at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    beq_iff_eq] at h
  obtain ⟨_, hg, plus, hp, minus, hm, rfl⟩ := h
  have hl : phi.length = S.entryBits := by
    by_contra c
    simp [guard, c] at hg
  refine isZero_of_val _ _ _ _ ?_
  unfold FoldedRow.addAll
  rw [coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]
  have e0 : (if o0.oracle = o ∧ Part.main = pt then
      (plus.map fun t => Reading.gl.val ((o0.lay.onTable t).entry i)).sum else 0) = 0 := by
    split_ifs with c
    · exact laid_cut_zero _ _ _ _ _ _ _ rfl ((vars_eq _ _).trans hl) h0 hp (b0 c.2.symm c.1.symm)
    · rfl
  have e1 : (if o1.oracle = o ∧ Part.main = pt then
      (minus.map fun t => Reading.gl.val ((o1.lay.onTable t).entry i)).sum else 0) = 0 := by
    split_ifs with c
    · exact laid_cut_zero _ _ _ _ _ _ _ rfl ((vars_eq _ _).trans hl) h1 hm (b1 c.2.symm c.1.symm)
    · rfl
  rw [e0, e1, add_zero]

/-- **(rec_gamma).** -/
theorem recGamma_beyond (s : IndexShape) (seed : SampleSeed) (a : Nat) (w y : Array E)
    (u : FoldedRow) (row : Row) (h : Desc.K14.recGamma s seed a w y u = some row)
    (hz : seed.z.length = s.cubeBits) (hb : s.cubeBits ≤ u.lay.bits)
    (hp : 3 * s.answers ≤ s.code.ell) (o : Nat) (pt : Part) (i : Nat)
    (b : pt = .main → o = u.oracle → Beyond u.lay s.code.ell i) :
    isZeroE (row.coefficient o pt i) = true := by
  obtain ⟨L, sum, hL, _, rfl⟩ := recGamma_inv s seed a w y u row h
  refine isZero_of_val _ _ _ _ ?_
  show Reading.gl.val ((recRow s seed a u L).coefficient o pt i) = 0
  unfold recRow FoldedRow.addAll
  rw [coefficient_foldl_units, coefficient_addLaid, coefficient_empty, zero_add]
  split_ifs with c
  · have hB := b c.2.symm c.1.symm
    rw [laid_cut_zero _ _ _ _ _ _ _ rfl ((vars_eq _ _).trans hz) hb hL hB, zero_add]
    refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    rw [if_neg]
    intro e
    simp only [padList, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨a', ha', t, ht, rfl⟩ := hx
    have hlt : s.padPlace a' t < s.code.ell := by
      unfold IndexShape.padPlace IndexShape.plain IndexShape.pads
      omega
    have hell : s.code.ell ≤ 2 ^ u.lay.bits :=
      Nat.le_trans (Slice.le_two_pow_ceilLog2 _) (Nat.pow_le_pow_right (by decide) hb)
    have := hB.2
    rw [← e, Slice.entryAt_index _ _ (Nat.lt_of_lt_of_le hlt hell)] at this
    omega
  · rfl

/-- Vectors with n variables, cut below r, on the stretch of 2 ^ n entries that begins at entry
first, a multiple of 2 ^ n: laid on a table they read as 0 from entry first + r on. -/
theorem placed_zero {K : Type} [Field K] (ρ : Reading K) (lay : VectorLay) (v : Tensor)
    (n r first : Nat) (tail : List Tensor) (i : Nat) (hd : v.denseVars = []) (hv : v.vars = n)
    (hn : n ≤ lay.bits) (hL : tensorBelow v 0 n r = some tail) (hal : 2 ^ n ∣ first)
    (hi : Beyond lay (first + r) i) :
    ((tail.map (·.insertChoice n (lay.bits - n) (first / 2 ^ n))).map fun t =>
      ρ.val ((lay.onTable t).entry i)).sum = 0 := by
  have hmem := tensorBelow_mem v hd 0 n r tail hL
  have hJ := Slice.entryAt_lt lay i hi.1
  have hbits : 2 ^ lay.bits = 2 ^ n * 2 ^ (lay.bits - n) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have e : ((tail.map (·.insertChoice n (lay.bits - n) (first / 2 ^ n))).map fun t =>
      ρ.val ((lay.onTable t).entry i)) =
      tail.map fun t =>
        (if lay.entryAt i / 2 ^ n % 2 ^ (lay.bits - n) = first / 2 ^ n % 2 ^ (lay.bits - n) then 1
          else 0) * ρ.val (t.entry (unshift n (lay.bits - n) (lay.entryAt i))) := by
    rw [List.map_map]
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨t1, t2⟩ := hmem t ht
    have t3 : t.pairs.length = n := t2.trans hv
    have hv' : (t.insertChoice n (lay.bits - n) (first / 2 ^ n)).vars = lay.bits := by
      simp only [Tensor.vars, Tensor.insertChoice, List.length_append, List.length_take,
        List.length_drop, choicePairs_length, t3]
      omega
    show ρ.val ((lay.onTable (t.insertChoice n (lay.bits - n) (first / 2 ^ n))).entry i) = _
    rw [Slice.entry_onTable ρ lay _ (by simp [Tensor.insertChoice, t1]) (le_of_eq hv') i hi.1, hv',
      if_pos hJ, Tensor.entry_insertChoice ρ t n (lay.bits - n) (first / 2 ^ n) _
        (le_of_eq t3.symm)]
  rw [e, List.sum_map_mul_left]
  by_cases c : lay.entryAt i / 2 ^ n % 2 ^ (lay.bits - n) = first / 2 ^ n % 2 ^ (lay.bits - n)
  · rw [if_pos c, one_mul, tensorBelow_val ρ v hd 0 n r tail hL, if_neg]
    have hq : lay.entryAt i / 2 ^ n < 2 ^ (lay.bits - n) :=
      Nat.div_lt_of_lt_mul (by rw [← hbits]; exact hJ)
    have hf : first / 2 ^ n < 2 ^ (lay.bits - n) :=
      Nat.div_lt_of_lt_mul (by rw [← hbits]; have := hi.2; omega)
    rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hf] at c
    have h0 : lay.entryAt i / 2 ^ (n + (lay.bits - n)) = 0 := by
      rw [Nat.pow_add, ← hbits]
      exact Nat.div_eq_of_lt hJ
    unfold unshift
    rw [h0, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.mod_mod]
    have d1 := Nat.div_add_mod (lay.entryAt i) (2 ^ n)
    have d2 := Nat.div_mul_cancel hal
    rw [c] at d1
    have := hi.2
    rw [Nat.mul_comm] at d1
    omega
  · rw [if_neg c, zero_mul]

theorem Beyond.mono {lay : VectorLay} {N N' i : Nat} (h : Beyond lay N' i) (hN : N ≤ N') :
    Beyond lay N i := ⟨h.1, Nat.le_trans hN h.2⟩

theorem vars_product_take (f : List F) (s : E) (n : Nat) (L : List Tensor) (len : Nat)
    (h : tensorBelow (Tensor.product (f.take n) s) 0 n len = some L) :
    (Tensor.product (f.take n) s).vars = n := by
  have h1 := (Desc.K14.Law.tensorBelow_some _ _ _ _ _ h).1
  have h2 : (Tensor.product (f.take n) s).vars ≤ n := by
    simp only [Tensor.product, Tensor.vars, List.length_map, List.length_take]
    omega
  omega

/-- **(loc_x).** -/
theorem locX_beyond (S : FoldeqShape) (x : Nat) (w : Array E) (column : Array F) (u : FoldedRow)
    (row : Row) (h : Desc.K14.locX S x w column u = some row)
    (hb : S.index.code.logEll ≤ u.lay.bits) (he : S.index.code.ell ≤ S.tailFirst)
    (hr : S.tailFirst + S.index.code.r ≤ 2 ^ u.lay.bits) (hal : 2 ^ S.index.code.logR ∣ S.tailFirst)
    (o : Nat) (pt : Part) (i : Nat)
    (b : pt = .main → o = u.oracle → Beyond u.lay (S.tailFirst + S.index.code.r) i) :
    isZeroE (row.coefficient o pt i) = true := by
  obtain ⟨A, tail, sum, hA, ht, _, rfl⟩ := locX_inv S x w column u row h
  refine isZero_of_val _ _ _ _ ?_
  show Reading.gl.val ((u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
    (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))).coefficient
      o pt i) = 0
  unfold FoldedRow.addAll
  rw [coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]
  split_ifs with c
  · have hB := b c.2.symm c.1.symm
    rw [laid_cut_zero _ _ _ _ _ _ _ rfl (vars_product_take _ _ _ _ _ hA) hb hA
      (hB.mono (by omega)), zero_add]
    by_cases h0 : S.index.code.r = 0
    · rw [if_pos (by simp [h0])] at ht
      obtain rfl := Option.some.inj ht
      rfl
    · rw [if_neg (by simp [h0])] at ht
      exact placed_zero _ _ _ _ _ _ _ _ rfl (vars_product_take _ _ _ _ _ ht)
        (Desc.K14.Law.ceilLog2_le _ _ (by omega)) ht hal hB
  · rfl

/-- A least value taken over some members of a list is at most each of them. -/
theorem foldl_min_le {α : Type} (c : α → Bool) (f : α → Nat) : ∀ (l : List α) (m : Nat) (a : α),
    a ∈ l → c a = true → l.foldl (fun m p => if c p then min m (f p) else m) m ≤ f a
  | p :: l, m, a, ha, hc => by
    rw [List.foldl_cons]
    have hle : ∀ (l : List α) (m : Nat),
        l.foldl (fun m p => if c p then min m (f p) else m) m ≤ m := by
      intro l
      induction l with
      | nil => exact fun m => Nat.le_refl m
      | cons q l ih =>
        intro m
        rw [List.foldl_cons]
        refine Nat.le_trans (ih _) ?_
        split_ifs
        · exact Nat.min_le_left _ _
        · exact Nat.le_refl _
    rcases List.mem_cons.1 ha with rfl | h
    · rw [if_pos hc]
      exact Nat.le_trans (hle l _) (Nat.min_le_right _ _)
    · exact foldl_min_le c f l _ a h hc

/-- A place of the pad on the main table, written out. -/
theorem pad_main (codes : Codes) (s : OracleShape) (places : List PadPlace) (q : PadPlace)
    (hp : Send.pad codes s = some places) (hq : q ∈ places) (hm : q.part = .main) :
    ∃ each a t, a < s.answers ∧ t < each ∧
      each * s.answers ≤ (codes.base.getD s.code default).ell ∧
      q.index = s.mainRows - 1 +
        ((codes.base.getD s.code default).ell - each * s.answers + each * a + t) *
          2 ^ (Send.cube codes s).mainRowBits := by
  unfold Send.pad at hp
  by_cases hk : (Send.cube codes s).hasMask = true
  · simp only [hk, if_true, Bool.true_or] at hp
    split at hp
    · cases hp
    · obtain rfl := Option.some.inj hp
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq
      obtain ⟨a, _, t, _, rfl⟩ := hq
      cases hm
  · simp only [hk, Bool.false_eq_true, if_false, Bool.false_or] at hp
    generalize (if (s.mainDeg == 3) = true then 1 else 3) = each at hp
    split at hp
    · cases hp
    · rename_i hlen
      obtain rfl := Option.some.inj hp
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq
      obtain ⟨a, ha, t, ht, rfl⟩ := hq
      exact ⟨_, a, t, ha, ht, Nat.not_lt.1 hlen, rfl⟩

/-- **The pad's places on a main table lie beyond the vector's room.** -/
theorem pad_beyond (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (places : List PadPlace)
    (q : PadPlace) (hp : Send.pad codes s = some places) (hq : q ∈ places) (hm : q.part = .main)
    (h0 : 0 < s.mainRows) :
    Beyond (vectorLay codes s rowsHigh) (vectorRoom codes s rowsHigh) q.index := by
  obtain ⟨each, a, t, ha, ht, hlen, hi⟩ := pad_main codes s places q hp hq hm
  constructor
  · have hrb : (Send.cube codes s).mainRowBits = ceilLog2 s.mainRows := by
      simp [Send.cube, h0]
    rw [hi, hrb]
    show s.mainRows - 1 + _ * 2 ^ ceilLog2 s.mainRows <
      2 ^ (ceilLog2 s.mainRows + (codes.base.getD s.code default).logEll)
    have r1 := Slice.le_two_pow_ceilLog2 s.mainRows
    have r2 := Slice.le_two_pow_ceilLog2 (codes.base.getD s.code default).ell
    have hpl : (codes.base.getD s.code default).ell - each * s.answers + each * a + t <
        (codes.base.getD s.code default).ell := by
      have : each * (a + 1) ≤ each * s.answers := Nat.mul_le_mul_left _ ha
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    generalize (codes.base.getD s.code default).ell - each * s.answers + each * a + t = P at hpl ⊢
    have hpl' : P + 1 ≤ 2 ^ (codes.base.getD s.code default).logEll := Nat.le_trans hpl r2
    have m1 := Nat.mul_le_mul_right (2 ^ ceilLog2 s.mainRows) hpl'
    rw [Nat.succ_mul] at m1
    rw [Nat.pow_add, Nat.mul_comm (2 ^ ceilLog2 s.mainRows)]
    omega
  · unfold vectorRoom
    dsimp only
    split_ifs with c1 c2 c3
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · rw [beq_iff_eq.1 c3] at ha
      exact absurd ha (Nat.not_lt_zero _)
    · rw [hp]
      exact foldl_min_le (fun p => p.part == .main) _ places _ q hq
        (by show (q.part == Part.main) = true; rw [hm]; rfl)

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.vars_eq
#print axioms Johnson.Prover.Link.eqPhi_beyond
#print axioms Johnson.Prover.Link.recGamma_beyond
#print axioms Johnson.Prover.Link.placed_zero
#print axioms Johnson.Prover.Link.Beyond.mono
#print axioms Johnson.Prover.Link.vars_product_take
#print axioms Johnson.Prover.Link.locX_beyond
#print axioms Johnson.Prover.Link.foldl_min_le
#print axioms Johnson.Prover.Link.pad_main
#print axioms Johnson.Prover.Link.pad_beyond
