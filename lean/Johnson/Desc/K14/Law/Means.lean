-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Means.lean: what the constraint (fold) says of words, and the law of (fold).

Main names: coefficient_addLaid, laid_sum, cut_laid_sum, sum_blocks, foldMeansW (what (fold) says of
words is the equation FoldEq), foldSound (the law of (fold): LAYS, MEANS and CATCHES joined),
foldLaw (with the half that says when "SPLIT" says yes).

What is not claimed. Nothing on how z_fd is drawn, on how words are tied to what a prover has sent,
that Placed holds behind the rounds in front, on (rec_gamma) or (loc_x), on an honest prover or on
hiding.

-/
import Johnson.Desc.K14.Law.Tensors
import Johnson.Desc.K14.Law.Lay
import Johnson.Desc.K14.Law.Catches
import Johnson.Desc.K14.Law.Tries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (ok)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The coefficients of a constraint made of laid vectors -/

/-- A structured vector more on a table. -/
theorem coefficient_add (r : Row) (o' : Nat) (p' : Part) (v : Tensor) (o : Nat) (pt : Part)
    (i : Nat) :
    ρ.val ((r.add o' p' v).coefficient o pt i) =
      ρ.val (r.coefficient o pt i) + if o' = o ∧ p' = pt then ρ.val (v.entry i) else 0 := by
  simp only [Row.coefficient_val, Row.add, Array.toList_push, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

/-- Vectors on a vector's entries, added as terms on the table that holds it. -/
theorem coefficient_addLaid (L : List Tensor) (r : Row) (o' : Nat) (lay : VectorLay) (o : Nat)
    (pt : Part) (i : Nat) :
    ρ.val ((addLaid r o' lay L).coefficient o pt i) =
      ρ.val (r.coefficient o pt i) + if o' = o ∧ Part.main = pt then
        (L.map fun t => ρ.val ((lay.onTable t).entry i)).sum else 0 := by
  induction L generalizing r with
  | nil => simp [addLaid]
  | cons t L ih =>
    have e : addLaid r o' lay (t :: L) = addLaid (r.add o' .main (lay.onTable t)) o' lay L := rfl
    rw [e, ih, coefficient_add]
    split_ifs <;> simp <;> ring

/-- They leave the target. -/
theorem target_addLaid (L : List Tensor) (r : Row) (o' : Nat) (lay : VectorLay) :
    (addLaid r o' lay L).target = r.target := by
  induction L generalizing r with
  | nil => rfl
  | cons t L ih =>
    have e : addLaid r o' lay (t :: L) = addLaid (r.add o' .main (lay.onTable t)) o' lay L := rfl
    rw [e, ih]; rfl

/-- The constraint without a summand has the coefficient 0 everywhere. -/
theorem coefficient_empty (o : Nat) (pt : Part) (i : Nat) :
    ρ.val (({} : Row).coefficient o pt i) = 0 := by
  rw [Row.coefficient_val]; simp

/-! ## Sums -/

/-- A sum of terms under one condition. -/
theorem sum_map_ite {α : Type} (c : Prop) [Decidable c] (L : List α) (f : α → K) :
    (L.map fun t => if c then f t else 0).sum = if c then (L.map f).sum else 0 := by
  split_ifs <;> simp

/-- A sum in which only the indices below R count. -/
theorem sum_below_len (n R : Nat) (hR : R ≤ n) (g : Nat → K) :
    ∑ j ∈ Finset.range n, (if j < R then g j else 0) = ∑ j ∈ Finset.range R, g j := by
  rw [← Finset.sum_subset (Finset.range_mono hR)]
  · exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.1 hj)]
  · intro j _ hj
    rw [if_neg fun h => hj (Finset.mem_range.2 h)]

/-- A sum below P R, block by block. -/
theorem sum_blocks (P R : Nat) (f : Nat → K) :
    ∑ k ∈ Finset.range (P * R), f k =
      ∑ j ∈ Finset.range R, ∑ t ∈ Finset.range P, f (t + P * j) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by rw [Nat.add_comm]

/-- A number is at most two to the number of bits that index it. -/
theorem le_two_pow_ceilLog2 (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  split_ifs with h
  · simpa using h
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- eqK at two lists of coordinates, at an index written in two parts. -/
theorem eqK_split (a b : List K) (n t j : Nat) (ha : a.length = n) (ht : t < 2 ^ n) :
    eqK (a ++ b) (t + 2 ^ n * j) = eqK a t * eqK b j := by
  subst ha
  rw [eqK_append, eqK_add_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt ht,
    Nat.zero_add]

/-- Vectors with n variables, laid on a table and applied to it: the sum over the vector's first
2 ^ n entries. -/
theorem laid_sum (lay : VectorLay) (L : List Tensor) (n : Nat)
    (hL : ∀ t ∈ L, t.denseVars = [] ∧ t.vars = n) (hn : n ≤ lay.bits) (w : Nat → K) :
    ∑ i ∈ Finset.range (2 ^ lay.bits),
        (L.map fun t => ρ.val ((lay.onTable t).entry i)).sum * w i =
      ∑ j ∈ Finset.range (2 ^ n), (L.map fun t => ρ.val (t.entry j)).sum * w (lay.index j) := by
  rw [sum_index lay]
  have hg : ∀ j ∈ Finset.range (2 ^ lay.bits),
      (L.map fun t => ρ.val ((lay.onTable t).entry (lay.index j))).sum =
        if j < 2 ^ n then (L.map fun t => ρ.val (t.entry j)).sum else 0 := by
    intro j hj
    rw [← sum_map_ite]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    have h0 := onTable_entry ρ lay t (hL t ht).1 (by rw [(hL t ht).2]; exact hn) j
      (Finset.mem_range.1 hj)
    rwa [(hL t ht).2] at h0
  have hsub : Finset.range (2 ^ n) ⊆ Finset.range (2 ^ lay.bits) :=
    Finset.range_mono (Nat.pow_le_pow_right (by decide) hn)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [hg j (hsub hj), if_pos (Finset.mem_range.1 hj)]
  · intro j hj hnj
    rw [hg j hj, if_neg (fun h => hnj (Finset.mem_range.2 h)), zero_mul]

/-- A vector cut below a length, laid on a table and applied to it. -/
theorem cut_laid_sum (lay : VectorLay) (v : Tensor) (hd : v.denseVars = [])
    (start count len : Nat) (L : List Tensor) (hL : tensorBelow v start count len = some L)
    (hn : v.vars ≤ lay.bits) (w : Nat → K) :
    ∑ i ∈ Finset.range (2 ^ lay.bits),
        (L.map fun t => ρ.val ((lay.onTable t).entry i)).sum * w i =
      ∑ j ∈ Finset.range (2 ^ v.vars),
        (if j / 2 ^ start % 2 ^ count < len then ρ.val (v.entry j) else 0) * w (lay.index j) := by
  rw [laid_sum ρ lay L v.vars (tensorBelow_mem v hd start count len L hL) hn]
  exact Finset.sum_congr rfl fun j _ => by rw [tensorBelow_val ρ v hd start count len L hL]

/-- A message that has a table is there. -/
theorem lt_of_has (T : Statement) (o : Nat) (pt : Part) (h : T.has o pt = true) :
    o < T.oracles.size := by
  by_contra hn
  have e : T.oracles[o]? = none := by
    simp only [Array.getElem?_eq_none_iff]; omega
  simp [Statement.has, e] at h

/-! ## MEANS -/

/-- **MEANS**, for (fold). -/
theorem foldMeansW : FoldMeansW ρ := by
  intro T S l lay row hf hP m
  have hR : S.matrixRows ≤ 2 ^ S.kRow := le_two_pow_ceilLog2 _
  unfold fold at hf
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hf
  obtain ⟨u0, hg, A, hA, B, hB, hrow⟩ := hf
  have hok : ok (foldL S l) = true := by
    by_contra hne
    simp [guard, hne] at hg
  simp only [ok, foldL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hok
  obtain ⟨hpsi, hz⟩ := hok
  have hvA : (Tensor.eq l.zFd).vars = S.kRow := by
    simp only [Tensor.eq, Tensor.vars, List.length_map, hz]
  have hlen : ((l.psiSh.take S.kLo).map ρ.val).length = S.kLo := by
    simp only [List.length_map, List.length_take, hpsi, LinShape.kCol]; omega
  have hvB : (Tensor.eq (l.psiSh.take S.kLo ++ l.zFd) (negE oneE)).vars = S.kLo + S.kRow := by
    simp only [Tensor.eq, Tensor.vars, List.length_map, List.length_append, List.length_take, hz,
      hpsi, LinShape.kCol]
    omega
  have hc : ∀ o pt i, ρ.val (row.coefficient o pt i) =
      (if l.oOmega = o ∧ Part.main = pt then
        (A.map fun t => ρ.val ((lay.onTable t).entry i)).sum else 0) +
      (if l.oU.oracle = o ∧ Part.main = pt then
        (B.map fun t => ρ.val ((l.oU.lay.onTable t).entry i)).sum else 0) := by
    intro o pt i
    rw [← hrow]
    unfold FoldedRow.addAll
    rw [coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]
  have ht : row.target = zeroE := by
    rw [← hrow]
    unfold FoldedRow.addAll
    rw [target_addLaid, target_addLaid]
  have tsO : Means.tableSize T l.oOmega .main = 2 ^ lay.bits := by
    unfold Means.tableSize; rw [if_pos hP.hasOmega, hP.bitsOmega]
  have tsU : Means.tableSize T l.oU.oracle .main = 2 ^ l.oU.lay.bits := by
    unfold Means.tableSize; rw [if_pos hP.hasU, hP.bitsU]
  have hmask : ∀ o, Means.onTable ρ T row m o .mask = 0 := by
    intro o
    unfold Means.onTable
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hc]; simp
  have hmain : ∀ o, Means.onTable ρ T row m o .main =
      (if l.oOmega = o then ∑ i ∈ Finset.range (2 ^ lay.bits),
        (A.map fun t => ρ.val ((lay.onTable t).entry i)).sum * m l.oOmega .main i else 0) +
      (if l.oU.oracle = o then ∑ i ∈ Finset.range (2 ^ l.oU.lay.bits),
        (B.map fun t => ρ.val ((l.oU.lay.onTable t).entry i)).sum * m l.oU.oracle .main i
        else 0) := by
    intro o
    unfold Means.onTable
    by_cases h1 : l.oOmega = o
    · subst h1
      have h2 : ¬ l.oU.oracle = l.oOmega := fun e => hP.two e.symm
      rw [if_pos rfl, if_neg h2, add_zero, tsO]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc]; simp [h2]
    · by_cases h2 : l.oU.oracle = o
      · subst h2
        rw [if_neg h1, if_pos rfl, zero_add, tsU]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hc]; simp [h1]
      · rw [if_neg h1, if_neg h2, add_zero]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hc]; simp [h1, h2]
  have hX : ∑ i ∈ Finset.range (2 ^ lay.bits),
      (A.map fun t => ρ.val ((lay.onTable t).entry i)).sum * m l.oOmega .main i =
      ∑ j ∈ Finset.range S.matrixRows, eqK (l.zFd.map ρ.val) j * omegaOf l lay m j := by
    rw [cut_laid_sum ρ lay _ rfl 0 S.kRow S.matrixRows A hA (by rw [hvA]; exact hP.roomOmega), hvA]
    refine Eq.trans ?_ (sum_below_len (2 ^ S.kRow) S.matrixRows hR
      fun j => eqK (l.zFd.map ρ.val) j * omegaOf l lay m j)
    refine Finset.sum_congr rfl fun j hj => ?_
    have e : j / 2 ^ 0 % 2 ^ S.kRow = j := by
      rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (Finset.mem_range.1 hj)]
    rw [e, entry_eq, ρ.one, one_mul]
    unfold omegaOf
    split_ifs <;> simp
  have hY : ∑ i ∈ Finset.range (2 ^ l.oU.lay.bits),
      (B.map fun t => ρ.val ((l.oU.lay.onTable t).entry i)).sum * m l.oU.oracle .main i =
      - ∑ j ∈ Finset.range S.matrixRows, ∑ t ∈ Finset.range (2 ^ S.kLo),
        eqK ((l.psiSh.take S.kLo).map ρ.val) t * eqK (l.zFd.map ρ.val) j *
          uOf l m (t + 2 ^ S.kLo * j) := by
    rw [cut_laid_sum ρ l.oU.lay _ rfl S.kLo S.kRow S.matrixRows B hB
      (by rw [hvB]; exact hP.roomU), hvB, Nat.pow_add, sum_blocks]
    refine Eq.trans ?_ (congrArg Neg.neg (sum_below_len (2 ^ S.kRow) S.matrixRows hR
      fun j => ∑ t ∈ Finset.range (2 ^ S.kLo),
        eqK ((l.psiSh.take S.kLo).map ρ.val) t * eqK (l.zFd.map ρ.val) j *
          uOf l m (t + 2 ^ S.kLo * j)))
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have e : ∀ t ∈ Finset.range (2 ^ S.kLo), (t + 2 ^ S.kLo * j) / 2 ^ S.kLo % 2 ^ S.kRow = j := by
      intro t ht
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (Finset.mem_range.1 ht),
        Nat.zero_add, Nat.mod_eq_of_lt (Finset.mem_range.1 hj)]
    by_cases hjR : j < S.matrixRows
    · rw [if_pos hjR, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [e t ht, if_pos hjR, entry_eq, neg_one, List.map_append,
        eqK_split _ _ S.kLo t j hlen (Finset.mem_range.1 ht)]
      unfold uOf
      ring
    · rw [if_neg hjR, neg_zero]
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [e t ht, if_neg hjR, zero_mul]
  have hval : Means.value ρ T row m =
      (∑ j ∈ Finset.range S.matrixRows, eqK (l.zFd.map ρ.val) j * omegaOf l lay m j) +
      - ∑ j ∈ Finset.range S.matrixRows, ∑ t ∈ Finset.range (2 ^ S.kLo),
        eqK ((l.psiSh.take S.kLo).map ρ.val) t * eqK (l.zFd.map ρ.val) j *
          uOf l m (t + 2 ^ S.kLo * j) := by
    unfold Means.value
    simp only [hmask, hmain, add_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
      if_pos (Finset.mem_range.2 (lt_of_has T _ _ hP.hasOmega)),
      if_pos (Finset.mem_range.2 (lt_of_has T _ _ hP.hasU)), hX, hY]
  unfold Means.Says
  rw [hval, ht, ρ.zero, ← sub_eq_add_neg, sub_eq_zero]

/-! ## The law of (fold) -/

/-- **The law of (fold)**: LAYS, MEANS and CATCHES joined. -/
theorem foldSound [Fintype K] : FoldSound ρ := by
  classical
  intro p d T m hS hP hgap
  refine le_trans (Finset.card_le_card ?_) (foldCatches p.S
    ((d.loc.psiSh.take p.S.kLo).map ρ.val) (omegaOf d.loc (linLayOmega d.st.codes p.S) m)
    (uOf d.loc m) (le_two_pow_ceilLog2 _) hgap)
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  obtain ⟨_, zs, r, d', hzs, hsp, hO, hU⟩ := hz
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨row, a, b, hf, h1, h2, h3⟩ := laysW ρ p _ d' r hS hsp
  have h1' : rowsOn d' d.loc.gOmega = rowsOn d d.loc.gOmega ++ [a] := h1
  have h2' : rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ [b] := h2
  have ha : Means.Says ρ T a m := hO a (by rw [h1']; simp)
  have hb : Means.Says ρ T b m := hU b (by rw [h2']; simp)
  have hP' : Placed T p.S { d.loc with zFd := zs } (linLayOmega d.st.codes p.S) :=
    ⟨hP.two, hP.hasOmega, hP.hasU, hP.bitsOmega, hP.bitsU, hP.roomOmega, hP.roomU⟩
  have h4 := (foldMeansW ρ T p.S _ _ row hf hP' m).1 (h3 T m ha hb)
  rw [← hzs]
  exact h4

/-- **The joined law of (fold).** -/
theorem foldLaw [Fintype K] : FoldLawOf ρ split := ⟨foldSound ρ, split_yes⟩

end Desc.K14.Law
