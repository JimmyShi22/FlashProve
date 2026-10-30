-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndsAt.lean: if every single equation of the list of
OnBytes/Tie/Pv/Tail/EndRows.lean holds at the arrays' entries, then the ties and the reads of the
relation after the smallness test's round hold, at the sizes read off the verifier's record and at
letters that are read off the same entries.

Definitions, statements and proofs.
Main names:
  `rows_iff`: every row of `rowsTail` is 0 at A if and only if every `tieRow` and every `readRow`
    is.
  `AtA`: the letters of the typed smallness test (Cb/Pv/Tail/Tables.lean) at `sizeOf tl` are read
    off the arrays' entries A: the symbols off the symbol arrays, the vector of reads off U3, the
    digits off ZZ at the verifier's columns, the tables' weights off the record's closed list, the
    drawn matrix off the record's drawn entries, by sign. Each is asked inside the sizes alone.
  `ties_of_rows`, `reads_of_rows`: the second and the third clause of `relOut`
    (Cb/Pv/Tail/Block.lean).
  `relOut_of_rows`: with the digits in their tables: `relOut`.
Limits: one way alone. Premises: the shapes fit the matrices (`Fits`); every table of the closed
list lies in U3. That the digits are in their tables is a premise of the last statement: it is the
lookup's matter. `AtA` is a premise on letters: who takes the letters from committed messages owes
it.
-/
import OnBytes.Tie.Pv.Tail.EndsRel
import OnBytes.Tie.Pv.Tail.EndSpread
import OnBytes.Tie.Pv.Tail.SizeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

open Finset Cb.Pv.Tail

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## The rows of the list -/

theorem readRows_iff (A : Nat → Nat → Nat → K) (tl : HTailF2) (pc : Nat) :
    ∀ (l : List (HFun × Nat)) (q : Nat), (∀ r ∈ readRowsFrom ρ tl pc q l, r.2 A = 0) ↔
      ∀ x ∈ l, ∀ u, readRow ρ tl x u A = 0
  | [], _ => ⟨fun _ _ h => absurd h (List.not_mem_nil), fun _ _ h => absurd h (List.not_mem_nil)⟩
  | x :: l, q => by
      have ih := readRows_iff A tl pc l (q + 1)
      rw [readRowsFrom_cons]
      constructor
      · intro h y hy u
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h _ (List.mem_append_left _ (List.mem_map.2 ⟨u, List.mem_finRange u, rfl⟩))
        · exact ih.1 (fun r hr => h r (List.mem_append_right _ hr)) y hy u
      · intro h r hr
        rcases List.mem_append.1 hr with hr | hr
        · obtain ⟨u, _, rfl⟩ := List.mem_map.1 hr
          exact h x (List.mem_cons_self) u
        · exact ih.2 (fun y hy => h y (List.mem_cons_of_mem _ hy)) r hr

/-- Every row of the list is 0 at A if and only if every single tie and every single equation of a
read is. -/
theorem rows_iff (A : Nat → Nat → Nat → K) (tl : HTailF2) (funs : Array HFun) (pc : Nat) :
    (∀ r ∈ rowsTail ρ tl funs pc, r.2 A = 0) ↔
      (∀ mu, mu < tl.NM → ∀ i' u, tieRow tl mu i' u A = 0) ∧
        ∀ x ∈ readsList tl funs, ∀ u, readRow ρ tl x u A = 0 := by
  constructor
  · intro h
    refine ⟨fun mu hmu i' u => ?_, (readRows_iff ρ A tl pc _ 0).1 fun r hr =>
      h r (List.mem_append_right _ hr)⟩
    exact h (pc + eTie tl mu i' u, tieRow tl mu i' u) (List.mem_append_left _
      (List.mem_flatMap.2 ⟨mu, List.mem_range.2 hmu, List.mem_flatMap.2 ⟨i', List.mem_finRange i',
        List.mem_map.2 ⟨u, List.mem_finRange u, rfl⟩⟩⟩))
  · rintro ⟨hT, hR⟩ r hr
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨mu, hmu, hr⟩ := List.mem_flatMap.1 hr
      obtain ⟨i', _, hr⟩ := List.mem_flatMap.1 hr
      obtain ⟨u, _, rfl⟩ := List.mem_map.1 hr
      exact hT mu (List.mem_range.1 hmu) i' u
    · exact (readRows_iff ρ A tl pc _ 0).2 hR r hr

/-! ## The letters, read off the arrays' entries -/

/-- the array that holds U3 -/
def u3Of (tl : HTailF2) : Nat := (tl.ix.U.getD 2 none).getD 0

/-- The letters are read off the arrays' entries A and the verifier's record. -/
structure AtA (tl : HTailF2) (Θ : TLetters K (sizeOf tl)) (x : Θ.X) (msg : Θ.M)
    (Z : Dig K (sizeOf tl).size) (β : Dr (sizeOf tl).size) (A : Nat → Nat → Nat → K) : Prop where
  phi : ∀ n Fn, tl.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
    Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE)
  sym : ∀ μ i' c, μ < tl.NM → i' < Alg.symRows (tl.mats.getD μ {}).m → c < (tl.mats.getD μ {}).k →
    Θ.sym msg μ i' c = A (tl.gtTree.getD μ 0) i' c
  u3 : ∀ y ∈ readsList tl tl.funs, ∀ d, d < (tl.mats.getD y.1.mat {}).k →
    Θ.u3 msg (posOf tl y.1 y.2 d) = A (u3Of tl) 0 (posOf tl y.1 y.2 d)
  zl : ∀ μ u i, Z.zl μ u i = A tl.ix.ZZ u ((tl.zzCol μ 0 0).getD 0 + i)
  zh : ∀ μ u i, Z.zh μ u i = A tl.ix.ZZ u ((tl.zzCol μ 1 0).getD 0 + i)
  th : ∀ μ u c, (((β μ u c).val : ℤ) : K) =
    signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD μ 0 + c) * tl.tau + u) 0)

theorem rad_eq (tl : HTailF2) : (((sizeOf tl).size.rad : ℕ) : ℤ) = (2 : ℤ) ^ 20 := by
  show ((radb : ℕ) : ℤ) = _
  norm_num [radb, lrad]

theorem lo_eq (tl : HTailF2) : (((sizeOf tl).size.lo : ℕ) : K) = (2 : K) ^ 10 := by
  show ((2 ^ t2D0 : ℕ) : K) = _
  norm_num [t2D0]

theorem beta_eq (tl : HTailF2) : (((sizeOf tl).size.beta : ℕ) : K) = (2 : K) ^ 17 := by
  show ((2 ^ lbz : ℕ) : K) = _
  norm_num [lbz]

/-- A single tie, with the numbers of rows of cells and of columns as letters. -/
def tieN (A : Nat → Nat → Nat → K) (tl : HTailF2) (mu m k u i' : Nat) : K :=
  Alg.pack ((2 : ℤ) ^ 20) (fun i : Fin m => A tl.ix.ZZ u ((tl.zzCol mu 0 0).getD 0 + i) +
      (2 : K) ^ 10 * A tl.ix.ZZ u ((tl.zzCol mu 1 0).getD 0 + i) - (2 : K) ^ 17) i' -
    ∑ c : Fin k, signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau + u) 0) *
      A (tl.gtTree.getD mu 0) i' c

variable {ρ}

/-- The ties of the relation after the round. -/
theorem ties_of_rows {tl : HTailF2} {Θ : TLetters K (sizeOf tl)} {x : Θ.X} {msg : Θ.M}
    {Z : Dig K (sizeOf tl).size} {β : Dr (sizeOf tl).size} {A : Nat → Nat → Nat → K}
    (at' : AtA ρ tl Θ x msg Z β A) (hfit : Fits tl)
    (hT : ∀ mu, mu < tl.NM → ∀ i' u, tieRow tl mu i' u A = 0)
    (μ : Fin (sizeOf tl).size.NM) (u : Fin (sizeOf tl).size.tau)
    (i' : Fin (Alg.symRows ((sizeOf tl).size.m μ))) :
    ∑ c, (((β μ u c).val : ℤ) : K) * Θ.letters.sym msg μ i' c =
      Alg.pack ((sizeOf tl).size.rad : ℤ) (comb Z μ u) i' := by
  have hμ : μ.val < tl.NM := μ.isLt
  obtain ⟨fm, fk⟩ := hfit μ.val hμ
  have h1 : ∀ j : Fin (Alg.symRows (tl.shp.getD μ.val {}).m),
      tieN A tl μ.val (tl.shp.getD μ.val {}).m (tl.shp.getD μ.val {}).k u.val j.val = 0 :=
    fun j => hT μ.val hμ j u
  rw [fm, fk] at h1
  have h2 := h1 i'
  unfold tieN at h2
  rw [sub_eq_zero] at h2
  rw [rad_eq]
  have e1 : comb Z μ u = fun i : Fin (tl.mats.getD μ.val {}).m =>
      A tl.ix.ZZ u ((tl.zzCol μ.val 0 0).getD 0 + i) +
        (2 : K) ^ 10 * A tl.ix.ZZ u ((tl.zzCol μ.val 1 0).getD 0 + i) - (2 : K) ^ 17 := by
    funext i
    show Z.zl μ u i + (((sizeOf tl).size.lo : ℕ) : K) * Z.zh μ u i -
      (((sizeOf tl).size.beta : ℕ) : K) = _
    rw [at'.zl, at'.zh, lo_eq, beta_eq]
  rw [e1]
  refine Eq.trans ?_ h2.symm
  refine sum_congr rfl fun c _ => ?_
  rw [at'.th]
  show _ * Θ.sym msg μ i' c = _
  rw [at'.sym _ _ _ hμ i'.isLt c.isLt]

/-! ## The reads -/

theorem dec_some {t : TSize} {μ r n sg : ℕ} {T : Tab} (h : t.dec μ r = some (n, T, sg)) :
    t.tabs[n]? = some T ∧ T.mat = μ ∧ sg < t.m μ / T.len := by
  unfold TSize.dec at h
  cases hT : t.tabs[r / (t.m μ + 1)]? with
  | none => simp only [hT] at h; cases h
  | some T' =>
    simp only [hT] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hT, hc.1, hc.2⟩

/-- The column of ZZ of row i of cells, from that of row 0. -/
theorem zzCol_add (tl : HTailF2) {mu p i : Nat} (hmu : mu < tl.NM) (hp : p ≤ 1)
    (hi : i < (tl.mats.getD mu {}).m) :
    (tl.zzCol mu p i).getD 0 = (tl.zzCol mu p 0).getD 0 + i := by
  have h0 : 0 < (tl.mats.getD mu {}).m := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  unfold HTailF2.zzCol
  rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hmu, hp⟩, hi⟩),
    if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hmu, hp⟩, h0⟩)]
  rfl

/-- The place of a table's entry. -/
theorem posOf_eq (tl : HTailF2) (Fn : HFun) {sg d : Nat} (hm : Fn.mat < tl.NM)
    (hs : sg < (tl.mats.getD Fn.mat {}).m / Fn.len) (hd : d < (tl.mats.getD Fn.mat {}).k) :
    posOf tl Fn sg d = Fn.start + d * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg := by
  have hl : Fn.len ≠ 0 := by
    intro h0
    rw [h0, Nat.div_zero] at hs
    exact absurd hs (Nat.not_lt_zero _)
  unfold posOf HTailF2.tabAt
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨hm, hl⟩)]
  dsimp only
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hd, hs⟩)]
  rfl

/-- The reads of the relation after the round. -/
theorem reads_of_rows {tl : HTailF2} {Θ : TLetters K (sizeOf tl)} {x : Θ.X} {msg : Θ.M}
    {Z : Dig K (sizeOf tl).size} {β : Dr (sizeOf tl).size} {A : Nat → Nat → Nat → K}
    (at' : AtA ρ tl Θ x msg Z β A) (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (hR : ∀ y ∈ readsList tl tl.funs, ∀ u, readRow ρ tl y u A = 0)
    (μ : Fin (sizeOf tl).size.NM) (u : Fin (sizeOf tl).size.tau)
    (r : Fin ((sizeOf tl).size.nr μ)) :
    ∑ c, (((β μ u c).val : ℤ) : K) * Θ.letters.tab msg μ r c =
      ∑ i, Θ.letters.w x μ r i * comb Z μ u i := by
  show ∑ c : Fin (tl.mats.getD μ.val {}).k,
      (((β μ u c).val : ℤ) : K) * tabOf (sizeOf tl) (Θ.u3 msg) μ r c =
    ∑ i : Fin (tl.mats.getD μ.val {}).m, wOf (sizeOf tl) (Θ.phi x) μ r i * comb Z μ u i
  cases hd : (sizeOf tl).dec μ r with
  | none =>
    have e1 : ∀ c : ℕ, tabOf (sizeOf tl) (Θ.u3 msg) μ r c = 0 := fun c => by
      unfold tabOf
      rw [hd]
    have e2 : ∀ i : ℕ, wOf (sizeOf tl) (Θ.phi x) μ r i = 0 := fun i => by
      unfold wOf
      rw [hd]
    simp only [e1, e2, mul_zero, zero_mul, sum_const_zero]
  | some z =>
    obtain ⟨n, T, sg⟩ := z
    obtain ⟨hT, hm, hs⟩ := dec_some hd
    have hT' : (tl.funs.toList.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))[n]? =
        some T := hT
    rw [List.getElem?_map] at hT'
    obtain ⟨Fn, hFn, rfl⟩ := Option.map_eq_some_iff.1 hT'
    have hm' : Fn.mat = μ.val := hm
    have hs' : sg < (tl.mats.getD μ.val {}).m / Fn.len := hs
    have hmem : Fn ∈ tl.funs.toList := List.mem_of_getElem? hFn
    have hμ : μ.val < tl.NM := μ.isLt
    have hx : (Fn, sg) ∈ readsList tl tl.funs :=
      (mem_readsList tl tl.funs Fn sg).2
        ⟨hmem, by rw [hm']; exact hμ, Or.inr (htree Fn hmem), by rw [hm']; exact hs'⟩
    have hl : 0 < Fn.len := by
      rcases Nat.eq_zero_or_pos Fn.len with h0 | h0
      · rw [h0, Nat.div_zero] at hs'
        exact absurd hs' (Nat.not_lt_zero _)
      · exact h0
    have hlen : sg * Fn.len + Fn.len ≤ (tl.mats.getD μ.val {}).m := by
      have h5 := (Nat.le_div_iff_mul_le hl).1 (Nat.succ_le_of_lt hs')
      rw [Nat.succ_mul] at h5
      exact h5
    -- the row, with the matrix's number written as μ
    have h0 : ∑ j : Fin Fn.len, ρ.val (Fn.phi.getD j zeroE) *
          (A tl.ix.ZZ u ((tl.zzCol μ.val 0 (sg * Fn.len)).getD 0 + j) +
            (2 : K) ^ 10 * A tl.ix.ZZ u ((tl.zzCol μ.val 1 (sg * Fn.len)).getD 0 + j) -
            (2 : K) ^ 17) =
        ∑ d ∈ range (tl.mats.getD μ.val {}).k,
          signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD μ.val 0 + d) * tl.tau + u) 0) *
            A (uOf tl Fn) 0 (posOf tl Fn sg d) := by
      have h := hR (Fn, sg) hx u
      unfold readRow readGap thOf at h
      rw [sub_eq_zero] at h
      have h' := h.trans (Fin.sum_univ_eq_sum_range (fun d =>
        signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD Fn.mat 0 + d) * tl.tau + u) 0) *
          A (uOf tl Fn) 0 (posOf tl Fn sg d)) (tl.mats.getD Fn.mat {}).k)
      simp only [hm'] at h'
      exact h'
    have eT : ∀ c : Fin (tl.mats.getD μ.val {}).k,
        tabOf (sizeOf tl) (Θ.u3 msg) μ r c = A (uOf tl Fn) 0 (posOf tl Fn sg c) := by
      intro c
      unfold tabOf
      rw [hd]
      show Θ.u3 msg (Fn.start + c * ((tl.mats.getD μ.val {}).m / Fn.len) + sg) = _
      have hp : posOf tl Fn sg c =
          Fn.start + c * ((tl.mats.getD μ.val {}).m / Fn.len) + sg := by
        rw [posOf_eq tl Fn (by rw [hm']; exact hμ) (by rw [hm']; exact hs')
          (by rw [hm']; exact c.isLt), hm']
      rw [← hp, at'.u3 (Fn, sg) hx c (by show (c : ℕ) < (tl.mats.getD Fn.mat {}).k
                                         rw [hm']; exact c.isLt)]
      unfold uOf u3Of
      rw [htree Fn hmem]
    have eW : ∀ i : ℕ, wOf (sizeOf tl) (Θ.phi x) μ r i =
        if sg * Fn.len ≤ i ∧ i < sg * Fn.len + Fn.len then Θ.phi x n (i - sg * Fn.len) else 0 := by
      intro i
      unfold wOf
      rw [hd]
    have eC : ∀ i : Fin (tl.mats.getD μ.val {}).m, comb Z μ u i =
        A tl.ix.ZZ u ((tl.zzCol μ.val 0 0).getD 0 + i) +
          (2 : K) ^ 10 * A tl.ix.ZZ u ((tl.zzCol μ.val 1 0).getD 0 + i) - (2 : K) ^ 17 := by
      intro i
      show Z.zl μ u i + (((sizeOf tl).size.lo : ℕ) : K) * Z.zh μ u i -
        (((sizeOf tl).size.beta : ℕ) : K) = _
      rw [at'.zl, at'.zh, lo_eq, beta_eq]
    have eR : ∑ i : Fin (tl.mats.getD μ.val {}).m,
          wOf (sizeOf tl) (Θ.phi x) μ r i * comb Z μ u i =
        ∑ j ∈ range Fn.len, Θ.phi x n j *
          (A tl.ix.ZZ u ((tl.zzCol μ.val 0 0).getD 0 + (sg * Fn.len + j)) +
            (2 : K) ^ 10 * A tl.ix.ZZ u ((tl.zzCol μ.val 1 0).getD 0 + (sg * Fn.len + j)) -
            (2 : K) ^ 17) := by
      rw [← sum_stretch (tl.mats.getD μ.val {}).m (sg * Fn.len) Fn.len hlen (Θ.phi x n)
        (fun i => A tl.ix.ZZ u ((tl.zzCol μ.val 0 0).getD 0 + i) +
          (2 : K) ^ 10 * A tl.ix.ZZ u ((tl.zzCol μ.val 1 0).getD 0 + i) - (2 : K) ^ 17)]
      exact sum_congr rfl fun i _ => by rw [eW, eC]
    have hlt : sg * Fn.len < (tl.mats.getD μ.val {}).m := by omega
    have eL : ∑ c : Fin (tl.mats.getD μ.val {}).k,
          (((β μ u c).val : ℤ) : K) * tabOf (sizeOf tl) (Θ.u3 msg) μ r c =
        ∑ d ∈ range (tl.mats.getD μ.val {}).k,
          signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD μ.val 0 + d) * tl.tau + u) 0) *
            A (uOf tl Fn) 0 (posOf tl Fn sg d) := by
      rw [← Fin.sum_univ_eq_sum_range (fun d =>
        signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD μ.val 0 + d) * tl.tau + u) 0) *
          A (uOf tl Fn) 0 (posOf tl Fn sg d)) (tl.mats.getD μ.val {}).k]
      exact sum_congr rfl fun c _ => by rw [eT c, at'.th]
    rw [eL, eR, ← h0, Finset.sum_range]
    refine sum_congr rfl fun j _ => ?_
    rw [at'.phi n Fn hFn j j.isLt, zzCol_add tl hμ (Nat.zero_le 1) hlt,
      zzCol_add tl hμ (Nat.le_refl 1) hlt, Nat.add_assoc, Nat.add_assoc]

/-- With the digits in their tables: the relation after the round. -/
theorem relOut_of_rows {tl : HTailF2} {Θ : TLetters K (sizeOf tl)} {x : Θ.X} {msg : Θ.M}
    {Z : Dig K (sizeOf tl).size} {β : Dr (sizeOf tl).size} {A : Nat → Nat → Nat → K} (pc : Nat)
    (at' : AtA ρ tl Θ x msg Z β A) (hfit : Fits tl)
    (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (hdig : ∀ μ u i, Cb.Rng.InTab (sizeOf tl).size.lo (Z.zl μ u i) ∧
      Cb.Rng.InTab (sizeOf tl).size.hi (Z.zh μ u i))
    (h : ∀ r ∈ rowsTail ρ tl tl.funs pc, r.2 A = 0) : relOut Θ.letters x β msg Z := by
  obtain ⟨hT, hR⟩ := (rows_iff ρ A tl tl.funs pc).1 h
  exact ⟨hdig, ties_of_rows at' hfit hT, reads_of_rows at' htree hR⟩

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.reads_of_rows
#print axioms OnBytes.Tie.Pv.Tail.Port.relOut_of_rows
#print axioms OnBytes.Tie.Pv.Tail.Port.rows_iff
#print axioms OnBytes.Tie.Pv.Tail.Port.ties_of_rows
