-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByNext.lean: proof of `Spec.next_tab` (RunBySpec.lean). A
prover's state after a code switch is defined twice: as lists of triples of words (`nextBy` at
`Seams.lib`, Run.lean) and as functions from an index to the field (`aNext`,
Johnson/Desc/K12/Honest/Stages.lean). `Tab s last P p` (RunBySpec.lean) says that each of the six
lists of p is the matching function of P, encoded as words below the prime.

  `nextBy_tab`   the proof: under the hypotheses of `Spec.next_tab`, if `Tab` holds before the
                 switch, it holds after it
  `nx_fresh`     `freshRows` (Fmt/M1Fold.lean), cut into rows, is the packing `packedN`, encoded,
                 where the rows have room and the coefficients' words are below the prime
  `ride_fresh`, `nx_riders_mid`   what `ridersBy` (Run.lean) returns at a stage that is not the last
  `nx_riders_last`   what it returns at the last stage
  `nx_met`       at any two stages some random values and lists satisfy `Tab` and `CoinTie` together

By what. Two triples of words below the prime are equal if they decode to the same field element
(`eq_ofE`, RunByTab.lean). Sections 1 to 7 prepare this for the six lists; section 8 puts them
together. The fresh table rests on a law of the library: where the rows have room, `freshRows` at a
structure U of coefficients decodes, entry by entry, to the packing of `coefU U` (`fresh_packed`,
Johnson/Prover/Link/FoldPairs.lean). `nx_fresh` (section 6) is its form on words, and `ride_fresh`
applies it to `ridersBy`.

Limits.
- The hiding polynomial's coefficients must be words below the prime (second clause of `HideTie`):
  `freshRows` (Fmt/M1Fold.lean) copies some of them into the table unchanged. The sampled elements
  need not be.
- Of the five clauses of `switchFitB` only the first two are used.
- The equation holds for all values of its variables, also for states that no run reaches.
- Two definitions give the same words. Nothing follows on what a verifier decides.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunByTab
import Johnson.Prover.Link.FoldPairs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Stage ent fitL fold1L foldLow foldRows csOwnG)
open Fmt.M1.Own (PSt rowsOf riders coins hideOf)
open Fmt.M1.FoldOwn (Hide freshRow freshRows)
open OnBytes.Slice (GE Sg ofE toE vec lst eqW okE_addE okE_zeroE fold1L_cons_cons toE_foldV
  vec_toArray eqW_congr lst_take sum_range_cube eqW_rowNo rowNo_testBit readE_ofTriple preP)
open Johnson.Prover.Link (PS BCoins wr length_wr lst_wr okE_wr okE_ofE μOf φOf ρOf ψOf foldMsg
  foldTl gMain gMask nextPS packedN coefU fresh_packed)
open H2K.Pub (sgOf)

/-! ## 1 Encoded lists -/

theorem nx_wr_add (a b : ℕ) (f : ℕ → GE) : wr (a + b) f = wr a f ++ wr b fun i => f (a + i) := by
  unfold wr
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem nx_getD_wr (n : ℕ) (f : ℕ → GE) (j : ℕ) (h : j < n) :
    (wr n f).getD j Fld.zeroE = ofE (f j) :=
  getD_range n _ _ j h

/-- If c q is `ofE (f q)` for every q, the list of the first n values of c is `wr n f`. -/
theorem nx_map_wr (n : ℕ) (c : ℕ → E) (f : ℕ → GE) (h : ∀ q, c q = ofE (f q)) :
    (List.range n).map c = wr n f :=
  congrArg (fun c => (List.range n).map c) (funext h)

theorem nx_fitL_wr (m n : ℕ) (f : ℕ → GE) (h : m ≤ n) : fitL Fld.zeroE m (wr n f) = wr m f := by
  unfold fitL
  rw [length_wr, Nat.sub_eq_zero_of_le h, List.replicate_zero, List.append_nil]
  unfold wr
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem nx_ent_toArray (l : List E) (i : ℕ) : ent l.toArray i = l.getD i Fld.zeroE := by
  unfold ent
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- `rowsOf` of an encoded table of nr * m entries: row b has the entries at the indices b + nr * c.
-/
theorem nx_rows_of (nr m n : ℕ) (hnr : 0 < nr) (hn : nr * m = n) (G G' : ℕ → GE)
    (h : ∀ i, i < n → G i = G' i) :
    rowsOf nr (wr n G).toArray = (List.range nr).map fun b => wr m fun c => G' (b + nr * c) := by
  subst hn
  unfold rowsOf
  rw [List.size_toArray, length_wr, Nat.mul_div_cancel_left _ hnr]
  refine List.map_congr_left fun b hb => ?_
  show (List.range m).map (fun c => ent (wr (nr * m) G).toArray (b + nr * c)) =
    (List.range m).map fun c => ofE (G' (b + nr * c))
  refine List.map_congr_left fun c hc => ?_
  have hi := tab_idx_lt nr m b c (List.mem_range.1 hb) (List.mem_range.1 hc)
  rw [nx_ent_toArray, nx_getD_wr _ _ _ hi, h _ hi]

/-! ## 2 A fold's words are below the prime -/

theorem nx_ok_fold1L (x : E) : ∀ (T : List E) (e : E), e ∈ fold1L .two x T → Fld.two.okE e = true
  | [], e, he => by
    have h : fold1L .two x [] = [] := rfl
    rw [h] at he
    cases he
  | [a], e, he => by
    have h : fold1L .two x [a] =
        [Fld.two.addE a (Fld.two.mulEF x (Fld.two.subE Fld.zeroE a))] := rfl
    rw [h, List.mem_singleton] at he
    rw [he]
    exact okE_addE _ _
  | a :: b :: T, e, he => by
    rw [fold1L_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact okE_addE _ _
    · exact nx_ok_fold1L x T e he

theorem nx_ok_foldl : ∀ (g T : List E), (∀ e ∈ T, Fld.two.okE e = true) →
    ∀ e ∈ g.foldl (fun T x => fold1L .two x T) T, Fld.two.okE e = true
  | [], _, h => h
  | x :: g, T, _ => by
    rw [List.foldl_cons]
    exact nx_ok_foldl g _ (nx_ok_fold1L x T)

theorem nx_ok_getD (l : List E) (h : ∀ e ∈ l, Fld.two.okE e = true) (i : ℕ) :
    Fld.two.okE (l.getD i Fld.zeroE) = true := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    exact okE_zeroE

/-- Folding a vector of words below the prime gives words below the prime. The hypothesis is needed
only for g = []: then the result is the first entry. -/
theorem nx_ok_foldV (g v : List E) (h : ∀ e ∈ v, Fld.two.okE e = true) :
    Fld.two.okE (Fmt.M1.foldV .two g v.toArray) = true := by
  unfold Fmt.M1.foldV foldLow
  rw [nx_ent_toArray]
  exact nx_ok_getD _ (nx_ok_foldl g _ h) 0

/-- `foldRows` of 2 ^ n encoded rows is the list of the rows' weighted sums, encoded. The weights
are `eqW` at the point that g decodes to. -/
theorem nx_foldRows (g : List E) (n : ℕ) (hg : g.length = n) (m : ℕ) (F : ℕ → ℕ → GE) :
    foldRows .two g ((List.range (2 ^ n)).map fun b => wr m (F b)) m =
      wr m fun c => ∑ b ∈ Finset.range (2 ^ n), eqW n (lst g) b * F b c := by
  subst hg
  unfold foldRows
  refine List.map_congr_left fun c hc => ?_
  have col : (((List.range (2 ^ g.length)).map fun b => wr m (F b)).map
      fun r => r.getD c Fld.zeroE) = wr (2 ^ g.length) fun b => F b c := by
    rw [List.map_map]
    exact List.map_congr_left fun b _ => nx_getD_wr m (F b) c (List.mem_range.1 hc)
  rw [col]
  refine eq_ofE (nx_ok_foldV g _ (okE_wr _ _)) ?_
  rw [toE_foldV]
  exact Finset.sum_congr rfl fun b hb => by
    rw [vec_toArray, lst_wr _ _ _ (Finset.mem_range.1 hb)]

/-- `nx_foldRows` for `g.take h`: the weights use the point's first h coordinates. -/
theorem nx_foldRows_take (g : List E) (h : ℕ) (hh : h ≤ g.length) (m : ℕ) (F : ℕ → ℕ → GE) :
    foldRows .two (g.take h) ((List.range (2 ^ h)).map fun b => wr m (F b)) m =
      wr m fun c => ∑ b ∈ Finset.range (2 ^ h), eqW h (lst g) b * F b c := by
  rw [nx_foldRows (g.take h) h (by rw [List.length_take]; omega) m F]
  exact wr_congr _ _ _ fun c _ => Finset.sum_congr rfl fun b _ => by
    rw [eqW_congr h _ (lst g) b fun t ht => lst_take h g t ht]

/-! ## 3 `foldMsg` and `foldTl` as sums over the rows' numbers -/

section Folded
variable (s : Sg) (P : PS) (z : ℕ → GE)

theorem nx_msg_main (c : Fin s.C.l) :
    foldMsg s (μOf s P) (φOf s P) (fun t => z t.val) (.inl c) =
      ∑ b ∈ Finset.range (2 ^ (s.h + s.g)),
        eqW (s.h + s.g) z b * P.tabM (b + 2 ^ (s.h + s.g) * c.val) := by
  rw [sum_range_cube]
  show Cb.foldV (fun t : Fin (s.h + s.g) => z t.val) (fun x => μOf s P (.inl x)) c = _
  unfold Cb.foldV
  exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo]; rfl

theorem nx_msg_mask (c : Fin s.Z.l) :
    foldMsg s (μOf s P) (φOf s P) (fun t => z t.val) (.inr (.inl c)) =
      ∑ b ∈ Finset.range (2 ^ s.h), eqW s.h z b * P.tabZ (b + 2 ^ s.h * c.val) := by
  rw [sum_range_cube]
  show Cb.foldV (preP s fun t => z t.val) (fun x => μOf s P (.inr x)) c = _
  unfold Cb.foldV
  exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo]; rfl

theorem nx_msg_fresh (c : Fin s.Z.l) :
    foldMsg s (μOf s P) (φOf s P) (fun t => z t.val) (.inr (.inr c)) =
      ∑ b ∈ Finset.range (2 ^ s.h), eqW s.h z b * P.fM b c.val := by
  rw [sum_range_cube]
  show Cb.foldV (preP s fun t => z t.val) (φOf s P) c = _
  unfold Cb.foldV
  exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo]; rfl

theorem nx_tl_main (q : Fin s.C.r) :
    foldTl s (ρOf s P) (ψOf s P) (fun t => z t.val) (.inl q) =
      ∑ b ∈ Finset.range (2 ^ (s.h + s.g)), eqW (s.h + s.g) z b * P.tM b q.val := by
  rw [sum_range_cube]
  show Cb.foldV (fun t : Fin (s.h + s.g) => z t.val) (fun x => ρOf s P (.inl x)) q = _
  unfold Cb.foldV
  exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo]; rfl

theorem nx_tl_mask (q : Fin s.Z.r) :
    foldTl s (ρOf s P) (ψOf s P) (fun t => z t.val) (.inr (.inl q)) =
      ∑ b ∈ Finset.range (2 ^ s.h), eqW s.h z b * P.tZ b q.val := by
  rw [sum_range_cube]
  show Cb.foldV (preP s fun t => z t.val) (fun x => ρOf s P (.inr x)) q = _
  unfold Cb.foldV
  exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo]; rfl

theorem nx_tl_fresh (q : Fin s.Z.r) :
    foldTl s (ρOf s P) (ψOf s P) (fun t => z t.val) (.inr (.inr q)) =
      ∑ b ∈ Finset.range (2 ^ s.h), eqW s.h z b * P.fT b q.val := by
  rw [sum_range_cube]
  show Cb.foldV (preP s fun t => z t.val) (ψOf s P) q = _
  unfold Cb.foldV
  exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo]; rfl

end Folded

/-! ## 4 `gMain` and `gMask`, range by range -/

section Lay
variable (s : Sg) (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE)

theorem nx_gMain (i : ℕ) (h : i < s.C.l) : gMain s μ' i = μ' (.inl ⟨i, h⟩) := by
  unfold gMain
  exact dif_pos h

theorem nx_gMask1 (i : ℕ) (h : i < s.Z.l) : gMask s μ' tl fr i = μ' (.inr (.inl ⟨i, h⟩)) := by
  unfold gMask
  exact dif_pos h

theorem nx_gMask2 (n i : ℕ) (e : n = s.Z.l + i) (h : i < s.Z.l) :
    gMask s μ' tl fr n = μ' (.inr (.inr ⟨i, h⟩)) := by
  subst e
  have e' : s.Z.l + i - s.Z.l = i := by omega
  unfold gMask
  rw [dif_neg (show ¬ s.Z.l + i < s.Z.l by omega),
    dif_pos (show s.Z.l + i - s.Z.l < s.Z.l by omega)]
  exact congrArg (fun x => μ' (.inr (.inr x))) (Fin.ext e')

theorem nx_gMask3 (n i : ℕ) (e : n = 2 * s.Z.l + i) (h : i < s.C.r) :
    gMask s μ' tl fr n = tl (.inl ⟨i, h⟩) := by
  subst e
  have e' : 2 * s.Z.l + i - 2 * s.Z.l = i := by omega
  unfold gMask
  rw [dif_neg (show ¬ 2 * s.Z.l + i < s.Z.l by omega),
    dif_neg (show ¬ 2 * s.Z.l + i - s.Z.l < s.Z.l by omega),
    dif_pos (show 2 * s.Z.l + i - 2 * s.Z.l < s.C.r by omega)]
  exact congrArg (fun x => tl (.inl x)) (Fin.ext e')

theorem nx_gMask4 (n i : ℕ) (e : n = 2 * s.Z.l + s.C.r + i) (h : i < s.Z.r) :
    gMask s μ' tl fr n = tl (.inr (.inl ⟨i, h⟩)) := by
  subst e
  have e' : 2 * s.Z.l + s.C.r + i - (2 * s.Z.l + s.C.r) = i := by omega
  unfold gMask
  rw [dif_neg (show ¬ 2 * s.Z.l + s.C.r + i < s.Z.l by omega),
    dif_neg (show ¬ 2 * s.Z.l + s.C.r + i - s.Z.l < s.Z.l by omega),
    dif_neg (show ¬ 2 * s.Z.l + s.C.r + i - 2 * s.Z.l < s.C.r by omega),
    dif_pos (show 2 * s.Z.l + s.C.r + i - (2 * s.Z.l + s.C.r) < s.Z.r by omega)]
  exact congrArg (fun x => tl (.inr (.inl x))) (Fin.ext e')

theorem nx_gMask5 (n i : ℕ) (e : n = 2 * s.Z.l + s.C.r + s.Z.r + i) (h : i < s.Z.r) :
    gMask s μ' tl fr n = tl (.inr (.inr ⟨i, h⟩)) := by
  subst e
  have e' : 2 * s.Z.l + s.C.r + s.Z.r + i - (2 * s.Z.l + s.C.r + s.Z.r) = i := by omega
  unfold gMask
  rw [dif_neg (show ¬ 2 * s.Z.l + s.C.r + s.Z.r + i < s.Z.l by omega),
    dif_neg (show ¬ 2 * s.Z.l + s.C.r + s.Z.r + i - s.Z.l < s.Z.l by omega),
    dif_neg (show ¬ 2 * s.Z.l + s.C.r + s.Z.r + i - 2 * s.Z.l < s.C.r by omega),
    dif_neg (show ¬ 2 * s.Z.l + s.C.r + s.Z.r + i - (2 * s.Z.l + s.C.r) < s.Z.r by omega),
    dif_pos (show 2 * s.Z.l + s.C.r + s.Z.r + i - (2 * s.Z.l + s.C.r + s.Z.r) < s.Z.r by omega)]
  exact congrArg (fun x => tl (.inr (.inr x))) (Fin.ext e')

theorem nx_gMask6 (n : ℕ) (h : 2 * s.Z.l + s.C.r + 2 * s.Z.r ≤ n) : gMask s μ' tl fr n = fr n := by
  unfold gMask
  rw [dif_neg (show ¬ n < s.Z.l by omega), dif_neg (show ¬ n - s.Z.l < s.Z.l by omega),
    dif_neg (show ¬ n - 2 * s.Z.l < s.C.r by omega),
    dif_neg (show ¬ n - (2 * s.Z.l + s.C.r) < s.Z.r by omega),
    dif_neg (show ¬ n - (2 * s.Z.l + s.C.r + s.Z.r) < s.Z.r by omega)]

end Lay

/-! ## 5 The two new tables of words -/

section Tables
-- every theorem of this section takes hg: g has s.h + s.g entries
variable (s : Sg) (P : PS) (g : List E) (hg : g.length = s.h + s.g)
include hg

/-- `rowsOf` of the folded main rows is `gMain` of `foldMsg`, encoded. -/
theorem nx_main (nr m : ℕ) (hA : 2 ^ nr * m = s.C.l) (M : List (List E))
    (hM : M = (List.range (2 ^ (s.h + s.g))).map fun b =>
      wr s.C.l fun c => P.tabM (b + 2 ^ (s.h + s.g) * c)) :
    rowsOf (2 ^ nr) (foldRows .two g M s.C.l).toArray =
      (List.range (2 ^ nr)).map fun b => wr m fun c =>
        gMain s (foldMsg s (μOf s P) (φOf s P) fun t => lst g t.val) (b + 2 ^ nr * c) := by
  subst hM
  rw [nx_foldRows g _ hg s.C.l fun b c => P.tabM (b + 2 ^ (s.h + s.g) * c)]
  exact nx_rows_of _ _ _ (Nat.two_pow_pos _) hA _ _ fun i hi =>
    ((nx_gMain s _ i hi).trans (nx_msg_main s P (lst g) ⟨i, hi⟩)).symm

/-- The list that `csOwnG` builds for the new mask table is `gMask`, encoded: the two folded mask
messages, the three folded tails, the free entries, the pad. -/
theorem nx_mask_list (fr : ℕ → GE) (N : ℕ) (hB : 2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ N)
    (W Pf Rh Sg' Pi : List (List E))
    (hW : W = (List.range (2 ^ s.h)).map fun b => wr s.Z.l fun c => P.tabZ (b + 2 ^ s.h * c))
    (hPf : Pf = (List.range (2 ^ s.h)).map fun b => wr s.Z.l (P.fM b))
    (hRh : Rh = (List.range (2 ^ (s.h + s.g))).map fun b => wr s.C.r (P.tM b))
    (hSg : Sg' = (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.tZ b))
    (hPi : Pi = (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.fT b))
    (free : List E) (pad : E)
    (hfree : free = wr N fun n => fr (2 * s.Z.l + s.C.r + 2 * s.Z.r + n))
    (hpad : pad = ofE (fr (N - 1))) :
    foldRows .two (g.take s.h) W s.Z.l ++ foldRows .two (g.take s.h) Pf s.Z.l ++
          foldRows .two g Rh s.C.r ++ foldRows .two (g.take s.h) Sg' s.Z.r ++
          foldRows .two (g.take s.h) Pi s.Z.r ++
        fitL Fld.zeroE (N - (foldRows .two (g.take s.h) W s.Z.l ++
          foldRows .two (g.take s.h) Pf s.Z.l ++ foldRows .two g Rh s.C.r ++
          foldRows .two (g.take s.h) Sg' s.Z.r ++
          foldRows .two (g.take s.h) Pi s.Z.r).length - 1) free ++ [pad] =
      wr N (gMask s (foldMsg s (μOf s P) (φOf s P) fun t => lst g t.val)
        (foldTl s (ρOf s P) (ψOf s P) fun t => lst g t.val) fr) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = 2 * s.Z.l + s.C.r + 2 * s.Z.r + m + 1 :=
    ⟨N - (2 * s.Z.l + s.C.r + 2 * s.Z.r) - 1, by omega⟩
  subst hW hPf hRh hSg hPi hfree hpad
  have hh : s.h ≤ g.length := by omega
  have hl : ∀ A1 A2 A3 A4 A5 : List E, A1.length = s.Z.l → A2.length = s.Z.l →
      A3.length = s.C.r → A4.length = s.Z.r → A5.length = s.Z.r →
      2 * s.Z.l + s.C.r + 2 * s.Z.r + m + 1 - (A1 ++ A2 ++ A3 ++ A4 ++ A5).length - 1 = m := by
    intro A1 A2 A3 A4 A5 h1 h2 h3 h4 h5
    simp only [List.length_append]
    omega
  have eN : 2 * s.Z.l + s.C.r + 2 * s.Z.r + m + 1 =
      s.Z.l + s.Z.l + s.C.r + s.Z.r + s.Z.r + m + 1 := by omega
  rw [nx_foldRows_take g s.h hh s.Z.l fun b c => P.tabZ (b + 2 ^ s.h * c),
    nx_foldRows_take g s.h hh s.Z.l P.fM, nx_foldRows g _ hg s.C.r P.tM,
    nx_foldRows_take g s.h hh s.Z.r P.tZ, nx_foldRows_take g s.h hh s.Z.r P.fT,
    hl _ _ _ _ _ (length_wr _ _) (length_wr _ _) (length_wr _ _) (length_wr _ _) (length_wr _ _),
    nx_fitL_wr m (2 * s.Z.l + s.C.r + 2 * s.Z.r + m + 1) _ (by omega), eN, nx_wr_add _ 1,
    nx_wr_add _ m, nx_wr_add _ s.Z.r, nx_wr_add _ s.Z.r, nx_wr_add _ s.C.r,
    nx_wr_add s.Z.l s.Z.l]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact wr_congr _ _ _ fun c hc =>
      ((nx_gMask1 s _ _ fr c hc).trans (nx_msg_mask s P (lst g) ⟨c, hc⟩)).symm
  · exact wr_congr _ _ _ fun c hc =>
      ((nx_gMask2 s _ _ fr _ c rfl hc).trans (nx_msg_fresh s P (lst g) ⟨c, hc⟩)).symm
  · exact wr_congr _ _ _ fun c hc =>
      ((nx_gMask3 s _ _ fr _ c (by omega) hc).trans (nx_tl_main s P (lst g) ⟨c, hc⟩)).symm
  · exact wr_congr _ _ _ fun c hc =>
      ((nx_gMask4 s _ _ fr _ c (by omega) hc).trans (nx_tl_mask s P (lst g) ⟨c, hc⟩)).symm
  · exact wr_congr _ _ _ fun c hc =>
      ((nx_gMask5 s _ _ fr _ c (by omega) hc).trans (nx_tl_fresh s P (lst g) ⟨c, hc⟩)).symm
  · exact wr_congr _ _ _ fun c _ =>
      ((nx_gMask6 s _ _ fr _ (by omega)).trans (congrArg fr (by omega))).symm
  · show [ofE (fr (s.Z.l + s.Z.l + s.C.r + s.Z.r + s.Z.r + m + 1 - 1))] =
      [ofE (gMask s _ _ fr (s.Z.l + s.Z.l + s.C.r + s.Z.r + s.Z.r + m + 0))]
    rw [nx_gMask6 s _ _ fr (s.Z.l + s.Z.l + s.C.r + s.Z.r + s.Z.r + m + 0) (by omega)]
    exact congrArg (fun n => [ofE (fr n)]) (by omega)

/-- `rowsOf` of the list of `nx_mask_list` is `gMask`, encoded, row by row. -/
theorem nx_mask (fr : ℕ → GE) (nr m : ℕ)
    (hB : 2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ 2 ^ nr * m) (W Pf Rh Sg' Pi : List (List E))
    (hW : W = (List.range (2 ^ s.h)).map fun b => wr s.Z.l fun c => P.tabZ (b + 2 ^ s.h * c))
    (hPf : Pf = (List.range (2 ^ s.h)).map fun b => wr s.Z.l (P.fM b))
    (hRh : Rh = (List.range (2 ^ (s.h + s.g))).map fun b => wr s.C.r (P.tM b))
    (hSg : Sg' = (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.tZ b))
    (hPi : Pi = (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.fT b))
    (free : List E) (pad : E)
    (hfree : free = wr (2 ^ nr * m) fun n => fr (2 * s.Z.l + s.C.r + 2 * s.Z.r + n))
    (hpad : pad = ofE (fr (2 ^ nr * m - 1))) :
    rowsOf (2 ^ nr) (foldRows .two (g.take s.h) W s.Z.l ++ foldRows .two (g.take s.h) Pf s.Z.l ++
          foldRows .two g Rh s.C.r ++ foldRows .two (g.take s.h) Sg' s.Z.r ++
          foldRows .two (g.take s.h) Pi s.Z.r ++
        fitL Fld.zeroE (2 ^ nr * m - (foldRows .two (g.take s.h) W s.Z.l ++
          foldRows .two (g.take s.h) Pf s.Z.l ++ foldRows .two g Rh s.C.r ++
          foldRows .two (g.take s.h) Sg' s.Z.r ++
          foldRows .two (g.take s.h) Pi s.Z.r).length - 1) free ++ [pad]).toArray =
      (List.range (2 ^ nr)).map fun b => wr m fun c =>
        gMask s (foldMsg s (μOf s P) (φOf s P) fun t => lst g t.val)
          (foldTl s (ρOf s P) (ψOf s P) fun t => lst g t.val) fr (b + 2 ^ nr * c) := by
  rw [nx_mask_list s P g hg fr _ hB W Pf Rh Sg' Pi hW hPf hRh hSg hPi free pad hfree hpad]
  exact nx_rows_of _ _ _ (Nat.two_pow_pos _) rfl _ _ fun _ _ => rfl

end Tables

/-! ## 6 The fresh table -/

theorem nx_ok_lead (p : ℕ → Bool) (F : ℕ → E) : ∀ (l : List ℕ) (a : E), Fld.two.okE a = true →
    Fld.two.okE (l.foldl (fun s i => if p i then Fld.two.addE s (F i) else s) a) = true
  | [], _, h => h
  | i :: l, a, h => by
    rw [List.foldl_cons]
    refine nx_ok_lead p F l _ ?_
    by_cases hp : p i = true
    · rw [if_pos hp]
      exact okE_addE _ _
    · rw [if_neg hp]
      exact h

section Fresh
-- every theorem of this section takes hw and h0: the coefficients' words are below the prime
variable (U : Hide) (hw : ∀ l t, Fld.two.okE (U.w l t) = true) (h0 : Fld.two.okE U.w0 = true)
include hw h0

/-- Every entry of `freshRow` has words below the prime: it is a coefficient copied unchanged, a
sum, or zero. -/
theorem nx_ok_freshRow (k h b : ℕ) : ∀ e ∈ freshRow .two k h U b, Fld.two.okE e = true := by
  unfold freshRow
  refine List.forall_mem_append.2 ⟨List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun i _ => ?_⟩,
    ?_⟩
  · refine nx_ok_lead _ _ _ _ ?_
    split
    · exact hw _ _
    · exact h0
  · split
    · exact hw _ _
    · exact okE_zeroE
  · split
    · refine List.forall_mem_append.2 ⟨List.forall_mem_cons.2 ⟨hw _ _, fun e he => ?_⟩,
        List.forall_mem_singleton.2 h0⟩
      obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 he
      rcases List.mem_cons.1 hi with rfl | hi
      · exact hw _ _
      · rw [List.mem_singleton.1 hi]
        exact hw _ _
    · intro e he
      cases he

theorem nx_ok_freshRows (k h lz i : ℕ) :
    Fld.two.okE (ent (freshRows .two k h lz U) i) = true := by
  unfold ent freshRows
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split
  · exact nx_ok_getD _ (nx_ok_freshRow U hw h0 k h _) _
  · exact okE_zeroE

/-- `rowsOf` of `freshRows` is the packing `packedN`, encoded, if the rows have room (hl). -/
theorem nx_fresh (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l) :
    rowsOf (2 ^ s.h) (freshRows .two (s.h + s.g) s.h s.Z.l U) =
      (List.range (2 ^ s.h)).map fun b => wr s.Z.l (packedN s (coefU (s.h + s.g) U) b) := by
  have hs : (freshRows .two (s.h + s.g) s.h s.Z.l U).size = 2 ^ s.h * s.Z.l := Array.size_ofFn
  unfold rowsOf
  rw [hs, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  refine List.map_congr_left fun b hb => List.map_congr_left fun c hc => ?_
  refine eq_ofE (nx_ok_freshRows U hw h0 _ _ _ _) ?_
  show vec (freshRows .two (s.h + s.g) s.h s.Z.l U) (b + 2 ^ s.h * c) = _
  unfold packedN
  rw [dif_pos ⟨hl, List.mem_range.1 hc⟩, ← fresh_packed s hl U]
  show _ = vec _ (OnBytes.Slice.Sz.rowNo (fun t : Fin s.h => b.testBit t.val) + 2 ^ s.h * c)
  rw [rowNo_testBit, Nat.mod_eq_of_lt (List.mem_range.1 hb)]

end Fresh

/-! ## 7 What `ridersBy` returns -/

/-- `ridersBy` at the last stage returns the masking word's four lists. -/
theorem nx_riders_last (f : Fld) (K : Sorted) (i : ℕ) (s : Stage) :
    ridersBy f K i s true =
      ([(List.range s.C.l).map (K.word i 0), (List.range s.Z.l).map (K.word i 1)],
        [(List.range s.C.r).map (K.word i 2), (List.range s.Z.r).map (K.word i 3)]) := by
  have e : ∀ t, rideCoin K i true (100 * i + 60 + t) = K.word i t := fun t => by
    funext n
    show K.word i (100 * i + 60 + t - (100 * i + 60)) n = _
    rw [Nat.add_sub_cancel_left]
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at e0 e1 e2 e3
  simp only [ridersBy, riders, coins, e0, e1, e2, e3, if_true]

/-- At a stage that is not the last, `ridersBy` returns the fresh table and its rows' tails. -/
theorem nx_riders_mid (f : Fld) (K : Sorted) (i : ℕ) (s : Stage) :
    ridersBy f K i s false =
      (rowsOf (2 ^ s.h) (freshRows f s.k s.h s.Z.l (hideBy K i)),
        (List.range (2 ^ s.h)).map fun b => (List.range s.Z.r).map (K.fresh i b)) := by
  have eh : rideCoin K i false (100 * i + 30) = K.hide i := by
    funext n
    simp only [rideCoin, if_true]
  have ef : ∀ b, rideCoin K i false (100 * i + 40 + b) = K.fresh i b := fun b => by
    funext n
    have h : ¬ (100 * i + 40 + b = 100 * i + 30) := by omega
    simp only [rideCoin, if_neg h, Nat.add_sub_cancel_left]
  simp only [ridersBy, riders, hideOf, hideBy, coins, eh, ef, Bool.false_eq_true, if_false]

/-- At a stage that is not the last, the first list of `ridersBy` is the packing `packedN`, encoded.
i: the stage's number, counted from 1. W: what the hiding polynomial's coefficients decode to. -/
theorem ride_fresh (K : Sorted) (i : ℕ) (s : Stage)
    (W : Cb.HIdx (Cb.sVars GE 2 ((sgOf s).h + (sgOf s).g)) → GE) (hh : s.h ≤ s.k)
    (hroom : 2 * s.k + 1 ≤ s.h + s.Z.l)
    (hW : coefU ((sgOf s).h + (sgOf s).g) (hideBy K i) = W)
    (hok : ∀ n, Fld.two.okE (K.hide i n) = true) :
    (ridersBy .two K i s false).1 =
      (List.range (2 ^ s.h)).map fun b => wr s.Z.l (packedN (sgOf s) W b) := by
  have hl : (sgOf s).h + 2 * (sgOf s).g + 1 ≤ (sgOf s).Z.l := by
    show s.h + 2 * (s.k - s.h) + 1 ≤ s.Z.l
    omega
  have hf := nx_fresh (hideBy K i) (fun _ _ => hok _) (hok _) (sgOf s) hl
  rw [hW] at hf
  rw [nx_riders_mid, ← sg_k hh]
  exact hf

/-! ## 8 The switch -/

/-- The point that a fold's rounds sampled, decoded in two ways: from the rounds' first elements as
`OnBytes.E` (as in `aPoint`), and from the list of these elements as triples of words. -/
theorem nx_point (n o : ℕ) (D : ℕ → Fmt.Drawn) :
    OnBytes.Slice.readP n ((List.range n).map fun m =>
        OnBytes.E.ofTriple ((D (o + (m + 1))).elems.headD (0, 0, 0))) =
      fun t : Fin n => lst ((List.range n).map fun m => headE (D (o + 1 + m))) t.val := by
  funext t
  show OnBytes.Slice.readE (List.getD _ t.val OnBytes.zeroE) = toE (List.getD _ t.val Fld.zeroE)
  rw [getD_range _ _ _ _ t.isLt, getD_range _ _ _ _ t.isLt, readE_ofTriple]
  exact congrArg (fun m => toE ((D m).elems.headD (0, 0, 0))) (by omega)

/-- The six fields of `Tab` after a switch, for two stages given as `Sg`. g: the elements that the
fold's rounds sampled. fr: the values of the free entries. new: the state whose tails, fresh table
and masking word the next stage takes over. The last two hypotheses: the two lists of `ridersBy`
are that state's, encoded. -/
theorem nx_core (s s' : Sg) (K : Sorted) (i : ℕ) (fr : ℕ → GE) (new P : PS) (p : PSt)
    (g : List E) (last : Bool) (hg : g.length = s.h + s.g)
    (hA : 2 ^ (s'.h + s'.g) * s'.C.l = s.C.l)
    (hB : 2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ 2 ^ s'.h * s'.Z.l) (T : Tab s.st false P p)
    (hmain : ∀ b q, K.main i b q = ofE (new.tM b q))
    (hmask : ∀ b q, K.mask i b q = ofE (new.tZ b q))
    (hfree : ∀ n, K.free i n = ofE (fr (2 * s.Z.l + s.C.r + 2 * s.Z.r + n)))
    (hpad : K.pad i = ofE (fr (2 ^ s'.h * s'.Z.l - 1)))
    (hP : (ridersBy .two K i s'.st last).1 =
      if last then [wr s'.C.l new.sM, wr s'.Z.l (new.fM 0)]
      else (List.range (2 ^ s'.h)).map fun b => wr s'.Z.l (new.fM b))
    (hPi : (ridersBy .two K i s'.st last).2 =
      if last then [wr s'.C.r new.sT, wr s'.Z.r (new.fT 0)]
      else (List.range (2 ^ s'.h)).map fun b => wr s'.Z.r (new.fT b)) :
    Tab s'.st last (nextPS s (fun t => lst g t.val) fr new P)
      (nextBy Seams.lib .two K i s.st s'.st last g p) where
  main := nx_main s P g hg (s'.h + s'.g) s'.C.l hA p.M T.main
  mainT := congrArg (fun F => (List.range (2 ^ (s'.h + s'.g))).map F)
    (funext fun b => nx_map_wr s'.C.r _ _ (hmain b))
  mask := nx_mask s P g hg fr s'.h s'.Z.l hB p.W p.P p.Rh p.Sg p.Pi T.mask T.ride T.mainT T.maskT
    T.rideT _ _ (nx_map_wr _ _ _ hfree) hpad
  maskT := congrArg (fun F => (List.range (2 ^ s'.h)).map F)
    (funext fun b => nx_map_wr s'.Z.r _ _ (hmask b))
  ride := hP
  rideT := hPi

/-- `nx_core` for two stages given as `Stage`, with h ≤ k, at the sampled point. -/
theorem nx_stage (K : Sorted) (i : ℕ) (fr : ℕ → GE) (cur next : Stage) (last : Bool) (o : ℕ)
    (new P : PS) (p : PSt) (D : ℕ → Fmt.Drawn) (hc : cur.h ≤ cur.k) (hn : next.h ≤ next.k)
    (hfit : switchFitB cur next = true) (T : Tab cur false P p)
    (hmain : ∀ b q, K.main i b q = ofE (new.tM b q))
    (hmask : ∀ b q, K.mask i b q = ofE (new.tZ b q))
    (hfree : ∀ n, K.free i n = ofE (fr (2 * cur.Z.l + cur.C.r + 2 * cur.Z.r + n)))
    (hpad : K.pad i = ofE (fr (2 ^ next.h * next.Z.l - 1)))
    (hP : (ridersBy .two K i next last).1 =
      if last then [wr next.C.l new.sM, wr next.Z.l (new.fM 0)]
      else (List.range (2 ^ next.h)).map fun b => wr next.Z.l (new.fM b))
    (hPi : (ridersBy .two K i next last).2 =
      if last then [wr next.C.r new.sT, wr next.Z.r (new.fT 0)]
      else (List.range (2 ^ next.h)).map fun b => wr next.Z.r (new.fT b)) :
    Tab next last (nextPS (sgOf cur) (aPoint cur o D) fr new P)
      (nextBy Seams.lib .two K i cur next last
        ((List.range cur.k).map fun n => headE (D (o + 1 + n))) p) := by
  have ec : (sgOf cur).st = cur := H2K.Pub.stN_eq hc
  have en : (sgOf next).st = next := H2K.Pub.stN_eq hn
  simp only [switchFitB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
  obtain ⟨⟨⟨⟨hA, hB⟩, -⟩, -⟩, -⟩ := hfit
  have hA' : 2 ^ ((sgOf next).h + (sgOf next).g) * (sgOf next).C.l = (sgOf cur).C.l := by
    rw [sg_k hn]
    exact hA
  have key := nx_core (sgOf cur) (sgOf next) K i fr new P p
    ((List.range ((sgOf cur).h + (sgOf cur).g)).map fun n => headE (D (o + 1 + n))) last
    (by rw [List.length_map, List.length_range]) hA' hB (by rw [ec]; exact T) hmain hmask hfree hpad
    (by rw [en]; exact hP) (by rw [en]; exact hPi)
  rw [ec, en] at key
  unfold aPoint
  rw [nx_point, ← sg_k hc]
  exact key

theorem nextBy_tab : Spec.next_tab := by
  intro K B j cur next last o P p D hc hn hfit hroom T Ct
  cases last
  · refine nx_stage K (j + 2) (B.fr j) cur next false o
      { B.new j with fM := packedN (sgOf next) (B.W (sgOf next) (j + 1)) } P p D hc hn hfit T
      Ct.main Ct.mask Ct.free Ct.pad ?_ ?_
    · exact ride_fresh K (j + 2) next _ hn (hroom rfl) (Ct.hide rfl).1 (Ct.hide rfl).2
    · rw [nx_riders_mid]
      exact congrArg (fun F => (List.range (2 ^ next.h)).map F)
        (funext fun b => nx_map_wr next.Z.r _ _ (Ct.fresh rfl b))
  · refine nx_stage K (j + 2) (B.fr j) cur next true o (B.new j) P p D hc hn hfit T Ct.main
      Ct.mask Ct.free Ct.pad ?_ ?_
    · rw [nx_riders_last]
      exact congrArg₂ (fun a b => [a, b]) (nx_map_wr _ _ _ fun n => (Ct.word rfl n).1)
        (nx_map_wr _ _ _ fun n => (Ct.word rfl n).2.1)
    · rw [nx_riders_last]
      exact congrArg₂ (fun a b => [a, b]) (nx_map_wr _ _ _ fun n => (Ct.word rfl n).2.2.1)
        (nx_map_wr _ _ _ fun n => (Ct.word rfl n).2.2.2)

/-- For any two stages, any state P before the switch, any values N and fr of `BCoins.new` and
`BCoins.fr`, and any values H that the hiding polynomial's random values decode to, some K, B and p
satisfy `Tab` and `CoinTie` together. So these two hypotheses of `nextBy_tab` never exclude each
other. `B.W` cannot be chosen: it is computed from K. -/
theorem nx_met (j : ℕ) (cur next : Stage) (last : Bool) (P : PS) (N : ℕ → PS) (fr : ℕ → ℕ → GE)
    (H : ℕ → GE) :
    ∃ (K : Sorted) (B : BCoins) (p : PSt), B.new = N ∧ B.fr = fr ∧
      (∀ i n, K.hide i n = ofE (H n)) ∧ Tab cur false P p ∧ CoinTie K B j cur next last := by
  let K : Sorted :=
    { main := fun _ b q => ofE ((N j).tM b q)
      mask := fun _ b q => ofE ((N j).tZ b q)
      hide := fun _ n => ofE (H n)
      fresh := fun _ b q => ofE ((N j).fT b q)
      free := fun _ n => ofE (fr j (2 * cur.Z.l + cur.C.r + 2 * cur.Z.r + n))
      pad := fun _ => ofE (fr j (2 ^ next.h * next.Z.l - 1))
      word := fun _ t n =>
        match t with
        | 0 => ofE ((N j).sM n)
        | 1 => ofE ((N j).fM 0 n)
        | 2 => ofE ((N j).sT n)
        | _ => ofE ((N j).fT 0 n) }
  refine ⟨K, ⟨fun s i => coefU (s.h + s.g) (hideBy K (i + 1)), N, fr⟩,
    ⟨(List.range (2 ^ cur.k)).map fun b => wr cur.C.l fun c => P.tabM (b + 2 ^ cur.k * c),
      (List.range (2 ^ cur.k)).map fun b => wr cur.C.r (P.tM b),
      (List.range (2 ^ cur.h)).map fun b => wr cur.Z.l fun c => P.tabZ (b + 2 ^ cur.h * c),
      (List.range (2 ^ cur.h)).map fun b => wr cur.Z.r (P.tZ b),
      (List.range (2 ^ cur.h)).map fun b => wr cur.Z.l (P.fM b),
      (List.range (2 ^ cur.h)).map fun b => wr cur.Z.r (P.fT b)⟩, rfl, rfl, fun _ _ => rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  exact
    { main := fun _ _ => rfl
      mask := fun _ _ => rfl
      free := fun _ => rfl
      pad := rfl
      fresh := fun _ _ _ => rfl
      hide := fun _ => ⟨rfl, fun _ => okE_ofE _⟩
      word := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩ }

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.nx_wr_add
#print axioms ProofFile.Honest.K12.Light.nx_getD_wr
#print axioms ProofFile.Honest.K12.Light.nx_map_wr
#print axioms ProofFile.Honest.K12.Light.nx_fitL_wr
#print axioms ProofFile.Honest.K12.Light.nx_ent_toArray
#print axioms ProofFile.Honest.K12.Light.nx_rows_of
#print axioms ProofFile.Honest.K12.Light.nx_ok_fold1L
#print axioms ProofFile.Honest.K12.Light.nx_ok_foldl
#print axioms ProofFile.Honest.K12.Light.nx_ok_getD
#print axioms ProofFile.Honest.K12.Light.nx_ok_foldV
#print axioms ProofFile.Honest.K12.Light.nx_foldRows
#print axioms ProofFile.Honest.K12.Light.nx_foldRows_take
#print axioms ProofFile.Honest.K12.Light.nx_msg_main
#print axioms ProofFile.Honest.K12.Light.nx_msg_mask
#print axioms ProofFile.Honest.K12.Light.nx_msg_fresh
#print axioms ProofFile.Honest.K12.Light.nx_tl_main
#print axioms ProofFile.Honest.K12.Light.nx_tl_mask
#print axioms ProofFile.Honest.K12.Light.nx_tl_fresh
#print axioms ProofFile.Honest.K12.Light.nx_gMain
#print axioms ProofFile.Honest.K12.Light.nx_gMask1
#print axioms ProofFile.Honest.K12.Light.nx_gMask2
#print axioms ProofFile.Honest.K12.Light.nx_gMask3
#print axioms ProofFile.Honest.K12.Light.nx_gMask4
#print axioms ProofFile.Honest.K12.Light.nx_gMask5
#print axioms ProofFile.Honest.K12.Light.nx_gMask6
#print axioms ProofFile.Honest.K12.Light.nx_main
#print axioms ProofFile.Honest.K12.Light.nx_mask_list
#print axioms ProofFile.Honest.K12.Light.nx_mask
#print axioms ProofFile.Honest.K12.Light.nx_ok_lead
#print axioms ProofFile.Honest.K12.Light.nx_ok_freshRow
#print axioms ProofFile.Honest.K12.Light.nx_ok_freshRows
#print axioms ProofFile.Honest.K12.Light.nx_fresh
#print axioms ProofFile.Honest.K12.Light.nx_riders_last
#print axioms ProofFile.Honest.K12.Light.nx_riders_mid
#print axioms ProofFile.Honest.K12.Light.ride_fresh
#print axioms ProofFile.Honest.K12.Light.nx_point
#print axioms ProofFile.Honest.K12.Light.nx_core
#print axioms ProofFile.Honest.K12.Light.nx_stage
#print axioms ProofFile.Honest.K12.Light.nextBy_tab
#print axioms ProofFile.Honest.K12.Light.nx_met
