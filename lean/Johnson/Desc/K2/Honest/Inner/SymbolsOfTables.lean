-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Inner/SymbolsOfTables.lean: the kind "the code switch" (K2): `SymbolsAre`
(Inner/Statement.lean) FROM WHAT STANDS IN THE TABLES THAT THE VERIFIER's TEXT LAYS OF THE OPENED
COLUMNS, AND FROM WHAT THE THREE FOLDED ROWS OF `Left` ARE, EACH AS MESSAGE AND TAIL. No frame and
no run: arrays and functions. Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness,
soundness or hiding.

  **`symG_sum`**  the code word's symbol is linear: of a weighted sum of n rows,
      message and tail
  `read_fold_all`  a table of just 2^|g| entries, folded at g: its first entry, read in the field
  `rowOfComplex_zero`, `rowOfComplex_mask`  row 0 of the complex; the rows behind the kept rows
  **`symbolsAre_of_tables`**  each entry of the main table, of the mask table and of the fresh
      mask's column reads as the symbol of a row (message and tail: six letters) · each kept symbol
      reads as the symbol of its row of the complex · W's main row and its two mask rows, message
      and tail, below the codes' sizes, are these rows' sums under the weights of the verifier's
      point ⊢ `SymbolsAre Z old W pos Y`
How. `rowsSymbols_eq` (Johnson/Desc/Own/SymbolsAgree.lean), `singleRowsSymbols_inv` and
`tablesAt_all` (OnBytes/Iop/SymbolLaws.lean) take Y apart; `readV_foldLowB_of`
(OnBytes/Slice/BlkFoldVec.lean) reads a folded table as a sum; `symG_line`, `symG_congr`
(Johnson/Prover/Link/Base.lean), `symG_zero` (Johnson/Prover/Link/FrontCols.lean).
Limits. An implication: none of its premises is shown here of anything. Two mask rows alone
(old.masks = 2). The rows are letters: nothing says whose they are.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K2.Honest.Inner.Statement
import Johnson.Desc.Own.SymbolsAgree
import OnBytes.Iop.SymbolLaws
import OnBytes.Slice.BlkFoldVec
import Johnson.Prover.Link.FrontCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE readV readL codeOf)
open Johnson.Prover.Link (symG symG_line symG_congr symG_zero)

set_option quotPrecheck false in
/-- The kept rows, by member and row, as `rowOfComplex` lists them. -/
local notation "keptList" Z =>
  ((Sizes.kept Z).zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b))

/-- **The symbol is linear**: of a weighted sum of n rows, message and tail. -/
theorem symG_sum (C : Fmt.M1.Code) (x n : ℕ) (w : ℕ → GE) (m t : ℕ → ℕ → GE) :
    symG C x (fun j => ∑ b ∈ Finset.range n, w b * m b j)
        (fun q => ∑ b ∈ Finset.range n, w b * t b q) =
      ∑ b ∈ Finset.range n, w b * symG C x (m b) (t b) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact symG_zero C x
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    exact (symG_line C x (fun j => ∑ b ∈ Finset.range n, w b * m b j) (m n)
      (fun q => ∑ b ∈ Finset.range n, w b * t b q) (t n) (w n)).trans (by rw [ih])

/-- A table of just 2^|g| entries, folded at g: its first entry, read in the field. -/
theorem read_fold_all (g : List E) (v : Array E) (hv : v.size = 2 ^ g.length) :
    readE ((foldLow v g).getD 0 zeroE) =
      ∑ b ∈ Finset.range (2 ^ g.length),
        OnBytes.Slice.eqW g.length (readL g) b * readE (v.getD b zeroE) := by
  have h := OnBytes.Slice.readV_foldLowB_of g v 1 (by rw [hv, Nat.one_mul]) 0
  simp only [Nat.mul_zero, Nat.add_zero] at h
  exact h

/-- Row 0 of the complex: the folded main row. -/
theorem rowOfComplex_zero (Z : Sizes) (W : Left) :
    rowOfComplex Z W 0 =
      (codeOf (Z.codes.base.getD Z.code default), W.main, W.mainTail) := rfl

/-- Behind the kept rows: the mask rows. -/
theorem rowOfComplex_mask (Z : Sizes) (W : Left) (j : ℕ) (hj : (keptList Z).length + 1 ≤ j) :
    rowOfComplex Z W j =
      (codeOf (Z.codes.mask.getD Z.maskCode default), W.mask (j - 1 - (keptList Z).length),
        W.maskTail (j - 1 - (keptList Z).length)) := by
  unfold rowOfComplex
  dsimp only
  split
  · rename_i h0
    exact absurd (beq_iff_eq.1 h0) (by omega)
  · split
    · rename_i y hy
      rw [List.getElem?_eq_none (by omega)] at hy
      cases hy
    · rfl

/-- **`SymbolsAre` from the tables.** mM, tM: the rows of the group's main table, message and tail;
mZ, tZ: of its mask table; mF, tF: of the fresh mask. -/
theorem symbolsAre_of_tables (Z : Sizes) (old : SingleRows) (W : Left) (pos : Positions)
    (opened : Array (Array Column)) (Y : Array E) (mM tM mZ tZ mF tF : ℕ → ℕ → GE)
    (hm : old.masks = 2) (hk : old.keptRows = (keptList Z).length)
    (hY : Own.rowsSymbols old opened pos.all.size = some Y)
    (hTM : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ old.layout.k →
      readE (mainTable old.layout opened i b) =
        symG (codeOf (Z.codes.base.getD Z.code default)) (pos.all.getD i 0) (mM b) (tM b))
    (hTZ : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ old.layout.h →
      readE (maskTable old.layout opened i b) =
        symG (codeOf (Z.codes.mask.getD Z.maskCode default))
          (pos.all.getD i 0 % 2 ^ (codeOf (Z.codes.mask.getD Z.maskCode default)).a) (mZ b) (tZ b))
    (hTF : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ old.layout.h →
      readE ((colB opened old.layout.members.size i).mask.getD b zeroE) =
        symG (codeOf (Z.codes.mask.getD Z.maskCode default))
          (pos.all.getD i 0 % 2 ^ (codeOf (Z.codes.mask.getD Z.maskCode default)).a) (mF b) (tF b))
    (hTK : ∀ i, i < pos.all.size → ∀ n, n < old.keptRows →
      readE ((keptSymbols old.layout opened i).getD n zeroE) =
        symG (rowOfComplex Z W (1 + n)).1 (pos.all.getD i 0) (rowOfComplex Z W (1 + n)).2.1
          (rowOfComplex Z W (1 + n)).2.2)
    (hWM : ∀ j, j < (codeOf (Z.codes.base.getD Z.code default)).l → W.main j =
      ∑ b ∈ Finset.range (2 ^ old.layout.k),
        OnBytes.Slice.eqW old.layout.k (readL old.gamma) b * mM b j)
    (hWT : ∀ q, q < (codeOf (Z.codes.base.getD Z.code default)).r → W.mainTail q =
      ∑ b ∈ Finset.range (2 ^ old.layout.k),
        OnBytes.Slice.eqW old.layout.k (readL old.gamma) b * tM b q)
    (hWZ : ∀ j, j < (codeOf (Z.codes.mask.getD Z.maskCode default)).l → W.mask 0 j =
      ∑ b ∈ Finset.range (2 ^ old.layout.h),
        OnBytes.Slice.eqW old.layout.h (readL (old.gamma.take old.layout.h)) b * mZ b j)
    (hWZT : ∀ q, q < (codeOf (Z.codes.mask.getD Z.maskCode default)).r → W.maskTail 0 q =
      ∑ b ∈ Finset.range (2 ^ old.layout.h),
        OnBytes.Slice.eqW old.layout.h (readL (old.gamma.take old.layout.h)) b * tZ b q)
    (hWF : ∀ j, j < (codeOf (Z.codes.mask.getD Z.maskCode default)).l → W.mask 1 j =
      ∑ b ∈ Finset.range (2 ^ old.layout.h),
        OnBytes.Slice.eqW old.layout.h (readL (old.gamma.take old.layout.h)) b * mF b j)
    (hWFT : ∀ q, q < (codeOf (Z.codes.mask.getD Z.maskCode default)).r → W.maskTail 1 q =
      ∑ b ∈ Finset.range (2 ^ old.layout.h),
        OnBytes.Slice.eqW old.layout.h (readL (old.gamma.take old.layout.h)) b * tF b q) :
    SymbolsAre Z old W pos Y := by
  intro i j hi hj
  rw [Own.rowsSymbols_eq] at hY
  obtain ⟨hg, hh, -, hall⟩ := singleRowsSymbols_inv old opened _ Y (by omega) hY
  obtain ⟨t, ht, -, e0, ek, e1, e2⟩ := hall i hi
  obtain ⟨s1, s2, s3, s4, s5⟩ := tablesAt_all _ _ _ t ht
  have hlow : (old.gamma.take old.layout.h).length = old.layout.h := by
    rw [List.length_take, hg]
    omega
  have hrows : old.rows = 1 + old.keptRows + 2 := by
    unfold SingleRows.rows
    rw [hm]
  have hsub : old.rows - old.masks = 1 + old.keptRows := by
    rw [hrows, hm]
    omega
  rw [hrows] at hj
  rcases Nat.lt_or_ge j (1 + old.keptRows) with hj1 | hj1
  · rw [if_pos (by rw [hsub]; exact hj1)]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [rowOfComplex_zero, Nat.add_zero, e0, read_fold_all _ _ (by rw [s1, hg]), hg]
      show _ = symG (codeOf (Z.codes.base.getD Z.code default)) (pos.all.getD i 0) W.main W.mainTail
      rw [symG_congr _ _ W.main _ W.mainTail _ hWM hWT, symG_sum]
      exact Finset.sum_congr rfl fun b hb => by rw [s4, hTM i hi b (Finset.mem_range.1 hb)]
    · obtain ⟨n, rfl⟩ : ∃ n, j = 1 + n := ⟨j - 1, by omega⟩
      have e : t.2.2.getD n zeroE = (keptSymbols old.layout opened i).getD n zeroE := by
        rw [← s3, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
      rw [← Nat.add_assoc, ek n (by omega), e]
      exact hTK i hi n (by omega)
  · rw [if_neg (by rw [hsub]; omega)]
    obtain ⟨r, hr, rfl⟩ : ∃ r, r < 2 ∧ j = 1 + old.keptRows + r :=
      ⟨j - (1 + old.keptRows), by omega, by omega⟩
    have er : 1 + old.keptRows + r - 1 - (keptList Z).length = r := by
      rw [← hk]
      omega
    rw [rowOfComplex_mask Z W _ (by rw [← hk]; omega), er]
    show _ = symG (codeOf (Z.codes.mask.getD Z.maskCode default))
      (pos.all.getD i 0 % 2 ^ (codeOf (Z.codes.mask.getD Z.maskCode default)).a) (W.mask r)
      (W.maskTail r)
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · rw [show i * old.rows + (1 + old.keptRows + 0) = i * old.rows + old.maskRow 0 from rfl,
        e1 (by omega), read_fold_all _ _ (by rw [s2, hlow]), hlow,
        symG_congr _ _ (W.mask 0) _ (W.maskTail 0) _ hWZ hWZT, symG_sum]
      exact Finset.sum_congr rfl fun b hb => by rw [s5, hTZ i hi b (Finset.mem_range.1 hb)]
    · rw [show i * old.rows + (1 + old.keptRows + 1) = i * old.rows + old.maskRow 1 from rfl,
        (e2 hm).2, read_fold_all _ _ (by rw [(e2 hm).1, hlow]), hlow,
        symG_congr _ _ (W.mask 1) _ (W.maskTail 1) _ hWF hWFT, symG_sum]
      exact Finset.sum_congr rfl fun b hb => by rw [hTF i hi b (Finset.mem_range.1 hb)]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.symG_sum
#print axioms VerifiableInference.Desc.K2.Honest.read_fold_all
#print axioms VerifiableInference.Desc.K2.Honest.rowOfComplex_zero
#print axioms VerifiableInference.Desc.K2.Honest.rowOfComplex_mask
#print axioms VerifiableInference.Desc.K2.Honest.symbolsAre_of_tables
