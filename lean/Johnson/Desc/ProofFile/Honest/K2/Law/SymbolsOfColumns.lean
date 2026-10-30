-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SymbolsOfColumns.lean: the kind "the code switch" (K2): THE
FIELD `symbols` OF THE RECORD `MadeAsks` (Honest/K2/Law/ExchangeAtMade.lean), EXCHANGED:
`SymbolsAre` (Johnson/Desc/K2/Honest/Inner/Statement.lean) AT WHAT THE CLOSING KEEPS OF WHAT A FOLD
LEAVES, FROM FIVE PREMISES ON THE OPENED COLUMNS AND NINE PUBLIC ONES. No frame and no run. One
lemma; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  **`symbolsAre_of_columns`**  ⊢ `SymbolsAre Z old (frozenLeft c z Z.kept (foldEndAt old.layout
      Z.codes Z.code Z.maskCode ms M fresh γ)) pos Y`, c and z being Z's two codes
THE FIVE ON THE COLUMNS. cMainN, cMaskN: at each listed position each member's column has as many
main and mask symbols as the member has rows. cMain, cMask: symbol b reads as the code word's symbol
of the member's row b, MESSAGE AND TAIL, a mask row's at the position modulo the mask code's length.
cFresh: the like of the fresh mask's column, at the rows below 2^h.
THE NINE PUBLIC ONES. hm: two mask rows. hk: as many kept rows as the sizes' kept shapes have. hY:
the verifier's own reading (`Own.rowsSymbols`) returns Y. hγ: γ is the verifier's point, read in the
field. hZk, hnos: the sizes' kept shapes and the members' kept numbers are the layout's. hkept: a
kept member has no first main row. hapM, hapZ: in each of the two tables the members' blocks lie
apart.
How. `symbolsAre_of_tables` (Inner/SymbolsOfTables.lean) at the rows `tabMain` and its fellows; its
premises by `mainTable_reads`, `maskTable_reads` (Inner/TablesAtColumns.lean), `keptSymbols_reads`
(Inner/KeptAtColumns.lean), the six sums of Carry/FoldEndSums.lean, `eqW_congr`
(OnBytes/Slice/SimBasic.lean), `readL_take` (OnBytes/Slice/ProgMle.lean) and the six lemmas of
FrozenReads.lean.
Limits. NOT IN FRONT OF A LAW OVER COINS. AN IMPLICATION: IT PAYS NOTHING: none of
the fourteen is shown here of anything; whether they can be met together is not shown. The members
ms, their rows M, the fresh mask and γ are letters: that they are what a closing makes or what any
sender sent is not said. M AND fresh HOLD A RUN's COINS. Where rows are made by `messageRows`
(Johnson/Desc/ProofFile/Honest/K2/Sending.lean), four of the six functions of `Rows` hold coins and
zeros alone: of mainTlE and mainTlF the one that the rows' field picks holds coins inside the shape,
the other 0; so do maskTl and mask (at a fold's own mask by way of the letter `table`). Of mainE and
mainF the one that is picked holds a coin wherever `padAt` answers. Here all of these stay letters
under "for all": no coin's value is named. `MadeAsks`' file is not imported.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FrozenReads
import Johnson.Desc.K2.Honest.Inner.TablesAtColumns
import Johnson.Desc.K2.Honest.Inner.KeptAtColumns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE readL codeOf eqW_congr readL_take)
open Johnson.Prover.Send (Rows)
open Johnson.Prover.Link (symG symG_congr)
open ProofFile.Honest.K2 (frozenLeft frozenRead_main frozenRead_mainTail frozenRead_mask
  frozenRead_maskTail frozenRead_kept frozenRead_keptTail)

set_option quotPrecheck false in
/-- The kept rows, by member and row, as `rowOfComplex` lists them. -/
local notation "keptList" Z =>
  ((Sizes.kept Z).zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b))

/-- **`SymbolsAre` FROM THE COLUMNS.** ms, M, fresh, γ: the group's members, each in full, the fresh
mask in full, the fold's point: letters. NOT IN FRONT OF A LAW OVER COINS. -/
theorem symbolsAre_of_columns (Z : Sizes) (old : SingleRows) (pos : Positions)
    (opened : Array (Array Column)) (Y : Array E) (ms : List GroupMember) (M : Nat → Rows)
    (fresh : Rows) (γ : List GE)
    (hm : old.masks = 2) (hk : old.keptRows = (keptList Z).length)
    (hY : Own.rowsSymbols old opened pos.all.size = some Y)
    (hγ : ∀ t, t < old.layout.k → γ.getD t zeroG = readL old.gamma t)
    (hZk : Z.kept = (Own.keptNos old.layout).map (shapeOf ms))
    (hnos : ((List.range ms.length).filter fun w => keptOf ms w) = Own.keptNos old.layout)
    (hkept : ∀ w, w < old.layout.members.size → old.layout.kept.getD w false = true →
      old.layout.mainFirst.getD w none = none)
    (hapM : ∀ w w', w < old.layout.members.size → w' < old.layout.members.size → w ≠ w' →
      ∀ f f', old.layout.mainFirst.getD w none = some f →
      old.layout.mainFirst.getD w' none = some f' →
      f + (shapeOf ms w).mainRows ≤ f' ∨ f' + (shapeOf ms w').mainRows ≤ f)
    (hapZ : ∀ w w', w < old.layout.members.size → w' < old.layout.members.size → w ≠ w' →
      ∀ f f', old.layout.maskFirst.getD w none = some f →
      old.layout.maskFirst.getD w' none = some f' →
      f + (shapeOf ms w).maskRows ≤ f' ∨ f' + (shapeOf ms w').maskRows ≤ f)
    (cMainN : ∀ i, i < pos.all.size → ∀ w, w < old.layout.members.size →
      (colB opened w i).main.size = (shapeOf ms w).mainRows)
    (cMain : ∀ i, i < pos.all.size → ∀ w, w < old.layout.members.size →
      ∀ b, b < (shapeOf ms w).mainRows →
      readE ((colB opened w i).main.getD b zeroE) =
        symG (codeOf (Z.codes.base.getD Z.code default)) (pos.all.getD i 0)
          ((M w).main ((shapeOf ms w).mainDeg == 3) b)
          (tailIn (M w) ((shapeOf ms w).mainDeg == 3) b))
    (cMaskN : ∀ i, i < pos.all.size → ∀ w, w < old.layout.members.size →
      (colB opened w i).mask.size = (shapeOf ms w).maskRows)
    (cMask : ∀ i, i < pos.all.size → ∀ w, w < old.layout.members.size →
      ∀ b, b < (shapeOf ms w).maskRows →
      readE ((colB opened w i).mask.getD b zeroE) =
        symG (codeOf (Z.codes.mask.getD Z.maskCode default))
          (pos.all.getD i 0 % 2 ^ (codeOf (Z.codes.mask.getD Z.maskCode default)).a)
          ((M w).mask b) ((M w).maskTl b))
    (cFresh : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ old.layout.h →
      readE ((colB opened old.layout.members.size i).mask.getD b zeroE) =
        symG (codeOf (Z.codes.mask.getD Z.maskCode default))
          (pos.all.getD i 0 % 2 ^ (codeOf (Z.codes.mask.getD Z.maskCode default)).a)
          (fresh.mask b) (fresh.maskTl b)) :
    SymbolsAre Z old
      (frozenLeft (Z.codes.base.getD Z.code default) (Z.codes.mask.getD Z.maskCode default) Z.kept
        (foldEndAt old.layout Z.codes Z.code Z.maskCode ms M fresh γ)) pos Y := by
  have hfit : Own.shapeFits old = true := by
    unfold Own.rowsSymbols at hY
    split at hY
    · assumption
    · cases hY
  unfold Own.shapeFits at hfit
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfit
  obtain ⟨⟨⟨⟨-, g2⟩, -⟩, g4⟩, g5⟩ := hfit
  have hγ' : ∀ t, t < old.layout.h →
      γ.getD t zeroG = readL (old.gamma.take old.layout.h) t := fun t ht => by
    rw [readL_take _ _ _ ht]
    exact hγ t (by omega)
  refine symbolsAre_of_tables Z old _ pos opened Y (tabMain old.layout ms M)
    (tabMainTl old.layout ms M) (tabMask old.layout ms M) (tabMaskTl old.layout ms M) fresh.mask
    fresh.maskTl hm hk hY ?_ ?_ cFresh ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun i hi b _ => mainTable_reads old.layout ms M opened i b _ _ g4 hkept
      (fun w hw _ => cMainN i hi w hw) hapM (fun w hw _ => cMain i hi w hw)
  · exact fun i hi b _ => maskTable_reads old.layout ms M opened i b _ _ g5 (cMaskN i hi) hapZ
      (cMask i hi)
  · intro i hi n hn
    refine keptSymbols_reads Z _ old.layout opened i _ (shapeOf ms) hZk
      (fun w hw => cMainN i hi w (List.mem_range.1 (List.mem_filter.1 hw).1)) ?_ n (hk ▸ hn)
    intro a w haw b hb
    have hw : w < old.layout.members.size :=
      List.mem_range.1 (List.mem_filter.1 (List.mem_of_getElem? haw)).1
    have ha : a < Z.kept.length := by
      rw [hZk, List.length_map]
      exact (List.getElem?_eq_some_iff.1 haw).1
    have hsh : Z.kept.getD a {} = shapeOf ms w := by
      rw [hZk, List.getD_eq_getElem?_getD, List.getElem?_map, haw]
      rfl
    have hno : keptNo ms a = w := by
      unfold keptNo
      rw [hnos, List.getD_eq_getElem?_getD, haw]
      rfl
    rw [cMain i hi w hw b hb]
    refine symG_congr _ _ _ _ _ _ (fun j hj => ?_) (fun q hq => ?_)
    · rw [frozenRead_kept _ _ _ _ a b j ha (by rw [hsh]; exact hb) hj]
      show _ = (M (keptNo ms a)).main ((shapeOf ms (keptNo ms a)).mainDeg == 3) b j
      rw [hno]
    · rw [frozenRead_keptTail _ _ _ _ a b q ha (by rw [hsh]; exact hb) hq]
      show _ = tailIn (M (keptNo ms a)) ((shapeOf ms (keptNo ms a)).mainDeg == 3) b q
      rw [hno]
  · intro j hj
    rw [frozenRead_main _ _ _ _ j hj, foldEndAt_main_sum _ _ _ _ _ _ _ _ g2 j hj]
    exact Finset.sum_congr rfl fun b _ => by rw [eqW_congr _ _ _ _ hγ]
  · intro q hq
    rw [frozenRead_mainTail _ _ _ _ q hq, foldEndAt_mainTail_sum _ _ _ _ _ _ _ _ g2 q hq]
    exact Finset.sum_congr rfl fun b _ => by rw [eqW_congr _ _ _ _ hγ]
  · intro j hj
    rw [frozenRead_mask _ _ _ _ 0 j (by omega) hj, foldEndAt_mask0_sum _ _ _ _ _ _ _ _ j hj]
    exact Finset.sum_congr rfl fun b _ => by rw [eqW_congr _ _ _ _ hγ']
  · intro q hq
    rw [frozenRead_maskTail _ _ _ _ 0 q (by omega) hq,
      foldEndAt_maskTail0_sum _ _ _ _ _ _ _ _ q hq]
    exact Finset.sum_congr rfl fun b _ => by rw [eqW_congr _ _ _ _ hγ']
  · intro j hj
    rw [frozenRead_mask _ _ _ _ 1 j (by omega) hj, foldEndAt_mask1_sum _ _ _ _ _ _ _ _ j hj]
    exact Finset.sum_congr rfl fun b _ => by rw [eqW_congr _ _ _ _ hγ']
  · intro q hq
    rw [frozenRead_maskTail _ _ _ _ 1 q (by omega) hq,
      foldEndAt_maskTail1_sum _ _ _ _ _ _ _ _ q hq]
    exact Finset.sum_congr rfl fun b _ => by rw [eqW_congr _ _ _ _ hγ']

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.symbolsAre_of_columns
