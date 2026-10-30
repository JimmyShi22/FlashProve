-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldPairs.lean: THE TABLE MADE OF THE 2 k + 1 WORDS PAIRS WITH THEIR POLYNOMIAL:
the premise "Pairs" (Johnson/Prover/Link/FoldHolds.lean) of the fold's laws, paid at the library's
own table of coefficients (Fmt.M1.FoldOwn.freshRows, Fmt/M1Fold.lean: the one that the library's
honest prover lays). Definitions with code: that table at the program's own elements: they define
part of the honest prover.

Main names (namespace Johnson.Prover.Link).
  freshRow_layL   a row of the library's table, in the order of the library's kit for such lists
      (layL, OnBytes/Slice/SimFold.lean).
  pMon_reaches   the library's test "row b reaches variable l", at the number of a vertex, is the
      sumcheck library's monomial at the vertex.
  toE_freshRow_at   at a column's place (hidePlace) a row reads as the sumcheck library's packing
      (pkC, Cb/Ld/LdSumPack.lean).
  fresh_packed   THE LIBRARY's TABLE, READ WITH THE ROW IN THE LOW BITS, IS packed (FoldHolds.lean)
      at the coefficients' names.
  FreshFits k h lz   THE ONE HOME OF "THE SHAPE FITS": h ≤ k, and room for the columns that hold
      coefficients; no subtraction. freshFits_stage: at a stage it follows from "room".
  freshTabE k h lz w hf   the table of the 2 k + 1 words, at the program's own elements: the proof
      that the shape fits is an argument. freshTabE?: for a caller that holds numbers: none where it
      does not fit. fresh_fits: its size (TabFits).
  pairs_fresh   "Pairs" at that table.
  fold_holds_fresh   fold_holds_words (FoldWordsShows.lean) WITHOUT ITS PREMISE "Pairs": one premise
      falls, one comes: "room".

WHY THE SHAPE MUST FIT. With fewer columns than 2 k - h + 1 the library's table leaves coefficients
out, without a word. With more row variables than variables (h > k) it lays one word in two columns,
and reads a coefficient that there is none of as 0: a test at the foot shows the first at (k, h) =
(1, 2). So the table cannot be called at such a shape. At a stage k is s.h + s.g, so h ≤ k holds of
itself, and "room" (s.h + 2 * s.g + 1 ≤ s.Z.l) is the named public premise of every law on the
table. The entries beyond these columns are 0 in the packing too; within them the only zeros are the
monomial's.

By calls: pairs_packed, placeF_inj (FoldHolds.lean); placeV_at (Cb/Ld/LdSumPackProofs.lean);
hidePlace_surj, hidePlace_lt, layL_zero, layL_hd, layL_lin, layL_sq, layL_one, layL_far
(SimFold.lean); testBit_rowNo, rowNo_lt (OnBytes/Slice/Cells.lean); ProxRun.sum_list_range
(OnBytes/Slice/BlkProxFold.lean); coefNamed_hIx, coefNamed_hCst (FoldWordsLaw.lean);
fold_holds_words.

Limits. The other premises of fold_holds_words stay the caller's. w is typed at its number and
handed in: nothing is sampled here, and nothing is said of sampled values. THIS TABLE HAS A SECOND
TERM ELSEWHERE: the sender of the segments' first messages lays it by a text of its own; no law ties
the two. Tests: #guard lines at the foot; the verifier's own fold is run against this table in
Johnson/Prover/Link/FoldWordsToy.lean. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.FoldWordsShows
import Johnson.Prover.Link.FoldRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes.Slice Cb
open Fmt (Fld)
open Fmt.M1.FoldOwn (Hide freshRow freshRows reaches)

/-! ## 1 The list's order -/

theorem midL_cons {α : Type} (lin sq : ℕ → α) (m : ℕ) :
    midL lin sq (m + 1) = sq 0 :: (List.range m).flatMap fun i => [lin (i + 1), sq (i + 1)] := by
  unfold midL
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  rfl

/-- **A row of the library's table of coefficients, in the order of the library's kit for such
lists** (layL, OnBytes/Slice/SimFold.lean). -/
theorem freshRow_layL (h n : ℕ) (U : Hide) (b : ℕ) :
    freshRow .two (h + n) h U b =
      layL ((List.range h).foldl
          (fun s i => if reaches h b (i + 1) then Fld.two.addE s (U.w (i + 1) 1) else s)
          (if h < h + n then U.w (h + 1) 1 else U.w0))
        (fun i => if reaches h b (i + 1) then U.w (i + 1) 2 else Fld.zeroE)
        (fun t => U.w (h + 1 + t) 1) (fun t => U.w (h + 1 + t) 2) U.w0 h n := by
  unfold freshRow layL
  cases n with
  | zero =>
      rw [if_neg (show ¬ h < h + 0 by omega), if_neg (show ¬ h < h + 0 by omega),
        if_neg (Nat.lt_irrefl 0)]
      rfl
  | succ m =>
      rw [if_pos (show h < h + (m + 1) by omega), if_pos (show h < h + (m + 1) by omega),
        if_pos (Nat.succ_pos m), midL_cons, show h + (m + 1) - h - 1 = m by omega]
      have e : ((List.range m).flatMap fun i => [U.w (h + 2 + i) 1, U.w (h + 2 + i) 2]) =
          (List.range m).flatMap fun i => [U.w (h + 1 + (i + 1)) 1, U.w (h + 1 + (i + 1)) 2] :=
        congrArg (fun f : ℕ → List Fmt.M1.E => (List.range m).flatMap f)
          (funext fun i => by rw [show h + 2 + i = h + 1 + (i + 1) by omega])
      rw [e]

/-! ## 2 The rows that reach a variable -/

/-- The library's test on a row's number, at the number of a vertex, is the sumcheck library's
monomial at the vertex. -/
theorem pMon_reaches {h : ℕ} (i : Fin h) (β : Fin h → Bool) :
    (pMon i β : GE) = if reaches h (Sz.rowNo β) (i.val + 1) then 1 else 0 := by
  unfold pMon reaches
  by_cases hall : ∀ j : Fin h, i ≤ j → β j = true
  · rw [if_pos, Finset.prod_eq_one]
    · intro j _
      by_cases hij : i ≤ j
      · rw [if_pos hij, if_pos (hall j hij)]
      · rw [if_neg hij]
    · rw [List.all_eq_true]
      intro j hj
      have hj' : i.val + j < h := by have := List.mem_range.1 hj; omega
      rw [show i.val + 1 - 1 + j = (⟨i.val + j, hj'⟩ : Fin h).val from by simp, testBit_rowNo]
      exact hall _ (Fin.le_def.2 (Nat.le_add_right _ _))
  · obtain ⟨j, hij, hj⟩ := by
      simpa only [not_forall, exists_prop] using hall
    rw [if_neg, Finset.prod_eq_zero (Finset.mem_univ j)]
    · rw [if_pos hij, if_neg hj]
    · intro hr
      rw [List.all_eq_true] at hr
      have hle : i.val ≤ j.val := Fin.le_def.1 hij
      have := hr (j.val - i.val) (List.mem_range.2 (by have := j.isLt; omega))
      rw [show i.val + 1 - 1 + (j.val - i.val) = j.val by omega, testBit_rowNo] at this
      exact hj this

theorem toE_foldl_if {α : Type} (p : α → Bool) (F : α → Fmt.M1.E) : ∀ (l : List α) (a : Fmt.M1.E),
    toE (l.foldl (fun s i => if p i then Fld.two.addE s (F i) else s) a) =
      toE a + (l.map fun i => toE (F i) * if p i then 1 else 0).sum
  | [], a => by simp
  | i :: l, a => by
      rw [List.foldl_cons, toE_foldl_if p F l, List.map_cons, List.sum_cons, ← add_assoc]
      congr 1
      by_cases hp : p i = true
      · rw [if_pos hp, if_pos hp, toE_addE, mul_one]
      · rw [if_neg hp, if_neg hp, mul_zero, add_zero]

/-- Column 0, read. -/
theorem toE_lead (h : ℕ) (U : Hide) (β : Fin h → Bool) (a : Fmt.M1.E) :
    toE ((List.range h).foldl (fun s i =>
        if reaches h (Sz.rowNo β) (i + 1) then Fld.two.addE s (U.w (i + 1) 1) else s) a) =
      toE a + ∑ i : Fin h, toE (U.w (i.val + 1) 1) * pMon i β := by
  rw [toE_foldl_if (fun i => reaches h (Sz.rowNo β) (i + 1)) (fun i => U.w (i + 1) 1),
    ProxRun.sum_list_range, Finset.sum_range]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [pMon_reaches]

/-! ## 3 Each column at its place -/

theorem coefU_at (k : ℕ) (U : Hide) (l : Fin k) (p : Fin 2) :
    coefU k U (hIx GE 2 k l p) = toE (U.w (l.val + 1) (p.val + 1)) :=
  coefNamed_hIx k _ _ l p

theorem coefU_cst (k : ℕ) (U : Hide) : coefU k U (hCst GE 2 k) = toE U.w0 :=
  coefNamed_hCst k _ _

/-- **At a column's place a row of the library's table reads as the sumcheck library's packing.** -/
theorem toE_freshRow_at (h n : ℕ) (U : Hide) (β : Fin h → Bool) (c : PCol h n 1) :
    toE ((freshRow .two (h + n) h U (Sz.rowNo β)).getD (hidePlace h n c) Fld.zeroE) =
      pkC h n 1 (coefU (h + n) U) (β, c) := by
  rw [freshRow_layL]
  rcases c with ⟨i, q⟩ | ⟨t, p⟩ | u
  · have hq : q.val = 0 := by have := q.isLt; omega
    show toE ((layL _ _ _ _ _ h n).getD (1 + i.val) Fld.zeroE) =
      coefU (h + n) U (hIx GE 2 (h + n) (Fin.castAdd n i) q.succ) * pMon i β
    rw [layL_hd _ _ _ _ _ _ _ _ _ i.isLt, coefU_at, pMon_reaches]
    show _ = toE (U.w (i.val + 1) (q.val + 1 + 1)) * _
    rw [hq]
    by_cases hr : reaches h (Sz.rowNo β) (i.val + 1) = true
    · rw [if_pos hr, if_pos hr, mul_one]
    · rw [if_neg hr, if_neg hr, mul_zero, toE_zeroE]
  · show toE ((layL _ _ _ _ _ h n).getD
        (if t.val = 0 ∧ p.val = 0 then 0 else h + 2 * t.val + p.val) Fld.zeroE) =
      coefU (h + n) U (hIx GE 2 (h + n) (Fin.natAdd h t) p) +
        if pLead n 1 (.inl (t, p)) then
          ∑ i : Fin h, coefU (h + n) U (hIx GE 2 (h + n) (Fin.castAdd n i) 0) * pMon i β
        else 0
    rw [coefU_at]
    show _ = toE (U.w (h + t.val + 1) (p.val + 1)) + _
    have hn : h < h + n := by have := t.isLt; omega
    by_cases h0 : t.val = 0 ∧ p.val = 0
    · rw [if_pos h0, layL_zero, toE_lead, if_pos hn,
        if_pos (show pLead n 1 (.inl (t, p)) = true from decide_eq_true h0), h0.1, h0.2]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [coefU_at]; rfl
    · rw [if_neg h0,
        if_neg (show ¬ pLead n 1 (.inl (t, p)) = true from fun e => h0 (of_decide_eq_true e)),
        add_zero]
      by_cases hp : p.val = 0
      · rw [hp, Nat.add_zero (h + 2 * t.val), layL_lin _ _ _ _ _ _ _ _ _ (by omega) t.isLt,
          show h + 1 + t.val = h + t.val + 1 by omega]
      · have hp1 : p.val = 1 := by have := p.isLt; omega
        rw [hp1, layL_sq _ _ _ _ _ _ _ _ _ t.isLt, show h + 1 + t.val = h + t.val + 1 by omega]
  · show toE ((layL _ _ _ _ _ h n).getD (if n = 0 then 0 else h + 2 * n) Fld.zeroE) =
      coefU (h + n) U (hCst GE 2 (h + n)) +
        if pLead n 1 (.inr u) then
          ∑ i : Fin h, coefU (h + n) U (hIx GE 2 (h + n) (Fin.castAdd n i) 0) * pMon i β
        else 0
    rw [coefU_cst]
    by_cases hn : n = 0
    · rw [if_pos hn, layL_zero, toE_lead, if_neg (show ¬ h < h + n by omega),
        if_pos (show pLead n 1 (.inr u) = true from decide_eq_true hn)]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [coefU_at]; rfl
    · rw [if_neg hn, layL_one _ _ _ _ _ _ _ _ (by omega),
        if_neg (show ¬ pLead n 1 (.inr u) = true from fun e => hn (of_decide_eq_true e)),
        add_zero]

/-! ## 4 The table -/

section Stage
variable (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l)

/-- An entry of the library's table, by row and place. -/
theorem vec_freshRows (k h lz : ℕ) (U : Hide) (b j : ℕ) (hb : b < 2 ^ h) (hj : j < lz) :
    vec (freshRows .two k h lz U) (b + 2 ^ h * j) =
      toE ((freshRow .two k h U b).getD j Fld.zeroE) := by
  have hlt : b + 2 ^ h * j < 2 ^ h * lz :=
    calc b + 2 ^ h * j < 2 ^ h + 2 ^ h * j := Nat.add_lt_add_right hb _
      _ = 2 ^ h * (j + 1) := by ring
      _ ≤ 2 ^ h * lz := Nat.mul_le_mul_left _ hj
  unfold vec Fmt.M1.ent freshRows
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hlt]
  show toE ((freshRow .two k h U ((b + 2 ^ h * j) % 2 ^ h)).getD ((b + 2 ^ h * j) / 2 ^ h)
    Fld.zeroE) = _
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Nat.add_mul_div_left _ _ (Nat.two_pow_pos h),
    Nat.div_eq_of_lt hb, Nat.zero_add]

/-- **THE LIBRARY's TABLE OF COEFFICIENTS, READ WITH THE ROW IN THE LOW BITS, IS THE SUMCHECK
LIBRARY's PACKING**, where the rows have room. -/
theorem fresh_packed (U : Hide) (x : s.cFr.J) :
    vec (freshRows .two (s.h + s.g) s.h s.Z.l U) (Sz.rowNo x.1 + 2 ^ s.h * x.2.val) =
      packed s hl (coefU (s.h + s.g) U) x := by
  obtain ⟨β, j⟩ := x
  rw [vec_freshRows _ _ _ _ _ _ (rowNo_lt β) j.isLt]
  show _ = placeV (placeF s hl) (fun c => pkC s.h s.g 1 (coefU (s.h + s.g) U) (β, c)) j
  by_cases hj : j.val < s.h + 2 * s.g + 1
  · obtain ⟨c, hc⟩ := hidePlace_surj s.h s.g j.val hj
    have e : j = placeF s hl c := Fin.ext hc.symm
    rw [e, placeV_at (placeF_inj s hl)]
    exact toE_freshRow_at s.h s.g U β c
  · rw [freshRow_layL, layL_far _ _ _ _ _ _ _ _ _ (by omega), toE_zeroE]
    unfold placeV
    refine (Finset.sum_eq_zero fun c _ => if_neg fun e => hj ?_).symm
    rw [← e]
    exact hidePlace_lt s.h s.g c

/-! ## 5 At the program's own elements -/

/-- **THE SHAPE FITS**: the rows stand on no more variables than there are, and a row has room for
the 2 k - h + 1 columns that hold coefficients. Written without a subtraction. A public shape. -/
def FreshFits (k h lz : ℕ) : Prop := h ≤ k ∧ 2 * k + 1 ≤ h + lz

instance (k h lz : ℕ) : Decidable (FreshFits k h lz) := by
  unfold FreshFits
  infer_instance

/-- **The table of the 2 k + 1 words**: the library's freshRows at uOfBook k w, at the program's own
elements: 2^h rows of lz entries, the row in the low bits of the index. IT CAN BE CALLED AT A SHAPE
THAT FITS ALONE: the proof is an argument. -/
def freshTabE (k h lz : ℕ) (w : Fin (2 * k + 1) → OnBytes.E) (_ : FreshFits k h lz) :
    Array OnBytes.E :=
  (freshRows .two k h lz (uOfBook k fun i => (w i).triple)).map .ofTriple

/-- The same for a caller that holds numbers: none where the shape does not fit. -/
def freshTabE? (k h lz : ℕ) (w : Fin (2 * k + 1) → OnBytes.E) : Option (Array OnBytes.E) :=
  if hf : FreshFits k h lz then some (freshTabE k h lz w hf) else none

/-- An array of triples, laid as the program's elements, reads as before: beyond its end too. -/
theorem readV_map_ofTriple (A : Array Fmt.M1.E) (i : ℕ) :
    readV (A.map OnBytes.E.ofTriple) i = vec A i := by
  unfold readV vec Fmt.M1.ent
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[i]? with
  | none => rfl
  | some a => rfl

theorem fresh_fits (k h lz : ℕ) (w : Fin (2 * k + 1) → OnBytes.E) (hf : FreshFits k h lz) :
    TabFits h lz (freshTabE k h lz w hf) := by
  unfold TabFits freshTabE freshRows
  rw [Array.size_map, Array.size_ofFn, Nat.mul_comm]

include hl in
/-- At a stage the shape fits where the rows have room: h ≤ k holds of itself there. -/
theorem freshFits_stage : FreshFits (s.h + s.g) s.h s.Z.l := ⟨Nat.le_add_right _ _, by omega⟩

/-- **"Pairs" AT THE TABLE OF THE 2 k + 1 WORDS**, where the rows have room. -/
theorem pairs_fresh (w : Fin (2 * (s.h + s.g) + 1) → OnBytes.E) :
    Pairs s s.Z.l (coefU (s.h + s.g) (uOfBook (s.h + s.g) fun i => (w i).triple))
      (tabRead s.h s.Z.l (freshTabE (s.h + s.g) s.h s.Z.l w (freshFits_stage s hl))) := by
  have e : tabRead s.h s.Z.l (freshTabE (s.h + s.g) s.h s.Z.l w (freshFits_stage s hl)) =
      packed s hl (coefU (s.h + s.g) (uOfBook (s.h + s.g) fun i => (w i).triple)) :=
    funext fun x => (readV_map_ofTriple _ _).trans (fresh_packed s hl _ x)
  rw [e]
  exact pairs_packed s hl _

/-- **THE SINGLE ROWS THAT THE DESCRIPTION's FOLD RETURNS ARE TRUE WHERE THE ROUNDS SEND THE WORDS
AND THE THIRD TABLE IS MADE OF THE SAME 2 k + 1 WORDS**: fold_holds_words
(Johnson/Prover/Link/FoldWordsShows.lean) without its premise "Pairs"; "room" comes in its stead. -/
theorem fold_holds_fresh (N : ℕ → ℕ) (κ : ℕ → ℕ → GE) (S : OnBytes.Statement)
    (F : OnBytes.FoldShape) (row : OnBytes.GroupRow) (id : ℕ) (rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (hk : F.layout.k = s.h + s.g) (hh : F.layout.h = s.h)
    (hok : OnBytes.foldRowOk (spent S id) F row = true)
    (hZ : ((spent S id).codes.mask.getD F.maskCode default).ell = s.Z.l)
    (c d m mu : Array OnBytes.E) (keptV : OnBytes.E) (w : Fin (2 * (s.h + s.g) + 1) → OnBytes.E)
    (hs : FoldSizes (s.h + s.g) s.h s.C.l s.Z.l (c.map (·.triple)) (d.map (·.triple))
      (m.map (·.triple)) (mu.map (·.triple)))
    (hv : vecG s row = vecIn s ⟨c.map (·.triple), d.map (·.triple), Fld.zeroE⟩)
    (hV : keptVal N κ row.kept = readE keptV)
    (hin : ∑ j, vecG s row j * vecIn s ⟨m.map (·.triple), mu.map (·.triple), Fld.zeroE⟩ j +
      keptVal N κ row.kept = readE row.target)
    (hσ : (sentOf rE).getD 0 OnBytes.zeroE = foldSigmaE (s.h + s.g) w)
    (hlen : rR.length = s.h + s.g)
    (hq : ∀ i (h : i < rR.length),
      (sentOf rR[i]).getD 0 OnBytes.zeroE = (foldRoundE (s.h + s.g) s.h c d m mu keptV w
          (drawnOf rE) ((rR.take i).map drawnOf)).1 ∧
        (sentOf rR[i]).getD 1 OnBytes.zeroE = (foldRoundE (s.h + s.g) s.h c d m mu keptV w
          (drawnOf rE) ((rR.take i).map drawnOf)).2) :
    ∑ j, vecS s (foldOutAt S F row id (rE :: rR)) j *
          foldMsg s (vecIn s ⟨m.map (·.triple), mu.map (·.triple), Fld.zeroE⟩)
            (tabRead s.h s.Z.l (freshTabE (s.h + s.g) s.h s.Z.l w (freshFits_stage s hl)))
            (sPt 2 (s.h + s.g) (ptK (s.h + s.g) (lst ((rR.map drawnOf).map (·.triple))))) j +
        keptVal N κ (foldOutAt S F row id (rE :: rR)).kept =
      readE (foldOutAt S F row id (rE :: rR)).target :=
  fold_holds_words s _ N κ S F row id rE rR hk hh hok hZ c d m mu keptV w hs hv hV hin
    (pairs_fresh s hl w) hσ hlen hq

end Stage

-- the table's size; its triples are the library's own
#guard ((freshTabE? 3 1 8 fun i => .ofTriple (Fmt.M1.FoldOwn.mk .two (100 + i.val))).map
  (·.size)) = some 16
#guard ((freshTabE? 3 1 8 fun i => .ofTriple (Fmt.M1.FoldOwn.mk .two (100 + i.val))).map
    fun T => T.map (·.triple)) =
  some (freshRows .two 3 1 8 (uOfBook 3 fun i => Fmt.M1.FoldOwn.mk .two (100 + i.val)))
-- negative tests: shapes that do not fit are rejected: more row variables than variables, at
-- (k, h) = (1, 2) and (0, 1); one column too few; and the least room is accepted
#guard (freshTabE? 1 2 8 fun i => .ofTriple (Fmt.M1.FoldOwn.mk .two (100 + i.val))).isNone
#guard (freshTabE? 0 1 8 fun i => .ofTriple (Fmt.M1.FoldOwn.mk .two (100 + i.val))).isNone
#guard (freshTabE? 3 1 5 fun i => .ofTriple (Fmt.M1.FoldOwn.mk .two (100 + i.val))).isNone
#guard (freshTabE? 3 1 6 fun i => .ofTriple (Fmt.M1.FoldOwn.mk .two (100 + i.val))).isSome
-- why (1, 2) is rejected: there the library's own row holds one word in two columns
#guard (freshRow .two 1 2 (uOfBook 1 fun i => Fmt.M1.FoldOwn.mk .two (100 + i.val)) 3).getD 1
    Fld.zeroE =
  (freshRow .two 1 2 (uOfBook 1 fun i => Fmt.M1.FoldOwn.mk .two (100 + i.val)) 3).getD 2 Fld.zeroE

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.midL_cons
#print axioms Johnson.Prover.Link.freshRow_layL
#print axioms Johnson.Prover.Link.pMon_reaches
#print axioms Johnson.Prover.Link.toE_foldl_if
#print axioms Johnson.Prover.Link.toE_lead
#print axioms Johnson.Prover.Link.coefU_at
#print axioms Johnson.Prover.Link.coefU_cst
#print axioms Johnson.Prover.Link.toE_freshRow_at
#print axioms Johnson.Prover.Link.vec_freshRows
#print axioms Johnson.Prover.Link.fresh_packed
#print axioms Johnson.Prover.Link.readV_map_ofTriple
#print axioms Johnson.Prover.Link.fresh_fits
#print axioms Johnson.Prover.Link.freshFits_stage
#print axioms Johnson.Prover.Link.pairs_fresh
#print axioms Johnson.Prover.Link.fold_holds_fresh
