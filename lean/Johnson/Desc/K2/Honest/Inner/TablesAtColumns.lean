-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Inner/TablesAtColumns.lean: the kind "the code switch" (K2): WHAT STANDS IN
THE TWO TABLES THAT THE VERIFIER's TEXT LAYS OF THE OPENED COLUMNS AT ONE POSITION (`mainTable`,
`maskTable`, OnBytes/Iop/SymbolLaws.lean), WHERE EACH MEMBER's COLUMN HOLDS ITS ROWS' SYMBOLS AND
THE LAYOUT's BLOCKS LIE APART: entry ρ reads as the symbol of row ρ of the group's table (`tabMain`
and its fellows, Johnson/Desc/K2/Honest/Carry/FoldEndSums.lean). Lemmas; NONE OF THE LIBRARY's
GOALS. Nothing on completeness, soundness or hiding.

  `tableRow_some`, `tableRow_none`  which row `tableRow` (FoldEnd.lean) finds; where it finds none
  `laid_off`, `laid_at`  a table laid member by member: a row in no laid member's block holds 0; a
      row in just one block holds that member's symbol
  **`mainTable_reads`**, **`maskTable_reads`**  the two tables
Limits. That the columns hold the rows' symbols, how many symbols each has, that the blocks lie
apart and that a kept member has no first main row are premises. The code and the position are
letters. One position.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K2.Honest.Carry.FoldEndSums
import Johnson.Desc.K2.Honest.Inner.SymbolsOfTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE codeOf)
open Johnson.Prover.Send (Rows)
open Johnson.Prover.Link (symG symG_zero)

/-! ## 1 Which row the table finds -/

/-- A row that the table finds: its member has a first row, and the row lies in its block. -/
theorem tableRow_some (first : Array (Option Nat)) (rows : Nat → Nat) (ρ w b : Nat)
    (h : tableRow first rows ρ = some (w, b)) :
    w < first.size ∧ ∃ f, first.getD w none = some f ∧ f ≤ ρ ∧ ρ < f + rows w ∧ b = ρ - f := by
  unfold tableRow at h
  obtain ⟨a, ham, ha⟩ := List.exists_of_findSome?_eq_some h
  cases hf : first.getD a none with
  | none => rw [hf] at ha; cases ha
  | some f =>
    rw [hf] at ha
    simp only [Option.bind_some] at ha
    split at ha
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ha)
      exact ⟨List.mem_range.1 ham, f, hf, hc.1, hc.2, rfl⟩
    · cases ha

/-- Where the table finds none, the row lies in no member's block. -/
theorem tableRow_none (first : Array (Option Nat)) (rows : Nat → Nat) (ρ : Nat)
    (h : tableRow first rows ρ = none) (w : Nat) (hw : w < first.size) (f : Nat)
    (hf : first.getD w none = some f) : ¬ (f ≤ ρ ∧ ρ < f + rows w) := by
  unfold tableRow at h
  have h1 := List.findSome?_eq_none_iff.1 h w (List.mem_range.2 hw)
  rw [hf] at h1
  simp only [Option.bind_some] at h1
  intro hc
  rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hc)] at h1
  cases h1

/-! ## 2 A table laid member by member -/

/-- A row in no laid member's block holds 0. -/
theorem laid_off (first : Nat → Option Nat) (col : Nat → Array E) (skip : Nat → Bool) (ρ : Nat) :
    ∀ n, (∀ w, w < n → skip w = false → ∀ f, first w = some f →
        ¬ (f ≤ ρ ∧ ρ < f + (col w).size)) →
      (List.range n).foldl
        (fun base w => if skip w then base else putAt (first w) (col w) base)
        (fun _ => zeroE) ρ = zeroE
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := laid_off first col skip ρ n fun w hw => h w (by omega)
    cases hs : skip n with
    | true => rw [if_pos rfl]; exact ih
    | false =>
      rw [if_neg (by simp)]
      unfold putAt
      cases hf : first n with
      | none => exact ih
      | some f =>
        show (if f ≤ ρ ∧ ρ < f + (col n).size then _ else _) = _
        rw [if_neg (h n (by omega) hs f hf)]
        exact ih

/-- A row in just one laid member's block holds that member's symbol. -/
theorem laid_at (first : Nat → Option Nat) (col : Nat → Array E) (skip : Nat → Bool)
    (ρ w₀ f₀ : Nat) (hs₀ : skip w₀ = false) (hf₀ : first w₀ = some f₀)
    (hc₀ : f₀ ≤ ρ ∧ ρ < f₀ + (col w₀).size) :
    ∀ n, w₀ < n → (∀ w, w < n → w ≠ w₀ → skip w = false → ∀ f, first w = some f →
        ¬ (f ≤ ρ ∧ ρ < f + (col w).size)) →
      (List.range n).foldl
        (fun base w => if skip w then base else putAt (first w) (col w) base)
        (fun _ => zeroE) ρ = (col w₀).getD (ρ - f₀) zeroE
  | 0, hw, _ => absurd hw (Nat.not_lt_zero _)
  | n + 1, hw, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases e : w₀ = n
    · subst e
      rw [hs₀, if_neg (by simp)]
      unfold putAt
      rw [hf₀]
      show (if f₀ ≤ ρ ∧ ρ < f₀ + (col w₀).size then _ else _) = _
      rw [if_pos hc₀]
    · have ih := laid_at first col skip ρ w₀ f₀ hs₀ hf₀ hc₀ n (by omega)
        fun w hw' => h w (by omega)
      cases hs : skip n with
      | true => rw [if_pos rfl]; exact ih
      | false =>
        rw [if_neg (by simp)]
        unfold putAt
        cases hf : first n with
        | none => exact ih
        | some f =>
          show (if f ≤ ρ ∧ ρ < f + (col n).size then _ else _) = _
          rw [if_neg (h n (by omega) (fun c => e c.symm) hs f hf)]
          exact ih

/-! ## 3 The two tables at columns that hold the rows' symbols -/

/-- **The main table.** C, x: the code and the position, letters. -/
theorem mainTable_reads (L : GroupLayout) (ms : List GroupMember) (M : Nat → Rows)
    (opened : Array (Array Column)) (i ρ : Nat) (C : Fmt.M1.Code) (x : Nat)
    (hsz : L.mainFirst.size = L.members.size)
    (hkept : ∀ w, w < L.members.size → L.kept.getD w false = true →
      L.mainFirst.getD w none = none)
    (hn : ∀ w, w < L.members.size → L.kept.getD w false = false →
      (colB opened w i).main.size = (shapeOf ms w).mainRows)
    (hapart : ∀ w w', w < L.members.size → w' < L.members.size → w ≠ w' → ∀ f f',
      L.mainFirst.getD w none = some f → L.mainFirst.getD w' none = some f' →
      f + (shapeOf ms w).mainRows ≤ f' ∨ f' + (shapeOf ms w').mainRows ≤ f)
    (hcol : ∀ w, w < L.members.size → L.kept.getD w false = false →
      ∀ b, b < (shapeOf ms w).mainRows →
      readE ((colB opened w i).main.getD b zeroE) =
        symG C x ((M w).main ((shapeOf ms w).mainDeg == 3) b)
          (tailIn (M w) ((shapeOf ms w).mainDeg == 3) b)) :
    readE (mainTable L opened i ρ) = symG C x (tabMain L ms M ρ) (tabMainTl L ms M ρ) := by
  cases h : tableRow L.mainFirst (fun w => (shapeOf ms w).mainRows) ρ with
  | none =>
    have e1 : tabMain L ms M ρ = fun _ => 0 := by
      funext j
      unfold tabMain
      rw [h]
      exact OnBytes.Slice.readE_zero
    have e2 : tabMainTl L ms M ρ = fun _ => 0 := by
      funext q
      unfold tabMainTl
      rw [h]
      exact OnBytes.Slice.readE_zero
    have e3 : mainTable L opened i ρ = zeroE := by
      unfold mainTable
      exact laid_off (fun w => L.mainFirst.getD w none) (fun w => (colB opened w i).main)
        (fun w => L.kept.getD w false) ρ _ fun w hw hs f hf => by
          rw [hn w hw hs]
          exact tableRow_none _ _ _ h w (by rw [hsz]; exact hw) f hf
    rw [e1, e2, e3, symG_zero]
    exact OnBytes.Slice.readE_zero
  | some p =>
    obtain ⟨w, b⟩ := p
    obtain ⟨hw, f, hf, h1, h2, rfl⟩ := tableRow_some _ _ _ _ _ h
    rw [hsz] at hw
    have hs : L.kept.getD w false = false := by
      cases hq : L.kept.getD w false with
      | false => rfl
      | true =>
        rw [hkept w hw hq] at hf
        cases hf
    have e1 : tabMain L ms M ρ = (M w).main ((shapeOf ms w).mainDeg == 3) (ρ - f) := by
      funext j
      unfold tabMain
      rw [h]
    have e2 : tabMainTl L ms M ρ = tailIn (M w) ((shapeOf ms w).mainDeg == 3) (ρ - f) := by
      funext q
      unfold tabMainTl
      rw [h]
    have e3 : mainTable L opened i ρ = (colB opened w i).main.getD (ρ - f) zeroE := by
      unfold mainTable
      exact laid_at (fun w => L.mainFirst.getD w none) (fun w => (colB opened w i).main)
        (fun w => L.kept.getD w false) ρ w f hs hf ⟨h1, by rw [hn w hw hs]; exact h2⟩ _ hw
        fun w' hw' hne hs' f' hf' => by
          rw [hn w' hw' hs']
          rcases hapart w w' hw hw' (fun c => hne c.symm) f f' hf hf' with c | c <;> omega
    rw [e1, e2, e3]
    exact hcol w hw hs _ (by omega)

/-- **The mask table.** -/
theorem maskTable_reads (L : GroupLayout) (ms : List GroupMember) (M : Nat → Rows)
    (opened : Array (Array Column)) (i ρ : Nat) (C : Fmt.M1.Code) (x : Nat)
    (hsz : L.maskFirst.size = L.members.size)
    (hn : ∀ w, w < L.members.size → (colB opened w i).mask.size = (shapeOf ms w).maskRows)
    (hapart : ∀ w w', w < L.members.size → w' < L.members.size → w ≠ w' → ∀ f f',
      L.maskFirst.getD w none = some f → L.maskFirst.getD w' none = some f' →
      f + (shapeOf ms w).maskRows ≤ f' ∨ f' + (shapeOf ms w').maskRows ≤ f)
    (hcol : ∀ w, w < L.members.size → ∀ b, b < (shapeOf ms w).maskRows →
      readE ((colB opened w i).mask.getD b zeroE) = symG C x ((M w).mask b) ((M w).maskTl b)) :
    readE (maskTable L opened i ρ) = symG C x (tabMask L ms M ρ) (tabMaskTl L ms M ρ) := by
  cases h : tableRow L.maskFirst (fun w => (shapeOf ms w).maskRows) ρ with
  | none =>
    have e1 : tabMask L ms M ρ = fun _ => 0 := by
      funext j
      unfold tabMask
      rw [h]
      exact OnBytes.Slice.readE_zero
    have e2 : tabMaskTl L ms M ρ = fun _ => 0 := by
      funext q
      unfold tabMaskTl
      rw [h]
      exact OnBytes.Slice.readE_zero
    have e3 : maskTable L opened i ρ = zeroE := by
      unfold maskTable
      exact laid_off (fun w => L.maskFirst.getD w none) (fun w => (colB opened w i).mask)
        (fun _ => false) ρ _ fun w hw _ f hf => by
          rw [hn w hw]
          exact tableRow_none _ _ _ h w (by rw [hsz]; exact hw) f hf
    rw [e1, e2, e3, symG_zero]
    exact OnBytes.Slice.readE_zero
  | some p =>
    obtain ⟨w, b⟩ := p
    obtain ⟨hw, f, hf, h1, h2, rfl⟩ := tableRow_some _ _ _ _ _ h
    rw [hsz] at hw
    have e1 : tabMask L ms M ρ = (M w).mask (ρ - f) := by
      funext j
      unfold tabMask
      rw [h]
    have e2 : tabMaskTl L ms M ρ = (M w).maskTl (ρ - f) := by
      funext q
      unfold tabMaskTl
      rw [h]
    have e3 : maskTable L opened i ρ = (colB opened w i).mask.getD (ρ - f) zeroE := by
      unfold maskTable
      exact laid_at (fun w => L.maskFirst.getD w none) (fun w => (colB opened w i).mask)
        (fun _ => false) ρ w f rfl hf ⟨h1, by rw [hn w hw]; exact h2⟩ _ hw
        fun w' hw' hne _ f' hf' => by
          rw [hn w' hw']
          rcases hapart w w' hw hw' (fun c => hne c.symm) f f' hf hf' with c | c <;> omega
    rw [e1, e2, e3]
    exact hcol w hw _ (by omega)

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.tableRow_some
#print axioms VerifiableInference.Desc.K2.Honest.tableRow_none
#print axioms VerifiableInference.Desc.K2.Honest.laid_off
#print axioms VerifiableInference.Desc.K2.Honest.laid_at
#print axioms VerifiableInference.Desc.K2.Honest.mainTable_reads
#print axioms VerifiableInference.Desc.K2.Honest.maskTable_reads
