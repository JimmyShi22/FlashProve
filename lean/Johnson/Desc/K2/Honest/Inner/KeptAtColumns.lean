-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Inner/KeptAtColumns.lean: the kind "the code switch" (K2): THE KEPT MEMBERS'
SYMBOLS AT ONE POSITION (`keptSymbols`, OnBytes/Iop/SymbolLaws.lean), ENTRY BY ENTRY, AGAINST THE
KEPT ROWS OF THE COMPLEX OF SINGLE ROWS (`rowOfComplex`, Inner/Statement.lean). Lemmas; NONE OF THE
LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  `rowOfComplex_kept`  a kept row of the complex
  `flatMap_if_filter`, `keptList_at`  on lists: which entry of the kept members' lists, laid flat, a
      kept row (member a, row b) is
  **`keptSymbols_reads`**  the sizes' kept shapes are the layout's kept members' · each such column
      has as many main symbols as the member has rows, and symbol b reads as the symbol of row b of
      `W.kept a` ⊢ kept symbol n reads as the symbol of row 1 + n of the complex
Limits. All three are premises. W, the shapes and the position are letters. One position.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K2.Honest.Inner.SymbolsOfTables
import Johnson.Top.H0.K2Hears.KeptAtIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE codeOf)
open Johnson.Prover.Link (symG)

set_option quotPrecheck false in
/-- The kept rows, by member and row, as `rowOfComplex` lists them. -/
local notation "keptList" Z =>
  ((Sizes.kept Z).zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b))

/-- A kept row of the complex. -/
theorem rowOfComplex_kept (Z : Sizes) (W : Left) (n : Nat) (x : Nat × Nat)
    (h : (keptList Z)[n]? = some x) :
    rowOfComplex Z W (1 + n) =
      (codeOf (Z.codes.base.getD Z.code default), (W.kept x.1).main x.2,
        (W.kept x.1).tail x.2) := by
  unfold rowOfComplex
  dsimp only
  split
  · rename_i h0
    exact absurd (beq_iff_eq.1 h0) (by omega)
  · rw [show 1 + n - 1 = n by omega, h]

/-- Lists laid flat where a test says yes: the lists of the members that pass, laid flat. -/
theorem flatMap_if_filter {α : Type} (p : Nat → Bool) (g : Nat → List α) :
    ∀ l : List Nat, (l.flatMap fun w => if p w then g w else []) = (l.filter p).flatMap g
  | [] => rfl
  | w :: l => by
    rw [List.flatMap_cons, flatMap_if_filter p g l]
    cases h : p w with
    | true => rw [if_pos rfl, List.filter_cons_of_pos h, List.flatMap_cons]
    | false => rw [if_neg (by simp), List.filter_cons_of_neg (by simp [h]), List.nil_append]

/-- **Which entry of the lists laid flat a kept row is.** nos: the kept members' numbers. sh: their
shapes. col: their lists, each as long as its member has main rows. -/
theorem keptList_at {α : Type} (sh : Nat → OracleShape) (col : Nat → List α) :
    ∀ (nos : List Nat) (k n a b : Nat), (∀ w ∈ nos, (col w).length = (sh w).mainRows) →
      (((nos.map sh).zipIdx k).flatMap fun s =>
        (List.range s.1.mainRows).map fun b => (s.2, b))[n]? = some (a, b) →
      ∃ w, nos[a - k]? = some w ∧ k ≤ a ∧ b < (sh w).mainRows ∧
        (nos.flatMap col)[n]? = (col w)[b]?
  | [], k, n, a, b, _, h => by simp at h
  | w :: nos, k, n, a, b, hl, h => by
    rw [List.map_cons, List.zipIdx_cons, List.flatMap_cons] at h
    by_cases hn : n < (sh w).mainRows
    · rw [List.getElem?_append_left (by simpa using hn), List.getElem?_map,
        List.getElem?_range hn] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨w, by simp, Nat.le_refl _, hn, ?_⟩
      rw [List.flatMap_cons,
        List.getElem?_append_left (by rw [hl w List.mem_cons_self]; exact hn)]
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hn)] at h
      simp only [List.length_map, List.length_range] at h
      obtain ⟨w', h1, h2, h3, h4⟩ := keptList_at sh col nos (k + 1) (n - (sh w).mainRows) a b
        (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h
      refine ⟨w', ?_, by omega, h3, ?_⟩
      · rw [show a - k = (a - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
        exact h1
      · rw [List.flatMap_cons,
          List.getElem?_append_right (by rw [hl w List.mem_cons_self]; exact Nat.le_of_not_lt hn),
          hl w List.mem_cons_self]
        exact h4

/-- **The kept symbols.** sh: the members' shapes, by their numbers in the layout. -/
theorem keptSymbols_reads (Z : Sizes) (W : Left) (L : GroupLayout) (opened : Array (Array Column))
    (i x : Nat) (sh : Nat → OracleShape) (hZk : Z.kept = (Own.keptNos L).map sh)
    (hn : ∀ w ∈ Own.keptNos L, (colB opened w i).main.size = (sh w).mainRows)
    (hcol : ∀ a w, (Own.keptNos L)[a]? = some w → ∀ b, b < (sh w).mainRows →
      readE ((colB opened w i).main.getD b zeroE) =
        symG (codeOf (Z.codes.base.getD Z.code default)) x ((W.kept a).main b) ((W.kept a).tail b))
    (n : Nat) (hlt : n < (keptList Z).length) :
    readE ((keptSymbols L opened i).getD n zeroE) =
      symG (rowOfComplex Z W (1 + n)).1 x (rowOfComplex Z W (1 + n)).2.1
        (rowOfComplex Z W (1 + n)).2.2 := by
  obtain ⟨⟨a, b⟩, hab⟩ : ∃ p, (keptList Z)[n]? = some p := ⟨_, List.getElem?_eq_getElem hlt⟩
  rw [rowOfComplex_kept Z W n (a, b) hab]
  rw [hZk] at hab
  obtain ⟨w, h1, -, h3, h4⟩ := keptList_at sh (fun w => (colB opened w i).main.toList)
    (Own.keptNos L) 0 n a b (fun w hw => by rw [Array.length_toList]; exact hn w hw) hab
  have e : keptSymbols L opened i =
      (Own.keptNos L).flatMap fun w => (colB opened w i).main.toList := by
    unfold keptSymbols Own.keptNos
    exact flatMap_if_filter _ _ _
  rw [e, List.getD_eq_getElem?_getD, h4, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]
  exact hcol a w h1 b h3

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.rowOfComplex_kept
#print axioms VerifiableInference.Desc.K2.Honest.flatMap_if_filter
#print axioms VerifiableInference.Desc.K2.Honest.keptList_at
#print axioms VerifiableInference.Desc.K2.Honest.keptSymbols_reads
