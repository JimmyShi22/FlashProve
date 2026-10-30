-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchCols.lean: the tree that an honest prover sends at a code switch into a
stage that is not the last, column by column, as functions; and that the format's cut of such a
column reads the code words' symbols back.

A column of a later stage's tree holds (`cutCol`, `stageCol`, Fmt/M1Types.lean): a symbol of each of
the stage's 2^k main rows, three words each; then a symbol of each of its 2^h carried mask rows;
then a symbol of each of the 2^h rows of the next fold's mask, which rides in the same tree.

Main names (namespace `Johnson.Prover.Link`).
  `words3`, `wordsOf`   an element's three words; a list of elements as a list of words
  `sym3_wordsOf`, `length_wordsOf`   the symbol that begins at word 3 i is the list's entry i
  `mainSym`, `maskSym`, `freshSym`   the symbols at the position x: of main row b (the main table's
      entries b + 2^k j, with the tail tM b), of carried mask row b (the mask table's entries
      b + 2^h j, with tZ b), of row b of the rider (fM b with fT b); mask rows at x modulo the mask
      code's length
  `stageColW`   the column's words
  `stageCol_written`   the format's cut returns a column whose entries read as these symbols
  `lt_stageColW`   every word of the column is below the prime

By: `stageCol_some` (OnBytes/Slice/BlkCuts.lean), `stageCol_inv` (OnBytes/Slice/BlkColumns.lean).

Limits. The last stage's column is another (`baseColW`, Johnson/Prover/Link/Base.lean). That these
symbols are those of the library's encoders (`ldOf`, `ldRep`) is not shown here. Nothing on how a
tail or the rider's rows are chosen; nothing on trees, salts or hashes. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchMsg
import OnBytes.Slice.BlkCuts
import OnBytes.Slice.BlkColumns

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes.Slice Cb
open VerifiableInference.Desc (fieldPrimeWord)

/-- An element's three words. -/
def words3 (e : Fmt.M1.E) : List UInt64 := [e.1, e.2.1, e.2.2]

/-- A list of elements as a list of words. -/
def wordsOf (l : List Fmt.M1.E) : List UInt64 := l.flatMap words3

theorem length_wordsOf : ∀ l : List Fmt.M1.E, (wordsOf l).length = 3 * l.length
  | [] => rfl
  | e :: l => by
    show (words3 e ++ wordsOf l).length = _
    rw [List.length_append, length_wordsOf l, List.length_cons]
    show 3 + 3 * l.length = _
    omega

/-- The symbol that begins at word 3 i is the list's entry i. -/
theorem sym3_wordsOf : ∀ (l : List Fmt.M1.E) (i : ℕ), i < l.length →
    sym3 (wordsOf l) (3 * i) = l.getD i Fmt.Fld.zeroE
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | e :: l, i + 1, h => by
    show sym3 (e.1 :: e.2.1 :: e.2.2 :: wordsOf l) (3 * (i + 1)) = _
    rw [show 3 * (i + 1) = 3 * i + 3 by omega, sym3_cons3,
      sym3_wordsOf l i (Nat.lt_of_succ_lt_succ h)]
    rfl

variable (s' : Sg) (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE) (x : ℕ)

/-- Main row b's symbol at the position x. -/
def mainSym (b : ℕ) : GE := symG s'.C x (fun j => tabM (b + 2 ^ (s'.h + s'.g) * j)) (tM b)

/-- Carried mask row b's symbol. -/
def maskSym (b : ℕ) : GE := symG s'.Z (x % 2 ^ s'.Z.a) (fun j => tabZ (b + 2 ^ s'.h * j)) (tZ b)

/-- The symbol of row b of the rider: the next fold's mask. -/
def freshSym (b : ℕ) : GE := symG s'.Z (x % 2 ^ s'.Z.a) (fM b) (fT b)

/-- **The column's words.** -/
def stageColW : List UInt64 :=
  wordsOf (wr (2 ^ (s'.h + s'.g)) (mainSym s' tabM tM x) ++
    (wr (2 ^ s'.h) (maskSym s' tabZ tZ x) ++ wr (2 ^ s'.h) (freshSym s' fM fT x)))

/-- **The format's cut reads the symbols back.** -/
theorem stageCol_written : ∃ col,
    Fmt.M1.stageCol s'.st 0 (2 ^ s'.st.k) (stageColW s' tabM tabZ tM tZ fM fT x) = some col ∧
    (∀ b, b < 2 ^ (s'.h + s'.g) → vec col.main b = mainSym s' tabM tM x b) ∧
    (∀ b, b < 2 ^ s'.h → vec col.mask b = maskSym s' tabZ tZ x b) ∧
    ∀ b, b < 2 ^ s'.h → vec col.fresh b = freshSym s' fM fT x b := by
  have hlen : (wr (2 ^ (s'.h + s'.g)) (mainSym s' tabM tM x) ++
      (wr (2 ^ s'.h) (maskSym s' tabZ tZ x) ++ wr (2 ^ s'.h) (freshSym s' fM fT x))).length =
      2 ^ (s'.h + s'.g) + (2 ^ s'.h + 2 ^ s'.h) := by
    rw [List.length_append, List.length_append, length_wr, length_wr, length_wr]
  obtain ⟨col, hcol⟩ := stageCol_some s'.st (2 ^ s'.st.k) (stageColW s' tabM tabZ tM tZ fM fT x) (by
    unfold stageColW
    rw [length_wordsOf, hlen]
    show 3 * (2 ^ (s'.h + s'.g) + (2 ^ s'.h + 2 ^ s'.h)) =
      3 * 2 ^ (s'.h + s'.g) + 3 * (2 * 2 ^ s'.h)
    omega)
  obtain ⟨i1, -, i3, i4⟩ := stageCol_inv s'.st (2 ^ s'.st.k) _ col hcol
  refine ⟨col, hcol, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
  · rw [i1 b hb hb]
    unfold stageColW
    rw [sym3_wordsOf _ _ (by rw [hlen]; exact Nat.lt_of_lt_of_le hb (Nat.le_add_right _ _))]
    show lst _ b = _
    rw [lst_append, if_pos (by rw [length_wr]; exact hb), lst_wr _ _ _ hb]
  · rw [i3 b hb]
    unfold stageColW
    rw [sym3_wordsOf _ _ (by
      rw [hlen]
      show 2 ^ (s'.h + s'.g) + b < _
      omega)]
    show lst _ (2 ^ (s'.h + s'.g) + b) = _
    rw [lst_append, if_neg (by rw [length_wr]; omega), length_wr,
      show 2 ^ (s'.h + s'.g) + b - 2 ^ (s'.h + s'.g) = b by omega, lst_append,
      if_pos (by rw [length_wr]; exact hb), lst_wr _ _ _ hb]
  · rw [i4 b hb]
    unfold stageColW
    rw [sym3_wordsOf _ _ (by
      rw [hlen]
      show 2 ^ (s'.h + s'.g) + 2 ^ s'.h + b < _
      omega)]
    show lst _ (2 ^ (s'.h + s'.g) + 2 ^ s'.h + b) = _
    rw [lst_append, if_neg (by rw [length_wr]; omega), length_wr,
      show 2 ^ (s'.h + s'.g) + 2 ^ s'.h + b - 2 ^ (s'.h + s'.g) = 2 ^ s'.h + b by omega,
      lst_append, if_neg (by rw [length_wr]; omega), length_wr,
      show 2 ^ s'.h + b - 2 ^ s'.h = b by omega, lst_wr _ _ _ hb]

/-- Every word of a list of written elements is below the prime. -/
theorem lt_wordsOf_wr (l : List Fmt.M1.E) (h : ∀ e ∈ l, ∃ y : GE, e = ofE y) :
    ∀ w ∈ wordsOf l, w < fieldPrimeWord := by
  intro w hw
  obtain ⟨e, he, hw'⟩ := List.mem_flatMap.1 hw
  obtain ⟨y, rfl⟩ := h e he
  simp only [words3, ofE, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with h | h | h <;> rw [h] <;> exact lt_ofF _

theorem mem_wr (n : ℕ) (f : ℕ → GE) : ∀ e ∈ wr n f, ∃ y : GE, e = ofE y := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
  exact ⟨_, rfl⟩

/-- **Every word of the column is below the prime.** -/
theorem lt_stageColW : ∀ w ∈ stageColW s' tabM tabZ tM tZ fM fT x, w < fieldPrimeWord :=
  lt_wordsOf_wr _ fun e he => by
    rcases List.mem_append.1 he with h | h
    · exact mem_wr _ _ e h
    · rcases List.mem_append.1 h with h | h
      · exact mem_wr _ _ e h
      · exact mem_wr _ _ e h

end Johnson.Prover.Link
