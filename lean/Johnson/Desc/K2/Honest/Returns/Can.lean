-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Can.lean: THE TEST «THE ROWS CAN BE MADE» OF A CODE SWITCH
(`rowsCan`, Johnson/Top/H0/Tw/K2/RowsCan.lean: eight clauses) SAYS YES, where the program's test on
the target has said yes and three things more hold. Statements and proofs.

  `getD_mem`        an entry of an array of numbers is among its entries
  `rowsCan_of`      of the eight: three (the codes are in the lists) follow from the test on the
                    target; one is `OldFits.named`; one is a fact on the list of positions. LEFT AS
                    PREMISES: there is one symbol for each row at each position · there is a new
                    message for each kept member · each kept member's stored sample rows read its
                    main table alone

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.Statement
import Johnson.Top.H0.Tw.K2.TargetMeans
import Johnson.Top.H0.Tw.K2.RowsCan
import OnBytes.Slice.BaseYields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open _root_.Tw.K2 (rowsCan rowsCanL readsMainOf TargetFits)

/-- An entry of an array of numbers is among its entries. -/
theorem getD_mem (a : Array Nat) {i : Nat} (hi : i < a.size) : a.getD i noId ∈ a.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  exact Array.getElem_mem_toList hi

/-- **The rows can be made.** -/
theorem rowsCan_of (S : Statement) (old : SingleRows) (T : SwitchTarget) (anew : Array Nat)
    (logN : Nat) (poss : List Nat) (y : Array E) (F : TargetFits S old T) (fits : OldFits S old)
    (hy : y.size = (Positions.ofDraws logN poss).all.size * old.rows)
    (hsz : anew.size = (switchKept old).size)
    (hread : ∀ o ∈ (switchKept old).toList,
      ∀ r ∈ (S.oracles.getD o default).sampleRows.toList, readsMainOf o r = true) :
    rowsCan S old T anew (Positions.ofDraws logN poss) y = true := by
  unfold rowsCan rowsCanL
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨by simpa using hy, decide_eq_true F.oldCode, decide_eq_true F.oldMaskCode,
    decide_eq_true F.code, by simpa using hsz, ?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro f hf
    rw [List.any_eq_true]
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (fits.named f hf)
    have hlt : i < (switchKept old).size := by
      have := (List.getElem?_eq_some_iff.1 hi).1
      simpa using this
    refine ⟨i, List.mem_range.2 hlt, ?_⟩
    rw [Array.getElem?_toList] at hi
    rw [Array.getD_eq_getD_getElem?, hi]
    simp
  · rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro r hr
    exact hread _ (getD_mem _ (List.mem_range.1 hi)) r hr
  · rw [List.all_eq_true]
    intro x hx
    have hx' : x ∈ poss := by simpa [Positions.ofDraws] using hx
    have hm : x ∈ (Positions.ofDraws logN poss).all := by
      show x ∈ (listOfT poss).toArray
      rw [listOfT_eq]
      simpa using (Fmt.listOf_mem poss x).2 hx'
    simpa using hm

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.rowsCan_of
