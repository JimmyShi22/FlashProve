-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshSymbols.lean: the symbols that a sending's part computes
(symbolsOf, Honest/K14/Sendings.lean) against the code word's symbol in the library's field (symG,
Johnson/Prover/Link/Base.lean).

  symbolsOf_congr rows that agree below the code's message length, and tails that agree below the
                  tail's length, have the same symbols
  lst_range       an entry of a list that is made over a range, read (kin of the library's lst_wr,
                  Johnson/Prover/Link/Base.lean: another list, another way of reading)
  symE_written    the format's symbol of a row of the program's elements is the WRITTEN form of symG
                  at the row and the tail as they are read: so it is a function of that one element
                  of the field
  symbolsOf_one   one row: the three words of that written form

By the library's toE_symE (OnBytes/Slice/SimBasic.lean), okE_symE (OnBytes/Slice/SimBase.lean),
okE_ofE (Johnson/Prover/Link/Base.lean) and toE_inj (OnBytes/Slice/Field.lean).

What is not claimed. Nothing on trees, columns, roots or paths. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Prover.Link.SwitchCols
import OnBytes.Slice.SimBase
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E)
open OnBytes.Slice (readE readE_def toE ofE toE_ofE toE_inj toE_symE okE_symE lst codeOf)
open Johnson.Prover.Link (symG okE_ofE words3)

/-- Rows and tails that agree where they are read have the same symbols. -/
theorem symbolsOf_congr (c : OnBytes.Code) (x n : Nat) (row row' tail tail' : Nat → Nat → E)
    (hr : ∀ r, r < n → ∀ j, j < c.ell → row r j = row' r j)
    (ht : ∀ r, r < n → ∀ t, t < c.r → tail r t = tail' r t) :
    symbolsOf c x n row tail = symbolsOf c x n row' tail' := by
  unfold symbolsOf
  refine List.flatMap_congr fun r hr' => ?_
  have hn := List.mem_range.1 hr'
  have e1 : ((List.range c.ell).map fun j => (row r j).triple) =
      (List.range c.ell).map fun j => (row' r j).triple :=
    List.map_congr_left fun j hj => by rw [hr r hn j (List.mem_range.1 hj)]
  have e2 : ((List.range c.r).map fun t => (tail r t).triple) =
      (List.range c.r).map fun t => (tail' r t).triple :=
    List.map_congr_left fun t ht' => by rw [ht r hn t (List.mem_range.1 ht')]
  simp only [e1, e2]

/-- An entry of a list that is laid over a range, read. -/
theorem lst_range (n : Nat) (f : Nat → E) (j : Nat) (h : j < n) :
    lst ((List.range n).map fun i => (f i).triple) j = readE (f j) := by
  unfold lst
  rw [readE_def]
  simp [List.getD_eq_getElem?_getD, h]

/-- **The format's symbol of a row is the written form of the library's.** -/
theorem symE_written (c : OnBytes.Code) (x : Nat) (row tail : Nat → E) :
    Fmt.M1.symE ⟨c.logN, c.ell, c.r⟩ x ((List.range c.ell).map fun j => (row j).triple)
        ((List.range c.r).map fun t => (tail t).triple) =
      ofE (symG (codeOf c) x (fun j => readE (row j)) fun t => readE (tail t)) := by
  refine toE_inj _ _ (okE_symE _ _ _ _) (okE_ofE _) ?_
  rw [toE_ofE, toE_symE]
  unfold symG
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun q hq => ?_)
    (Finset.sum_congr rfl fun j hj => ?_)
  · rw [lst_range c.r tail q (Finset.mem_range.1 hq)]
    rfl
  · rw [lst_range c.ell row j (Finset.mem_range.1 hj)]
    rfl

/-- **One row: the three words of the written symbol.** -/
theorem symbolsOf_one (c : OnBytes.Code) (x : Nat) (row tail : Nat → Nat → E) :
    symbolsOf c x 1 row tail =
      words3 (ofE (symG (codeOf c) x (fun j => readE (row 0 j)) fun t => readE (tail 0 t))) := by
  rw [← symE_written c x (row 0) (tail 0)]
  rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.symbolsOf_congr
#print axioms ProofFile.Honest.K14.lst_range
#print axioms ProofFile.Honest.K14.symE_written
#print axioms ProofFile.Honest.K14.symbolsOf_one
