-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5AttExp.lean

The verifier's table of exponentials at S = 12 and rx = 8 (OnBytes/Model/AttentionExp.lean:
expTable) is the library's refExp at its 2,307 rows (Inst/Model/TablesRef.lean). A closed fact, by
evaluation in Lean's kernel.

How. To evaluate the statement as it stands (the loop, which gathers the entries in an array by
pushing, and the comparison of the two lists) the kernel needs more than 16 GiB. So the loop is
first described by a test on a GIVEN list of entries ("checkL": it walks the list once and keeps one
number), the description is proved for every list ("expLoop_of_check"), and the kernel evaluates the
test alone ("check_ref").

* "refL": the list of refExp ι for ι < 2307.
* "expTable_ref": expTable 12 8 returns an array whose list of entries is refL.
* "entries_of_list": an array whose list of entries is the list of f ι for ι < n has n entries, and
  entry ι is f ι.
* "exp_of_shaped": so a shape that the verifier derives from a configuration with S = 12 and rx = 8
  ("Shaped", Johnson/Road/Lane5AttShape.lean) has u0 = 2307 and meets the hypothesis hE of
  Johnson/Road/Lane5AttLink.lean.

What is compared with what: the verifier's function, in whole numbers, with the library's table,
which is stored as data. Not claimed: anything on the table that the C++ programs compute in
floating point.

Files named above that a package may lack. Johnson/Road/Lane5AttLink.lean is in the library's full
tree; a package that is cut to what its front theorems need may not hold it. Where it lacks, "the
hypothesis hE" cannot be looked up there.

-/
import Johnson.Road.Lane5AttShape
import Inst.Model.TablesRef

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (tbRef refExp)

/-- The entry that the verifier's loop forms from its number x. -/
def vOf (S x : ℕ) : ℕ :=
  (x * 2 ^ S + 2 ^ (Attention.expDigits - 1)) / 2 ^ Attention.expDigits

/-- The loop's next number. -/
def nextX (q x : ℕ) : ℕ := x * q / 2 ^ Attention.expDigits

/-- The test: from the number x on the loop forms the entries of the list, none of them 0, and then
an entry 0. -/
def checkL (S q : ℕ) : List ℕ → ℕ → Bool
  | [], x => vOf S x == 0
  | w :: ws, x => vOf S x == w && (w != 0 && checkL S q ws (nextX q x))

/-- **If the test passes, the verifier's loop returns what it held, and then the list.** -/
theorem expLoop_of_check (S q : ℕ) :
    ∀ (ws : List ℕ) (fuel x : ℕ) (acc : Array ℕ), checkL S q ws x = true → ws.length < fuel →
      (Attention.expLoop S q fuel x acc).map Array.toList = some (acc.toList ++ ws)
  | [], fuel, x, acc, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
      have : 0 < fuel := hf
      omega⟩
    have hv : (vOf S x == 0) = true := h
    unfold Attention.expLoop
    show (if (vOf S x == 0) = true then some acc
      else Attention.expLoop S q f (nextX q x) (acc.push (vOf S x))).map Array.toList = _
    rw [if_pos hv]
    simp
  | w :: ws, fuel, x, acc, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
      have : 0 < fuel := Nat.lt_of_le_of_lt (Nat.zero_le _) hf
      omega⟩
    have h' : (vOf S x == w && (w != 0 && checkL S q ws (nextX q x))) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h'
    obtain ⟨hv, hw, hc⟩ := h'
    have hl : ws.length < f := by
      have : ws.length + 1 < f + 1 := hf
      omega
    have ih := expLoop_of_check S q ws f (nextX q x) (acc.push w) hc hl
    unfold Attention.expLoop
    show (if (vOf S x == 0) = true then some acc
      else Attention.expLoop S q f (nextX q x) (acc.push (vOf S x))).map Array.toList = _
    rw [hv, if_neg (by simpa using hw), ih]
    simp

/-- The library's table of exponentials, as a list of 2,307 numbers. -/
def refL : List ℕ := (List.range 2307).map fun ι => (refExp ((ι : ℕ) : ℤ)).toNat

/- outside the kernel the list is a letter: no step of the elaborator may unfold its entries -/
attribute [local irreducible] refL

theorem refL_length : refL.length = 2307 := by
  unfold refL
  rw [List.length_map, List.length_range]

/-- The test passes at (12, 8) on the library's list. By evaluation in the kernel. -/
theorem check_ref :
    checkL 12 (Attention.expUnit 8) refL (2 ^ Attention.expDigits) = true := by
  decide +kernel

/-- **The verifier's table of exponentials at (12, 8) is the library's.** -/
theorem expTable_ref : (Attention.expTable 12 8).map Array.toList = some refL := by
  have h := expLoop_of_check 12 (Attention.expUnit 8) refL (2 ^ 20 + 2)
    (2 ^ Attention.expDigits) #[] check_ref (by rw [refL_length]; norm_num)
  have e : (#[] : Array ℕ).toList ++ refL = refL := List.nil_append refL
  rw [e] at h
  exact h

/-- An array from its list of entries. -/
theorem entries_of_list {a : Array ℕ} {n : ℕ} {f : ℕ → ℕ}
    (h : a.toList = (List.range n).map f) : a.size = n ∧ ∀ ι < n, a.getD ι 0 = f ι := by
  obtain ⟨l⟩ := a
  have h' : l = (List.range n).map f := h
  subst h'
  refine ⟨by simp, fun ι hι => ?_⟩
  simp [Array.getD_eq_getD_getElem?, hι]

/-- **The two hypotheses on the table of exponentials**, for a shape that the verifier derives from
a configuration with S = 12 and rx = 8. -/
theorem exp_of_shaped {cf : Attention.Cfg} {S : Attention.Shape} (P : Shaped cf S)
    (h12 : cf.S = 12) (h8 : cf.rx = 8) :
    S.u0 = 2307 ∧ ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι := by
  have e : Attention.expTable 12 8 = some S.Tt := by
    rw [← h12, ← h8]
    exact P.exp
  have L := expTable_ref
  rw [e] at L
  have L' : S.Tt.toList = refL := Option.some.inj L
  unfold refL at L'
  obtain ⟨h1, h2⟩ := entries_of_list L'
  have hu : S.u0 = 2307 := P.u0.trans h1
  refine ⟨hu, fun ι hι => ?_⟩
  rw [h2 ι (hu ▸ hι)]
  exact Int.toNat_of_nonneg (le_trans (by norm_num) (le_max_left 1 _))

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.check_ref
#print axioms OnBytes.Road.L5.expTable_ref
#print axioms OnBytes.Road.L5.exp_of_shaped
