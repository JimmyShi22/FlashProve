-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/Clamp/BlockCovers.lean: an index J of a table that a block of the request's
layout WEIGHS (`K9L.inBlock b R P J` is not 0: Johnson/Desc/First/Batch/Law/Laid.lean) is one that
the block COVERS by the programs' own test (`laidCovers`, OnBytes/Iop/ReqRows.lean); so, at a block
of an oracle message's layout, it lies inside the message's main rows and places. Statements and
proofs; one placeholder block with an example and a negative example.

What it pays. The sentences on linear forms are the same at the reader of the witness that is
clamped to each oracle message's own ranges and at the reader that is not, given that every index
which a block holds lies inside the ranges of the member at its seat. A cell of the data weighs
entry J by `inBlock`; the geometry (Johnson/Goal/Meaning/LaidInside.lean) speaks by
`laidCovers`. This file is the step between.

  `stretch_of_div`   a number whose quotient by 2 ^ k is that of an aligned f lies in [f, f + 2 ^ k)
  `inBlock_covers`   at a block that passes `laidBlockOk b R P`, at J < 2 ^ (R + P): a weight that
                     is not 0 gives `laidCovers b R J = true`
  `inBlock_inside`   with `Meaning.block_of_message`: at a block of an array in an oracle message
                     whose layout passes `reqMessageLayoutOk`: J's row is below the message's main
                     rows, its place below 2 ^ logEll
  `toyBlock`, `toy_ok`, `toy_in`, `toy_covers`: an example: a block of two rows and two places in a
                     table of four by four passes the test; at J = 10 its weight is 1, and it covers
                     J
  `toy_out`, `toy_not`: a negative example: at J = 0 the weight is 0, and it does not cover J
Limits. Main rows alone: nothing on mask entries. Nothing says that a given layout passes the tests.
Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.Laid
import Johnson.Goal.Meaning.LaidInside
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray)

/-- A number whose quotient by 2 ^ k is that of an aligned f lies in the stretch of 2 ^ k from f. -/
theorem stretch_of_div {x f k : ℕ} (hal : f % 2 ^ k = 0) (h : x / 2 ^ k = f / 2 ^ k) :
    f ≤ x ∧ x < f + 2 ^ k := by
  have hx := Nat.div_add_mod x (2 ^ k)
  have hf := Nat.div_add_mod f (2 ^ k)
  have hl := Nat.mod_lt x (Nat.two_pow_pos k)
  rw [h] at hx
  rw [hal] at hf
  generalize 2 ^ k * (f / 2 ^ k) = A at hx hf
  omega

/-- **An index that a block weighs is one that the block covers.** -/
theorem inBlock_covers (b : LaidBlock) (R P J : ℕ) (hok : laidBlockOk b R P = true)
    (hJ : J < 2 ^ (R + P)) (h : (K9L.inBlock b R P J : GQ) ≠ 0) : laidCovers b R J = true := by
  have F := K9L.blockFacts b R P hok
  have hc : J / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) =
        b.firstRow / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) ∧
      J / 2 ^ (R + b.placeBits) % 2 ^ (P - b.placeBits) =
        b.firstPlace / 2 ^ b.placeBits % 2 ^ (P - b.placeBits) := by
    unfold K9L.inBlock at h
    by_contra hn
    apply h
    rcases not_and_or.1 hn with n | n
    · rw [if_neg n, zero_mul]
    · rw [if_neg n, mul_zero]
  obtain ⟨c1, c2⟩ := hc
  have pR : 2 ^ R = 2 ^ b.rowBits * 2 ^ (R - b.rowBits) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' F.hR]
  have pP : 2 ^ P = 2 ^ b.placeBits * 2 ^ (P - b.placeBits) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' F.hP]
  have r1 : J % 2 ^ R / 2 ^ b.rowBits = b.firstRow / 2 ^ b.rowBits := by
    rw [pR, Nat.mod_mul_right_div_self, c1]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pR]; exact F.rowLt))
  have hpl : J / 2 ^ R < 2 ^ P := Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hJ)
  have r2 : J / 2 ^ R / 2 ^ b.placeBits = b.firstPlace / 2 ^ b.placeBits := by
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pP]; exact hpl)),
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← pP]; exact F.placeLt))] at c2
    exact c2
  obtain ⟨a1, a2⟩ := stretch_of_div F.alRow r1
  obtain ⟨a3, a4⟩ := stretch_of_div F.alPlace r2
  unfold laidCovers
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩

/-- **So it lies inside the oracle message's main rows and places.** -/
theorem inBlock_inside {codes : Codes} {o : OracleShape} {inIt : List ReqArray}
    (hM : reqMessageLayoutOk codes o inIt = true) {A : ReqArray} (hA : A ∈ inIt) {b : LaidBlock}
    (hb : b ∈ A.blocks) (J : ℕ)
    (hJ : J < 2 ^ (ceilLog2 o.mainRows + (codes.base.getD o.code default).logEll))
    (h : (K9L.inBlock b (ceilLog2 o.mainRows) (codes.base.getD o.code default).logEll J : GQ) ≠
      0) :
    J % 2 ^ ceilLog2 o.mainRows < o.mainRows ∧
      J / 2 ^ ceilLog2 o.mainRows < 2 ^ (codes.base.getD o.code default).logEll := by
  obtain ⟨pad, -, -, hok, hrow, -⟩ := _root_.Meaning.block_of_message hM hA hb
  have hc := inBlock_covers b _ _ J hok hJ h
  unfold laidCovers at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨Nat.lt_of_lt_of_le hc.1.1.2 hrow,
    Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hJ)⟩

/-! ### An example and a negative example -/

/-- A placeholder: the rows 2, 3 and the places 2, 3 of a table of four rows and four places. -/
def toyBlock : LaidBlock :=
  { firstI := 0, firstC := 0, firstRow := 2, firstPlace := 2, bitsI := 1, bitsC := 1, rowBits := 1
    placeBits := 1, iIsLow := true }

theorem toy_ok : laidBlockOk toyBlock 2 2 = true := by decide

/-- At J = 10 (row 2, place 2) the weight is 1. -/
theorem toy_in : (K9L.inBlock toyBlock 2 2 10 : GQ) = 1 := by
  unfold K9L.inBlock
  rw [if_pos (by decide), if_pos (by decide), one_mul]

theorem toy_covers : laidCovers toyBlock 2 10 = true := by decide

/-- At J = 0 the weight is 0. -/
theorem toy_out : (K9L.inBlock toyBlock 2 2 0 : GQ) = 0 := by
  unfold K9L.inBlock
  rw [if_neg (by decide), zero_mul]

theorem toy_not : laidCovers toyBlock 2 0 = false := by decide

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.stretch_of_div
#print axioms VerifiableInference.Desc.Sound.inBlock_covers
#print axioms VerifiableInference.Desc.Sound.inBlock_inside
#print axioms VerifiableInference.Desc.Sound.toy_ok
#print axioms VerifiableInference.Desc.Sound.toy_in
#print axioms VerifiableInference.Desc.Sound.toy_covers
#print axioms VerifiableInference.Desc.Sound.toy_out
#print axioms VerifiableInference.Desc.Sound.toy_not
