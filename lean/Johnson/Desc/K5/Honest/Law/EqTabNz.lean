-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/EqTabNz.lean: WHEN NO ENTRY OF A TABLE OF EQUALITY WEIGHTS IS THE WORD 0.
On the verifier's own functions `eqTab` and `blockRows` (Johnson/Desc/First/Att/Geo.lean); no
prover, no state, no chain in it.

Why. At an attention segment the weights of two of the verifier's tables are a table of equality
weights, and a product of two such tables, of challenges that the segment's own rounds draw. A test
of the smallness test's kind asks that a weight "is not the word 0" (`isZeroE`: all three words
are 0).

How. A word that does not READ 0 is not the word 0: the word 0 reads 0. What an entry of `eqTab` z
reads is the product, over z's coordinates, of the coordinate's reading v or of 1 - v
(`read_eqTab`, Johnson/Desc/K5/Honest/Law/Cells.lean). So no word of a table need be below the
prime: it is enough that each coordinate reads neither 0 nor 1.

Main names:
  `isOneE`, `nz01`: a test with code on one element's three words: they are below the prime, and
    the element is neither the word 0 nor the word 1.
  `nz01_val`: what passes it reads neither 0 nor 1, at the reading `Reading.gl`.
  `notZero_of_val`: what does not read 0 is not the word 0.
  `eqN_ne_zero`, `eqTab_nz`: **at a point none of whose coordinates reads 0 or 1 no entry of the
    table is the word 0.**
  `blockRows_nz`, `blockRows_eq_nz`: the like for a product of two tables.

Limits. Sufficient, not necessary, in the words: an element with a word that is not below the prime
fails `nz01` whatever it reads. Nothing on how an element is drawn, and no count.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Cells
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E mulE zeroE oneE okE isZeroE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (eqTab blockRows)

/-- All three words are those of the element 1. -/
def isOneE (w : E) : Bool := w.c0 == 1 && w.c1 == 0 && w.c2 == 0

/-- **The test on one element**: its words are below the prime; it is neither the word 0 nor the
word 1. -/
def nz01 (w : E) : Bool := okE w && !isZeroE w && !isOneE w

/-- What passes the test reads neither 0 nor 1. Conditional: h. -/
theorem nz01_val {w : E} (h : nz01 w = true) :
    Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1 := by
  unfold nz01 at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hk, h0⟩, h1⟩ := h
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [(OnBytes.Slice.isZeroE_iff w hk).2 e] at h0
    exact nomatch h0
  · have e1 : w = oneE :=
      OnBytes.Slice.readE_inj w oneE hk rfl (e.trans Reading.gl.one.symm)
    rw [e1] at h1
    exact nomatch h1

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- What does not read 0 is not the word 0. Conditional: h. -/
theorem notZero_of_val {w : E} (h : ρ.val w ≠ 0) : isZeroE w = false := by
  cases hz : isZeroE w with
  | false => rfl
  | true => exact absurd (by rw [(OnBytes.Slice.isZeroE_eq _).1 hz, ρ.zero]) h

/-- The equality weight at a point none of whose coordinates is 0 or 1 is not 0. -/
theorem eqN_ne_zero {n : ℕ} {v : ℕ → K} (hv : ∀ j < n, v j ≠ 0 ∧ v j ≠ 1) (c : ℕ) :
    Blocks.eqN n 0 v c ≠ 0 := by
  unfold Blocks.eqN
  refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
  have h1 := hv t (Finset.mem_range.1 ht)
  rw [Nat.zero_add]
  split
  · exact h1.1
  · exact sub_ne_zero.2 (Ne.symm h1.2)

/-- An entry of the table does not read 0. Conditional: hz: no coordinate reads 0 or 1; hc. -/
theorem eqTab_val_ne {z : Array E} (hz : ∀ j < z.size, pt ρ z j ≠ 0 ∧ pt ρ z j ≠ 1) {c : ℕ}
    (hc : c < 2 ^ z.size) : ρ.val ((eqTab z).getD c zeroE) ≠ 0 := by
  rw [read_eqTab ρ rfl (fun _ _ => rfl) hc]
  exact eqN_ne_zero hz c

/-- **No entry of a table of equality weights is the word 0**, at a point none of whose coordinates
reads 0 or 1. Conditional: hz; hc: the entry's number is below the table's length. -/
theorem eqTab_nz {z : Array E} (hz : ∀ j < z.size, pt ρ z j ≠ 0 ∧ pt ρ z j ≠ 1) {c : ℕ}
    (hc : c < 2 ^ z.size) : isZeroE ((eqTab z).getD c zeroE) = false :=
  notZero_of_val ρ (eqTab_val_ne ρ hz hc)

/-- An entry of a product of two tables is not the word 0 where neither factor reads 0. -/
theorem blockRows_nz (low tk : Array E) {r i : ℕ} (hr : r < low.size) (hi : i < tk.size)
    (h1 : ρ.val (low.getD r zeroE) ≠ 0) (h2 : ρ.val (tk.getD i zeroE) ≠ 0) :
    isZeroE ((blockRows low tk).getD (r * tk.size + i) zeroE) = false := by
  have e : (blockRows low tk).getD (r * tk.size + i) zeroE =
      mulE (low.getD r zeroE) (tk.getD i zeroE) := OnBytes.Road.blockRows_getD low tk hr hi
  rw [e]
  exact notZero_of_val ρ (by rw [ρ.mul]; exact mul_ne_zero h1 h2)

/-- **No entry of a product of two tables of equality weights is the word 0**, at two points none of
whose coordinates reads 0 or 1. Conditional: ha, hb; hx: the entry's number is below the product's
length. -/
theorem blockRows_eq_nz {a b : Array E} (ha : ∀ j < a.size, pt ρ a j ≠ 0 ∧ pt ρ a j ≠ 1)
    (hb : ∀ j < b.size, pt ρ b j ≠ 0 ∧ pt ρ b j ≠ 1) {x : ℕ}
    (hx : x < 2 ^ a.size * 2 ^ b.size) :
    isZeroE ((blockRows (eqTab a) (eqTab b)).getD x zeroE) = false := by
  have hB : 0 < 2 ^ b.size := Nat.two_pow_pos _
  have h1 : x / 2 ^ b.size < 2 ^ a.size := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  have h2 : x % 2 ^ b.size < 2 ^ b.size := Nat.mod_lt _ hB
  have e := blockRows_nz ρ (eqTab a) (eqTab b) (r := x / 2 ^ b.size) (i := x % 2 ^ b.size)
    (by rw [size_eqTab]; exact h1) (by rw [size_eqTab]; exact h2) (eqTab_val_ne ρ ha h1)
    (eqTab_val_ne ρ hb h2)
  rw [size_eqTab, Nat.div_add_mod' x (2 ^ b.size)] at e
  exact e

end

end H2K5.Honest

#print axioms H2K5.Honest.nz01_val
#print axioms H2K5.Honest.notZero_of_val
#print axioms H2K5.Honest.eqN_ne_zero
#print axioms H2K5.Honest.eqTab_val_ne
#print axioms H2K5.Honest.eqTab_nz
#print axioms H2K5.Honest.blockRows_nz
#print axioms H2K5.Honest.blockRows_eq_nz
