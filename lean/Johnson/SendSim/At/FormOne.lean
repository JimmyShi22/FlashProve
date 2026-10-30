-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/FormOne.lean: K1's closed form of an answer (K1.Msg.form) on an oracle message
all of whose entries but one are 0 is K1's weight at that entry times the entry, if the entry is
within the sizes.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. General lemmas on finite sums, for all codes, every shape s, all rows V of
one oracle message, every point z, every factor β and every answer number i.
  form_main_one   If every entry of the main rows but the one at (r0, j0) is 0, every entry of the
                  mask rows is 0, r0 is below the number of main rows and j0 is below 2 ^ logEll of
                  the main code, then the form is the weight at (r0, j0) times that entry.
  form_mask_one   The same with main rows and mask rows exchanged.
  form_none       If every entry of the main and the mask rows is 0, the form is 0.
  sum2_one, sum2_zero   a double sum all of whose terms but one are 0; all of whose terms are 0.

How it fits. Johnson/SendSim/At/PadsOf.lean, Johnson/SendSim/At/PadSeat.lean and
Johnson/SendSim/At/Single.lean use these to compute one message coin's contribution to an answer.
That serves mendsOf, so rowsExact (Johnson/SendSim/At/RowsExact.lean), and the model's premise
MendsOff, so rowsFresh (Johnson/SendSim/At/RowsFresh.lean) and rowsFreshAny
(Johnson/SendSim/At/FreshWideProofs.lean). The proofs rest on form_rows
(Johnson/SendSim/At/Answers.lean). K1.Msg.form is defined in Johnson/Desc/K1/Law/Law.lean.
-/
import Johnson.SendSim.At.Answers

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

theorem sum2_one (A B r0 j0 : ℕ) (hr : r0 < A) (hj : j0 < B) (f : ℕ → ℕ → GE)
    (h : ∀ r j, (r, j) ≠ (r0, j0) → f r j = 0) :
    ∑ r ∈ Finset.range A, ∑ j ∈ Finset.range B, f r j = f r0 j0 := by
  rw [Finset.sum_eq_single r0, Finset.sum_eq_single j0]
  · intro j _ hne
    exact h r0 j fun e => hne (Prod.mk.inj e).2
  · intro hn
    exact absurd (Finset.mem_range.2 hj) hn
  · intro r _ hne
    exact Finset.sum_eq_zero fun j _ => h r j fun e => hne (Prod.mk.inj e).1
  · intro hn
    exact absurd (Finset.mem_range.2 hr) hn

theorem sum2_zero (A B : ℕ) (f : ℕ → ℕ → GE) (h : ∀ r j, f r j = 0) :
    ∑ r ∈ Finset.range A, ∑ j ∈ Finset.range B, f r j = 0 :=
  Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun j _ => h r j

variable (codes : Codes) (s : OracleShape) (V : Rows) (z : ℕ → GE) (β : GE) (i : ℕ)

/-- If every entry of the main rows and of the mask rows of V is 0, K1's closed form on V is 0. -/
theorem form_none (h1 : ∀ r j, V.main (s.mainDeg == 3) r j = 0) (h2 : ∀ r j, V.mask r j = 0) :
    (K1.Msg.of codes s).form z β i (V.word s) = 0 := by
  rw [form_rows, sum2_zero _ _ _ fun r j => by rw [h1, mul_zero],
    sum2_zero _ _ _ fun r j => by rw [h2, mul_zero], add_zero]

/-- If every entry of V is 0 but the entry j0 of main row r0, with r0 and j0 within the sizes, K1's
closed form on V is K1's weight at that entry's index times the entry. -/
theorem form_main_one (r0 j0 : ℕ) (hr : r0 < s.mainRows)
    (hj : j0 < 2 ^ (codes.base.getD s.code default).logEll)
    (h1 : ∀ r j, (r, j) ≠ (r0, j0) → V.main (s.mainDeg == 3) r j = 0)
    (h2 : ∀ r j, V.mask r j = 0) :
    (K1.Msg.of codes s).form z β i (V.word s) =
      (K1.Msg.of codes s).weight z β i .main (r0 + j0 * 2 ^ K1.clog s.mainRows) *
        V.main (s.mainDeg == 3) r0 j0 := by
  rw [form_rows, sum2_one _ _ r0 j0 hr hj _ fun r j hne => by rw [h1 r j hne, mul_zero],
    sum2_zero _ _ _ fun r j => by rw [h2, mul_zero], add_zero]

/-- If every entry of V is 0 but the entry j0 of mask row r0, with r0 and j0 within the sizes, K1's
closed form on V is K1's weight at that entry's index times the entry. -/
theorem form_mask_one (r0 j0 : ℕ) (hr : r0 < s.maskRows)
    (hj : j0 < 2 ^ (codes.mask.getD s.maskCode default).logEll)
    (h1 : ∀ r j, V.main (s.mainDeg == 3) r j = 0)
    (h2 : ∀ r j, (r, j) ≠ (r0, j0) → V.mask r j = 0) :
    (K1.Msg.of codes s).form z β i (V.word s) =
      (K1.Msg.of codes s).weight z β i .mask (r0 + j0 * 2 ^ K1.clog s.maskRows) *
        V.mask r0 j0 := by
  rw [form_rows, sum2_zero _ _ _ fun r j => by rw [h1, mul_zero],
    sum2_one _ _ r0 j0 hr hj _ fun r j hne => by rw [h2 r j hne, mul_zero], zero_add]

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.form_main_one
#print axioms OnBytes.SendSim.At.form_mask_one
