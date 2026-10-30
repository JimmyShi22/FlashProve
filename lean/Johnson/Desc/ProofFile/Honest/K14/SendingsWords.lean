-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsWords.lean: WHAT THE TWO SENDINGS' MAIN TABLES HOLD, IN
THIS KIND's OWN TEXT OF THE SENDINGS, WHERE THE PLAN's TEST linFits ACCEPTS AND THE MESSAGE's SHAPE
MEETS VecShape: the table that "send o_omega"'s part lays with code (wordsOf,
Honest/K14/Sendings.lean) holds, through the library's layout linLayOmega, omega_col as it is made
with code (omegaAtE, Johnson/Desc/K14/Honest/Coded.lean); and the table of "send o_u", where that
sending has messages, the folded row (uAtE), through the layout of o_u.

  omega_first, u_first   o_omega and o_u are the first messages of their sendings (u_first: where
                  "send o_u" has messages, hU)
  omega_words     **o_omega**: at the index of the entry number j, for j below the matrix's rows
  u_words         **o_u**: at the index of the entry number i, for i below the folded row's entries

Both are equations in the field, between readings (rdE.val) of the program's elements, at every
state, every list of coins and every number atPoint. By word_main_reads
(Honest/K14/SendingsTables.lean) and word_vec (Johnson/Desc/K14/Honest/SendHeld.lean).

What is assumed. linFits: the plan's own test on the linear part's shape with the codes. VecShape
(Honest/K14/SendingsRows.lean) at the message's shape. For o_u: "send o_u" has messages.
What is not claimed. Nothing on the calls of the shared sending's part
(Honest/K14/SendingsVia.lean): no file of this tree carries the two equations to the calls, and none
calls omega_words or u_words; omega_first and u_first are called (Honest/K14/SendingsViaCounts.lean,
Honest/K14/SendingsViaHolds.lean). Nothing on the entries beyond these numbers, on the pad, the
tails or the symbols. That the point which the part hears is the chain's. Nothing on a verifier's
decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E OracleNotice linLayOmega vectorLay)
open OnBytes.Slice (rdE)
open Desc.K14 (P14)
open Desc.K14.Honest (word_vec withOmega_two withU_zero)

/-- o_omega is the first message of its sending. -/
theorem omega_first (Q : P14) (n : Nat) :
    ((jobOmega ⟨Q, n⟩).Q.sent.getD 0 default).shape = Q.S.omega := by
  have sO : (jobOmega ⟨Q, n⟩).Q.sent = Desc.K14.withOmega Q.S := Desc.K14.Law.parK1_sent Q 5 _ _
  rw [sO]
  unfold Desc.K14.withOmega OnBytes.linMessageOmega
  split <;> simp

/-- **o_omega's main table holds omega_col, through the library's layout**, at the index of the
entry number j below the matrix's rows (hj), where linFits accepts (hfit) and o_omega's shape meets
VecShape (hV): at every state, every list of coins and every number n (atPoint). -/
theorem omega_words (Q : P14) (n : Nat)
    (hfit : VerifiableInference.Desc.Own.linFits Q.codes Q.S = true)
    (hV : VecShape Q.codes Q.S.omega) (t : State Ask Unit) (cs : Array E) (j : Nat)
    (hj : j < Q.S.matrixRows) :
    rdE.val (wordsOf (jobOmega ⟨Q, n⟩).Q.sent ((jobOmega ⟨Q, n⟩).rows t cs) 0 .main
        ((linLayOmega Q.codes Q.S).index j)) =
      rdE.val (Desc.K14.Honest.omegaAtE Q.S (elems (heardFrom t n 1)) t.input.rows j) := by
  obtain ⟨hs, _, _, _, _, _, hr, _⟩ :=
    (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.S).1 hfit
  have h0 := omega_first Q n
  rw [word_main_reads Q.codes (jobOmega ⟨Q, n⟩).Q.sent ((jobOmega ⟨Q, n⟩).rows t cs) 0
    Q.S.omegaRowsHigh (Desc.K14.Honest.omegaAtE Q.S (elems (heardFrom t n 1)) t.input.rows)
    (msgCoins (jobOmega ⟨Q, n⟩) cs 0) rfl (by rw [h0]; exact hV.noMask)
    (by rw [h0]; exact hV.main) (by rw [h0]; exact hV.overE) (by rw [h0]; exact hV.room), h0]
  exact word_vec Q.codes Q.S.omega Q.S.omegaRowsHigh _ _ hV.overE Q.S.matrixRows hs.2.1 hr j hj

/-- o_u is the first message of its sending, where "send o_u" has messages (hU). -/
theorem u_first (Q : P14) (n : Nat) {sentU : Array OracleNotice}
    (hU : Desc.K14.withU Q.S = some sentU) :
    ((jobU ⟨Q, n⟩).Q.sent.getD 0 default).shape = Q.S.fold.u := by
  have sU : (jobU ⟨Q, n⟩).Q.sent = (Desc.K14.withU Q.S).getD #[] := Desc.K14.Law.parK1_sent Q 2 _ _
  rw [sU, hU, Option.getD_some, Array.getD_eq_getD_getElem?, withU_zero hU]
  rfl

/-- **o_u's main table holds the folded row, through its layout**, at the index of the entry number
i below the folded row's entries (hi), where "send o_u" has messages (hU), linFits accepts (hfit)
and o_u's shape meets VecShape (hV): at every state, every list of coins and every number n
(atPoint). -/
theorem u_words (Q : P14) (n : Nat) {sentU : Array OracleNotice}
    (hU : Desc.K14.withU Q.S = some sentU)
    (hfit : VerifiableInference.Desc.Own.linFits Q.codes Q.S = true)
    (hV : VecShape Q.codes Q.S.fold.u) (t : State Ask Unit) (cs : Array E) (i : Nat)
    (hi : i < Q.S.fold.entries) :
    rdE.val (wordsOf (jobU ⟨Q, n⟩).Q.sent ((jobU ⟨Q, n⟩).rows t cs) 0 .main
        ((vectorLay Q.codes Q.S.fold.u Q.S.fold.rowsHigh).index i)) =
      rdE.val (Desc.K14.Honest.uAtE Q.S (elems (heardFrom t n 1)) t.input.rows i) := by
  obtain ⟨_, hf, _⟩ := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.S).1 hfit
  have h0 := u_first Q n hU
  rw [word_main_reads Q.codes (jobU ⟨Q, n⟩).Q.sent ((jobU ⟨Q, n⟩).rows t cs) 0
    Q.S.fold.rowsHigh (Desc.K14.Honest.uAtE Q.S (elems (heardFrom t n 1)) t.input.rows)
    (msgCoins (jobU ⟨Q, n⟩) cs 0) rfl (by rw [h0]; exact hV.noMask)
    (by rw [h0]; exact hV.main) (by rw [h0]; exact hV.overE) (by rw [h0]; exact hV.room), h0]
  exact word_vec Q.codes Q.S.fold.u Q.S.fold.rowsHigh _ _ hV.overE Q.S.fold.entries (by omega)
    hf.2.2 i hi

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.omega_first
#print axioms ProofFile.Honest.K14.omega_words
#print axioms ProofFile.Honest.K14.u_first
#print axioms ProofFile.Honest.K14.u_words
