-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/SmallBack.lean: THE SMALLNESS TEST: FROM THE LAW's SENTENCE `SmallAt` BACK TO
THE TABLE's SENTENCE ON THE RUN "small": the other way of the library's `smallAt_of_formsQA`
(Johnson/Desc/First/K8/LawSmallAhead.lean). One theorem; no definition; none of the library's goals.

  **`formsQA_of_smallAt`**   the state has a record of the test and the caller's list of tables is
                   the record's own · the reader of the run is the reader of the single equations ·
                   THE PUBLIC TEST `formsInA` SAYS YES AT THE STATE · SmallAt at the library's table
                   `cellsAhead` ⊢ `formsQA` at that run
WHY THE TEST IS A PREMISE. `formsQA` (Johnson/Desc/Sound/FormsAhead.lean) asks, beside the forms'
worth, an open segment's part, `lateOk` and `affInA` at every form: facts on the state alone, which
SmallAt does not give; `formsInA` (Johnson/Desc/First/Batch/Ahead.lean) is their test with code.
HOW. The lines of `smallAt_of_formsQA`, read the other way: `rowsAff_zero_iff`
(Johnson/Desc/First/TailClaims/SingleFormsLaw.lean), its second half.
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. NO TACTIC THAT SEARCHES.
Limits. An implication: none of its premises is paid here. Nothing on the digits.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.First.K8.LawSmallAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest

open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Tie.Pv.Tail.Port VerifiableInference.Desc
  VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.TailClaims (rowsAff)
open VerifiableInference.Desc.First.TailClaims.Law (ownWorld rowsAff_zero_iff)
open VerifiableInference.Desc.First.K8 (SmallAt cellsAhead)

variable {P Cells Tok : Type}

/-- **From the law's sentence on the run "small" back to the table's.** -/
theorem formsQA_of_smallAt (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
    (m : ℕ) (z : P) (s : S) (Rd : K9.Readers) (piece : ℕ) (run : String) {tl : HTailF2}
    (ht : s.tl? = some tl) (hf : s.funs? = some tl.funs)
    (hR : Rd.forms piece run s = K9.smallReader s) (w : Wit Cells Tok MsgT)
    (hin : K9.formsInA Rd (N.sent m) (N.group m) piece run s = true)
    (h : SmallAt (cellsAhead cs arr ms N m (z, s)) s w) :
    formsQA (N.sent m) (N.group m) Rd piece run s (seatTab cs arr ms w) := by
  have hs : Rd.forms piece run s = some { forms := rowsAff tl tl.funs, late := [] } := by
    rw [hR]
    unfold K9.smallReader
    rw [ht, hf]
  unfold K9.formsInA at hin
  rw [hs] at hin
  cases ha : K9.segAt? s with
  | none =>
    rw [ha] at hin
    exact absurd hin Bool.false_ne_true
  | some a =>
    rw [ha] at hin
    obtain ⟨hl, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
    obtain ⟨tl', ht', hv⟩ := h
    obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
    have e : cellsAhead cs arr ms N m (z, s) w =
        (worldOwn a [] (dataQA (N.sent m) (N.group m) a (seatTab cs arr ms w))).entry := by
      funext t r c
      show (match K9.segAt? s with
        | some p =>
          (worldOwn p [] (dataQA (N.sent m) (N.group m) p (seatTab cs arr ms w))).entry t r c
        | none => 0) = _
      rw [ha]
    rw [e] at hv
    exact ⟨a, _, ha, hs, hl, fun f hm => ⟨List.all_eq_true.1 hall f hm,
      (rowsAff_zero_iff Reading.gl _
        (worldOwn a [] (dataQA (N.sent m) (N.group m) a (seatTab cs arr ms w))).slot tl tl.funs
        0).2 hv f hm⟩⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.formsQA_of_smallAt
