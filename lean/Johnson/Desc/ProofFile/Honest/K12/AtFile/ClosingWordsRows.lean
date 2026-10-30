-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingWordsRows.lean: the rows of the carrying message, two
ways: what the switch's lot of messages lays (switchRowsLaid, Honest/K2/ScriptLots.lean), which the
thread's witness reads, and what the closing test's job lays (carryRows, K12/AtProof/JobL.lean). At
one closing, challenges and stretches they are one.

  carryRows_of_laid   where the lot's rows return, the job's text returns message 0 of them

By what. rowsAll_at (K2/Law/MaskCoin.lean): message 0 is laid of the cut at 0; mainRows at 0 does not
read the next segment's own messages.

Hypotheses. hV: the lot's rows return. hc: the stretches that the job hands the closing are those
that the switch's part is handed. h0: the sending has a message. hf: message 0 is no fold's fresh
mask. hown: the job's own stretch is the cut at 0 of the part's own coins.

Limits. At one closing: that the thread's witness and the job read the same challenges, and that the
coins agree, is asked here. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobL
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K2.Honest (mainRows zeroG)
open ProofFile.Honest.K2.Law (SwitchCoins)

variable {W₀ Rc Xi Tr X : Type}

/-- **Where the lot's rows return, the job's text returns message 0 of them.** -/
theorem carryRows_of_laid {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {closing : K2.Closing} {p : K2.SwitchPlace} {w : Local W₀ Rc Xi Tr}
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} {h : List Fmt.Drawn}
    {mem : ℕ → Stretch} {V : ℕ → Johnson.Prover.Send.Rows}
    (hV : K2.switchRowsLaid D readers closing p c w h = .ok V)
    (hc : (fun n => match p.front[n]? with
        | some x => Except.ok (asK2 x.2.2 (mem n))
        | none => Except.error "a stretch is asked beyond the list") =
      K2.Stretch.carried p.carries c.2.2)
    (h0 : 0 < (K2.switchSent p.sizes p.others).size)
    (hf : K2.foldAt (K2.switchFresh p.sizes p.others p.foldVars) 0 = none)
    (hown : ∀ c', c.1.cut (K2.dueBefore p.sizes.codes (K2.switchSent p.sizes p.others)
          (K2.switchFresh p.sizes p.others p.foldVars) 0)
        (K2.messageDue p.sizes.codes ((K2.switchSent p.sizes p.others).getD 0 default).shape
          (K2.foldAt (K2.switchFresh p.sizes p.others p.foldVars) 0)) = some c' →
      (⟨_, c'⟩ : K2.Stretch) =
        asK2 (K2.messageDue p.sizes.codes (shapeL p) none) (mem p.front.length)) :
    carryRows D readers closing p w h mem = .ok (V 0) := by
  unfold K2.switchRowsLaid at hV
  split at hV
  · cases hV
  split at hV
  · cases hV
  obtain ⟨M, hM, hV'⟩ := K2.Reads.bind_ok' hV
  unfold K2.switchRowsAt at hM
  obtain ⟨W, hW, rfl⟩ := K2.Reads.map_ok hM
  have hW' : closing p (D w.x) (readers w) h (fun n => match p.front[n]? with
      | some x => Except.ok (asK2 x.2.2 (mem n))
      | none => Except.error "a stretch is asked beyond the list") = .ok W := by
    rw [hc]
    simpa [K2.switchWit] using hW
  obtain ⟨c', hcut, hmsg⟩ := K2.rowsAll_at hV' h0
  rw [hown c' hcut, hf] at hmsg
  unfold carryRows
  erw [hW']
  exact hmsg

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carryRows_of_laid
