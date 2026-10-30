-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotKey.lean: the proofs of the two statements of
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotKeyStatement.lean, to the letter. Lemmas; none of
the library's goals. Joinings: no new argument.

How. The first: `K1.msgTxt_mask_slot` (Honest/K1/ScriptMaskSlot.lean) rewrites the text's answer;
where the part's own cut (`K1.lentCut`, Honest/K1/ScriptAt.lean) is not there the text is silent;
where it is c, the answer is `ce` c at the number `maskStart` + ν, which lies below the part's count
(`K1.mask_in`) and so is c's own element (`K1.ce_eq`; both Honest/K1/MaskLaw.lean); the cut begins
at the owner's first element, so `cut_eAt` with `eAt_of_lt` (Honest/K2/Law/Reads.lean) carries it to
the owner's number. The second: `indexLotMeets` (IndexLotOwner.lean of this folder) at that text,
its premise on the text by the first.

It stands over another group of authors' Honest/K1/ files, which are not in this library, and over
the switches' authors' Honest/K2/Law/Reads.lean.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotKeyStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotOwner
import Johnson.Desc.ProofFile.Honest.K1.ScriptMaskSlot
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open ProofFile.Honest.K1 (msgTxt msgTxt_mask_slot lentCut dueR mask_in ce_eq)
open ProofFile.Honest.K2.Reads (cut_eAt eAt_of_lt)

/-- **Where the sender's text answers at an entry of its mask rows, it answers its own element.** -/
theorem senderAtSlot : SenderAtSlot := by
  intro Bk W Wl X ch wit J own₀ n ν hn hr hν k w hd y' h
  rw [msgTxt_mask_slot ch wit J own₀ n ν k w hd hr hν] at h
  have hi := mask_in J.P J.ride n ν hn hr hν
  cases hc : lentCut k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) with
  | none =>
    rw [hc] at h
    cases h
  | some c =>
    rw [hc] at h
    have e : c.e ⟨K1.maskStart J.P J.ride n + ν, hi⟩ = y' := by
      rw [← ce_eq _ c _ hi]
      exact Option.some.inj h
    have hc' : (k.look ch ⟨J.P.place, 0⟩).2.cut ⟨0, 0⟩ (dueR J.P J.ride) = some c := hc
    have q := cut_eAt hc' (eAt_of_lt c hi)
    rw [e] at q
    have z : (⟨0, 0⟩ : Due).e + (K1.maskStart J.P J.ride n + ν) = K1.maskStart J.P J.ride n + ν :=
      Nat.zero_add _
    rw [z] at q
    exact q

/-- **Wherever the lot and the sender's text both answer, they answer alike.** -/
theorem indexLotAgrees : IndexLotAgrees := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n' W Y wit J own₀ n ν sf hn hr hν hE
  exact indexLotMeets Bk W₀ Rc Xi Tr X ch pl P claims weights n' _ _ ⟨J.P.place, 0⟩ sf
    (K1.maskStart J.P J.ride n + ν) (msgTxt ch wit J own₀ n) hE
    (senderAtSlot Bk W (Local W₀ Rc Xi Tr) Y ch wit J own₀ n ν hn hr hν)

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.senderAtSlot
#print axioms ProofFile.Honest.K11.indexLotAgrees
