-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/OneStored.lean: the code switch: EACH KEPT OLD ORACLE MESSAGE HAS JUST
ONE STORED OOD CLAIM: the premise hone of rows_debts (Johnson/Top/H0/Tw/K2C/RowsDebts.lean),
whose own head says that none of the table's fixed tests gives it: FROM THE TWO INVARIANTS ON STORED
SAMPLE ROWS.
  one_stored   a message whose shape counts one answer has just one stored sample row: «at least
               one» by AnsweredStored (K2Hands/AnsweredStored.lean), «as many as the shape's
               answers» by the first clause of RowsAre (K2Hears/SentRows.lean) inside
               SampleGoodS (Johnson/Top/H/SwitchSeedFits.lean)
  hone_of_both  the same at every entry of a list of kept places, in hone's own letters
WHO PAYS THE PREMISES. hG, hA: both_in_scope (BothInScope.lean) at the border's state, carried to
the front's statement (K2Caller/FrontSide.lean has the road). h: at each kept place's own number the
statement has a message whose shape counts one answer: hx_of with shape_of
(Johnson/G/SwitchSampleTop.lean :120-131, read), from the tests storedB and keptShapeB: THESE SPEAK
OF THE ENTRY AT EACH TYPED KEPT MEMBER's PLACE: that every entry of the frame's list is such a one
(the list is as long as the typed list of kept members) goes with them.
LIMITS. Two short laws. Nothing is shown at a real value. No soundness is claimed.
-/
import Johnson.Top.H.SwitchSeedFits
import Johnson.Top.H0.K2Hands.AnsweredStored

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model

theorem one_stored {St : Statement} (hG : SampleGoodS St) (hA : AnsweredStored St) {o : Nat}
    {xo : OnBytes.Oracle} (hx : St.oracles[o]? = some xo) (ha : xo.shape.answers = 1) :
    (St.oracles.getD o default).sampleRows.size = 1 := by
  have hn : xo.sampleRows.size ≠ 0 := hA o xo hx (by rw [ha]; decide)
  obtain ⟨seeds, hr, -⟩ := hG o xo hx hn
  rw [Array.getD_eq_getD_getElem?, hx]
  exact hr.1.trans ha

theorem hone_of_both {St : Statement} (hG : SampleGoodS St) (hA : AnsweredStored St)
    {kept : List KeptPlace}
    (h : ∀ k ∈ kept, ∃ xo : OnBytes.Oracle, St.oracles[k.old]? = some xo ∧ xo.shape.answers = 1) :
    ∀ k ∈ kept, (St.oracles.getD k.old default).sampleRows.size = 1 := by
  intro k hk
  obtain ⟨xo, hx, ha⟩ := h k hk
  exact one_stored hG hA hx ha

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.one_stored
#print axioms VerifiableInference.Desc.First.K2.hone_of_both
