-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MessageAlike.lean: the kind "the code switch" (K2): WHETHER ONE
MESSAGE's ROWS ARE MADE (`messageRows`, Honest/K2/Sending.lean) HANGS ON PUBLIC DATA AND ON THE
STRETCH's COUNT ALONE. One statement with its proof. A step of the law on the closing's refusals
(Honest/K2/Law/ReturnsTop.lean): it says nothing on what a run shows.

  `messageRows_alike`   at one table, codes, shape and fold: at two stretches of one count and at
                    whatever stands in the main rows: both return; or both refuse, in the same words

Limits. Nothing on what the rows hold. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Alike
import Johnson.Desc.ProofFile.Honest.K2.Sending

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

theorem messageRows_alike (table : FreshTable) (codes : OnBytes.Codes) (s : OnBytes.OracleShape)
    (fold : Option Nat) (data data' : Nat → Nat → Cb.Gl.E) {k k' : Stretch} (h : k.due = k'.due) :
    Alike Any (messageRows table codes s fold data k)
      (messageRows table codes s fold data' k') := by
  unfold messageRows
  dsimp only
  rw [h]
  split
  · exact Alike.error _
  · simp only [pure_bind]
    split
    · exact Alike.error _
    · refine Alike.bind (fs_alike h _ _) fun _ _ _ => ?_
      refine Alike.bind (es_alike h _ _) fun _ _ _ => ?_
      refine Alike.bind (es_alike h _ _) fun _ _ _ => ?_
      refine Alike.bind (es_alike h _ _) fun _ _ _ => ?_
      exact Alike.ite (Alike.error _) trivial

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.messageRows_alike
