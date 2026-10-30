-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/GuardOn.lean: the log of an algorithm that answers its own queries at some strings by
a table.

OnBytes/Slice/Guard.lean speaks of the log of a checker's run under an oracle (`PartO.ownLog`). The
parts of the join at tables of the oracle's values (OnBytes/Slice/JoinAtSet.lean) have checkers that
answer their queries at finitely many strings by a table (`pinOn`, OnBytes/Slice/AtSet.lean). This
file says what the log of such a checker is, so that the guard can be used for such a part.

Main theorem: `det_withTrace_pinOn`: under g it is the log of the checker itself under g with the
table put over it, without the entries at the strings of the table. `withTrace_pinOn`
(OnBytes/Slice/AtSet.lean) says the same of the law over the coins; this is the form for `det`: the
run in which every coin toss yields 0.

What is not claimed. A fact on logs; no probability. Nothing on any part.

-/
import OnBytes.Slice.Guard
import OnBytes.Slice.AtSet

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open scoped ENNReal

variable {lam : ℕ} {α : Type}

/-- **The log of the algorithm that answers by the table**, under g, is the log of the algorithm
itself under g with the table put over it, without the entries at the strings of S. The form of
`withTrace_pinOn` for `det`: the run in which every coin toss yields 0. -/
theorem det_withTrace_pinOn (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (g : Fam (rom lam)) (c : OComp (rom lam) α) :
    ((pinOn S T c).withTrace.det g).2 = offSet S ((c.withTrace.det (over S T g)).2) := by
  induction c with
  | pure a => rfl
  | query o s k ih =>
    cases o
    rw [det_withTrace_query]
    by_cases hs : s ∈ S
    · rw [pinOn_query_mem T hs, ih, over_mem T g hs]
      show _ = List.filter _ (_ :: _)
      rw [List.filter_cons_of_neg (by simpa using hs)]
      rfl
    · have e : pinOn S T (OComp.query (S := rom lam) () s k) =
          OComp.query (S := rom lam) () s fun r => pinOn S T (k r) := by
        simp only [pinOn, if_neg hs]
      rw [e, det_withTrace_query, ih, over_not_mem T g hs]
      show _ = List.filter _ (_ :: _)
      rw [List.filter_cons_of_pos (by simpa using hs)]
      rfl
  | sample n k ih => exact ih _

end OnBytes.Slice

#print axioms OnBytes.Slice.det_withTrace_pinOn
