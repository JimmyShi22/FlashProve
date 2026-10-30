-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/CloseLen.lean: the premise on the main code's message length, from the program's test on the
codes' lengths.

What is proved. `close_claimTrue` (Johnson/Desc/K10/Honest/LeftClaim.lean) and the theorems that stand on it ask that
the main code's message length is 2 ^ logEll of the group's layout (hlen). **`hlen_of_lengthsOk`**: under `CloseBase`
that follows from `Codes.lengthsOk` (OnBytes/Iop/Ground.lean) at the statement's codes, by the library's `ell_pow`
(Johnson/Goal/Meaning/LaidInside.lean): the beginning of the test leaves the codes as they are (`extends_begun`), the
layout's logEll is the group's code's, the group's code is the frame's (`CloseBase.code`), and the closing's own test on
the fold's shape finds that code in the list (`CloseBase.shape`).

Limits. `Codes.lengthsOk` is a premise: a Bool that the program computes from the public codes, and the first chain's
start asks it (`S.startOk`, Johnson/Desc/First/State.lean), at the codes that it lays into the first state; that a state
of a run still has the start's codes is not shown here. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.K10.Honest.LeftClaim
import Johnson.Goal.Meaning.LaidInside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-- **The main code's message length is 2 ^ logEll of the group's layout**, under `CloseBase` and the program's test on
the codes' lengths. -/
theorem hlen_of_lengthsOk {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D)
    (hC : s.st.codes.lengthsOk = true) :
    2 ^ (Own.layoutOf s.st D.G).logEll =
      ((D.S1 s).codes.base.getD s.frame.shape.code default).ell := by
  have hc : (D.S1 s).codes = s.st.codes := (extends_begun s.st s.frame.group D.G).codes
  obtain ⟨c, zk, h1, -, -⟩ := (Own.foldShapeFits_iff _ _).1 H.shape
  have hj : s.frame.shape.code < s.st.codes.base.size := by
    rw [hc] at h1
    exact (Array.getElem?_eq_some_iff.1 h1).1
  rw [hc]
  show 2 ^ (s.st.codes.base.getD D.G.code default).logEll = _
  rw [H.code]
  exact Meaning.ell_pow hC hj

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.hlen_of_lengthsOk
