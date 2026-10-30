-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/NoticesFit.lean: code switching: A TEST WITH CODE ON THE NOTICES OF A SWITCH's
SENDING: each notice but the last counts an answer and has a row. ONE DEFINITION: A LIGHT FILE, so
that the test can be evaluated without the laws that spend it (K2C/HeldAtPlan.lean). It imports
OnBytes/Iop/Ground.lean and nothing else. NO SUB-PROTOCOL IMPORTS THIS FILE.
LIMITS. THE TEST HAS BEEN EVALUATED AT NO LIST OF ROUNDS. Of the last notice (meant: the fold's
mask) it says nothing. No soundness is claimed.
-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes

/-- **The test.** sent: the notices of the switch's sending, off the list of rounds. -/
def noticesFitB (sent : Array OracleNotice) : Bool :=
  (List.range (sent.size - 1)).all fun i => (sent[i]?).any fun nt =>
    nt.shape.answers != 0 && decide (0 < nt.shape.mainRows + nt.shape.maskRows)

end VerifiableInference.Desc.First.K2
