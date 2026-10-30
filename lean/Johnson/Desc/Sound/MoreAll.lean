-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MoreAll.lean: THE COMPOSED FILLING's CLOSED DOOR `mgMore`
(Johnson/Desc/Sound/MgAllAt.lean) WITH CODE. `mgMore` stands in a section in which Lean makes no
code; `moreAll` is the same term outside it. One definition, one theorem.
Limits. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (More rowMore leavesName)
open VerifiableInference.Desc.K13.Law (wSitsMore)
open VerifiableInference.Desc.First.FillSent (sentMore sent1More)
open VerifiableInference.Desc.First.FillBare (leftMore)

/-- **The closed list of extra public tests, with code.** -/
def moreAll : More :=
  (((((((({} : More).merge rowMore).merge leftMore).merge sent1More).merge sentMore).merge
    H2K5.Door.more).merge wSitsMore).strike leavesName)

/-- The same before the names that leave are struck: for a negative test. -/
def moreUnstruck : More :=
  ((((((({} : More).merge rowMore).merge leftMore).merge sent1More).merge sentMore).merge
    H2K5.Door.more).merge wSitsMore)

theorem mgMore_is : mgMore = moreAll := rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mgMore_is
