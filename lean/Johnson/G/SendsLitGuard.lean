-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SendsLitGuard.lean: the two written lists of Johnson/G/SendsLit.lean are what `sendsOf`
(Johnson/G/Sends.lean) computes from the public files, under the written codes.

Two tests by evaluation, one for each example; each evaluates the planner once.

Main names:
  `litOf`: a computed list of chains in the form of the written lists.
  `litOk`: the computed list is the written one, and every chain stands under the written codes of
    its file (`codesAtFull`, `codesAtSmall`, Johnson/G/SendsAll.lean).

Limits: evidence by evaluation at two examples. Those of Johnson/G/Sends.lean.
-/
import Johnson.G.SendsAll
import Johnson.G.PackList
import Johnson.G.KitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Model.Verify OnBytes.Params

/-- A computed list of chains in the form of the written lists; empty if the making refuses. -/
def litOf (K : Except String (List ChainSends)) : List SendLit :=
  (K.toOption.getD []).flatMap fun C => C.sends.map fun s =>
    ((if C.file == "key" then 0 else if C.file == "entry" then 1 else 2), C.chain, s.entry, s.sent)

/-- The test: the computed list is the written one, and every chain stands under the written codes
of its file. -/
def litOk (K : Except String (List ChainSends)) (lit : List SendLit) (cs : Nat → Codes) : Bool :=
  litOf K == lit && (K.toOption.getD []).all fun C =>
    C.codes == cs (if C.file == "key" then 0 else if C.file == "entry" then 1 else 2)

#guard litOk (sendsOf KitFull.policy.toUTF8 KitFull.layout.toUTF8 KitFull.scales) sendsFullLit
  SendsAll.codesAtFull

#guard litOk (sendsOf (TestRecordWork.policyOf TestRecordWork.smallHead)
  SmallFiles.layout SmallFiles.scales) sendsSmallLit SendsAll.codesAtSmall

end Johnson.G
