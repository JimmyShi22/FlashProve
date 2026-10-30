-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Item.lean: the statement's item "request" at an instance. One named part of
`VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
State: the true one. `theItemAt o`: the first of the request's two strings at the parameter file and
the scale file (`PV.RunArgsF.spFO`, Johnson/PV/RequestStringsWithHashAsArgumentFull.lean: the format's `Fmt.requestItem` with
o in the second hash function's place; the empty string where that gives nothing). `theItem`: at
the format's second hash function: the name of which the laws speak.
Limit. At an o with collisions two requests may share this string; the compiler's side tells them
apart by the second string, the request file's own bytes (`PV.MFull.apartI`).

-/
import Johnson.Goal.Tie.DescriptionOfData
import Johnson.PV.RequestStringsWithHashAsArgumentFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open LPFD.Full (XF)

def theItemAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : XF → ByteArray :=
  fun x => (PV.RunArgsF.spFO o Zk.pol Zk.KL x).1

def theItem (Zk : OnBytes.K.Pub) : XF → ByteArray := theItemAt OnBytes.secondHashFunction Zk

end FlashProve
