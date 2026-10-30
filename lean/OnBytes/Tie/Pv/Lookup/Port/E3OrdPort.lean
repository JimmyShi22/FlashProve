-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/E3OrdPort.lean.
The two lists of Cb/Pv/Lookup/Order/E3Ord.lean are terms of the Lean verifier under OnBytes/.

Main names:
  `lastList_eq_port`: lastList mu rK is OnBytes.Model.Forest.orderForestRange mu rK, by rfl.
  `defaultList_eq_port`: defaultList mu is OnBytes.Model.orderDefault mu, by rfl.
Limits: the lists alone are compared. At which level that verifier uses which list
(OnBytes/Model/Look.lean) is not stated here.

-/
import Cb.Pv.Lookup.Order.E3Ord
import OnBytes.Model.Forest
import OnBytes.Model.Frame

set_option autoImplicit false

namespace E3
theorem lastList_eq_port (mu rK : Nat) : lastList mu rK = OnBytes.Model.Forest.orderForestRange mu
    rK := rfl
theorem defaultList_eq_port (mu : Nat) : defaultList mu = OnBytes.Model.orderDefault mu := rfl
end E3
