-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Stm.lean: the statement that a user of verify-on-bytes means. A definition only, in a
module of its own, so that a definition over it can be imported where the program's entry function
cannot.

-/
import OnBytes.Model.Verify

set_option autoImplicit false

namespace OnBytes.K

/-- The statement that the user means: the bytes of the three public files, of the request and of
the reply, and the options as read from the command line. -/
structure UserStm where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  request : ByteArray
  y : ByteArray
  options : Model.Verify.Options

end OnBytes.K
