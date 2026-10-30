-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Oracle.lean: what a description says of an oracle message where it is sent: two
records, no function, no import. They stand in a file of their own so that the tests on the plan
that speak of tenants (Johnson/Desc/BookPlan.lean) can lie beneath Johnson/Desc/Block.lean, which
calls them.
Terms: lean/GLOSSARY.md.

-/

set_option autoImplicit false

namespace VerifiableInference.Desc

/-- Who shares a leaf: one tenant of an oracle message's symbol. -/
structure SymbolComponent where
  /-- its main words in a symbol -/
  main : Nat
  /-- its mask words in a symbol -/
  mask : Nat
  /-- the degree of its main rows: 1 (the base field) or 3 (the extension field) -/
  degree : Nat
  /-- whether it has an out-of-domain sample -/
  sampled : Bool
  /-- the groups that it belongs to -/
  groups : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- An oracle message, where it is sent. -/
structure Oracle where
  /-- it has 2 ^ logLength symbols -/
  logLength : Nat
  /-- the words of one symbol -/
  words : Nat
  /-- who shares a symbol, in order: their words add up to `words` -/
  tenants : List SymbolComponent
  deriving DecidableEq, Repr, Inhabited

end VerifiableInference.Desc
