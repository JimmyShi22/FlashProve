-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsStored.lean: a stored symbol's body as a string of bits, for ALL symbols.

The sibling asks of the way of writing a symbol of an encoded index into a leaf's body (`embE`,
`prjE`) that what is written is read back, for EVERY symbol of the interface's type. The format
writes only some: a place below the table's length, a column of the table's width. So the pattern of
OnBytes/TypedOracleCompiler/Strings.lean's `embT` (the own string, or the empty string) does not do here: two
symbols outside the format's range would have one body.

This file takes three things: a partial code p of the symbols, which writes what the format writes;
a total code c of all symbols; a string e with which no string of p begins. The body of a symbol is
p's string where p writes one, and else e and then c's string: the library's `PCode.orElse`. What is
written is read back, for all symbols (`prjE_embE`); where the format writes a symbol, its body is
the format's string (`embE_fmt`); a body that p's parser reads is read as p reads it (`prjE_fmt`).

Main definitions: `embE`, `prjE`.
Main theorems: `prjE_embE`, `embE_fmt`, `embE_esc`, `prjE_fmt`.

Not claimed. No p, c or e is given HERE: OnBytes/TypedOracleCompiler/StringsStoredAt.lean takes the sibling's code
of stored symbols as p and 16 zero bits as e, shows that a body behind that escape fails the test on
bodies, and says what the code of bodies writes on it; OnBytes/TypedOracleCompiler/StringsAt.lean gives a c. Nothing
ties p to the format: "the format's string" above is a reading of p. That a p can be given with the
label's width and salt's words fixed by the setting, as a body needs it (a body does not see the
salt), is not shown. `embE` has no position: the symbol must hold its own, as the library's `SgX`
does. Nothing on whether `prjE` reads a prover's own leaf's body, or `prjT` a stored one. No wire is
made here. A body behind the escape is no string of the format; whether it passes a test on the
leaves' numbers hangs on e, and what a code of leaf queries does with it is not said. Nothing on a
join with an interface over the library's bodies: at symbols outside p's range the two write
different strings.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPart

set_option autoImplicit false

namespace TypedOracleCompiler.StringsStored
open Rom Run

variable {Sg : Type} (p : PCode Sg) (c : StrCode Sg) (e : List Bool)
  (he : ∀ a s, p.put a = some s → ¬ e <+: s)

/-- A stored symbol as a body: the format's string where the format writes the symbol; else the
escape and then the total code's string. -/
def embE (s : Sg) : List Bool := (p.orElse c e he).put s

/-- A body read as a stored symbol. -/
def prjE (b : List Bool) : Option Sg := (p.orElse c e he).parse b

/-- What is written is read back, for all symbols. -/
theorem prjE_embE (s : Sg) : prjE p c e he (embE p c e he s) = some s :=
  (p.orElse c e he).parse_put s

/-- Where the format writes a symbol, its body is the format's string. -/
theorem embE_fmt {s : Sg} {m : List Bool} (h : p.put s = some m) : embE p c e he s = m :=
  PCode.orElse_put_some p c e he h

/-- Elsewhere it is the escape and then the total code's string. -/
theorem embE_esc {s : Sg} (h : p.put s = none) : embE p c e he s = e ++ c.put s :=
  PCode.orElse_put_none p c e he h

/-- A body that the format's parser reads is read as the format's parser reads it. -/
theorem prjE_fmt {s : Sg} {m : List Bool} (h : p.parse m = some s) : prjE p c e he m = some s := by
  have h1 : embE p c e he s = m := embE_fmt p c e he (p.put_parse m s h)
  rw [← h1]
  exact prjE_embE p c e he s

end TypedOracleCompiler.StringsStored
