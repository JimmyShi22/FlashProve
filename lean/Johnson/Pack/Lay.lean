-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/Lay.lean: the symbols of a row as they are sent, over the base field or over the
extension field.

Definitions. An oracle message of the programs has rows over the base field F and rows over its
cubic extension E. An oracle message of the library (`OMsg`, Cb/Ld/LdSig.lean) has a format: the
symbols as they are sent, and how they are read as symbols over E. The three definitions of this
file are the format of one row. Johnson/Pack/Port.lean uses them.
Main names:
  `RowTy b`: F if b is true, else E.
  `upRow b`: how such a symbol is read in E.
  `row0 b`: the symbol 0.
Limits: no statement is made here.
-/
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb.Gl

/-- A row's symbols as they are sent: over the base field if b is true, else over the extension
field. -/
def RowTy : Bool → Type
  | true => F
  | false => E

/-- How such a symbol is read in the extension field. -/
noncomputable def upRow : (b : Bool) → RowTy b → E
  | true, x => algebraMap F E x
  | false, x => x

/-- The symbol 0. -/
noncomputable def row0 : (b : Bool) → RowTy b
  | true => (0 : F)
  | false => (0 : E)

end Johnson.Pack
