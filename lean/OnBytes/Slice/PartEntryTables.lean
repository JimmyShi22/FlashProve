-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/PartEntryTables.lean: the bytes of a table's value at a string, and the string of the
call on the configuration's files.


Why. OnBytes/Slice/JoinAtSet.lean bounds a verifier that asks the oracle for digests of public
bytes, in two steps: a table T₀ of the oracle's values at a fixed set S₀ of strings, and a table T₁
at a set `S₁ T₀` that may depend on T₀. Its three parts K, E, F are families over the two tables.



That the string sc of `cOf sc T₀` lies in S₀ is asked nowhere:
where it does not, `cOf sc T₀` is a value of the table that does not reach the oracle, and `hYes`
of `join_id_at` cannot be shown of a verifier that asks at sc.



Main definitions.
 `cOf sc T₀`         the bytes of T₀'s value at sc: 32 bytes (`cOf_size`).
 `scOf files`        the string of the call on the configuration's files.

















































-/
import OnBytes.Slice.PartChainOn
import OnBytes.Slice.ChainChkAsk
import OnBytes.Slice.NamesAtPd
import OnBytes.Slice.JoinAtSet

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal

/-! ## The bytes of a table's value -/

/-- The bytes of the table's value at the string sc. -/
def cOf (sc : List Bool) (T₀ : Tab) : ByteArray := digToBytes (T₀ sc)

/-- They are 32 bytes. -/
theorem cOf_size (sc : List Bool) (T₀ : Tab) : (cOf sc T₀).size = 32 := size_digToBytes _

variable {γ γ' : Type} (sc : List Bool) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
  (pick : γ → Params.TableName × ByteArray)

/-! ## The string of the call on the configuration's files -/

section
variable {γ : Type}

/-- The string of the call on the configuration's files. -/
def scOf (files : List ByteArray) : List Bool :=
  bytesToBits (Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes files))

end

end OnBytes.Slice
