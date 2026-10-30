-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FineAt.lean: the key that enters the ID.


In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.









Main definition.








 `keyAt` the key that enters the ID, at the table of values T₀.





























-/
import OnBytes.Slice.PartEntryTables
import OnBytes.Slice.JoinRun
import OnBytes.Slice.OffSetGlue

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (IdKey idCode firstId)

variable {β δ Xi : Type}

/-! ## One fixed reading -/

/-- The key that enters the ID, at the table of values T₀: the fixed shape, the digest that T₀ gives
at sc, and the stored table's name that `table` reads off the prover's output. -/
def keyAt (shape₀ : Params.IndexShape) (sc : List Bool) (table : δ → Params.TableName) (T₀ : Tab)
    (d : δ) : IdKey := (shape₀, cOf sc T₀, table d)

/-! ## The join with what is fine written out -/

end OnBytes.Slice
