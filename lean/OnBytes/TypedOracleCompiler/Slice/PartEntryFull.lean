-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/PartEntryFull.lean: from the line's limits test to what the part over the sibling
takes, for every description; and that the sibling's and the line's "string of a call with the
number 169" are one notion.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.



"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler.








HOW. For every description within the line's limits test: the sibling's `ok`, the condition on
work, `okX` (`okT_of_within`, `workT_of_within`, `okxT_of_within`). NO NEW CLOSED FACT IS EVALUATED:
the tactic `decide` stands nowhere in this file.






6 DECLARATIONS, ALL NEW.




`okLib_of_within`, `okT_of_within`, `workT_of_within`, `okxT_of_within`,
`isCall169_iff` (the sibling's and the line's "string of a call with the number 169" are one notion,
by definition), `isCall169_s0Of`.





WHAT IT IMPORTS OF THE LINE: OnBytes/Slice/PartChainOn.lean, ChainChkAsk.lean and NamesAtPd.lean.


WHAT IS NOT SAID. No part: for an entry file, a key file or a proof file.







Nothing on any hash function.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryFromLib
import OnBytes.TypedOracleCompiler.Slice.PartChainStr
import OnBytes.Slice.PartChainOn
import OnBytes.Slice.ChainChkAsk
import OnBytes.Slice.NamesAtPd
import OnBytes.Slice.WalkOff
import OnBytes.Slice.TopAny
import OnBytes.Tie.EntryPre
import OnBytes.Tie.StoredMain

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PQ (StmInv FitsS okX)
open OnBytes.Slice (RootsIn s0Of)
open OnBytes.Tie (withinX bareStatement)
open scoped ENNReal

/-! ## From the line's limits test to what the part over the sibling takes, for every description -/

section
variable (S0 : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
  (hw : withinX S0 = true)
include hw

/-- Within the line's limits test the chain passes the library's `ok`. -/
theorem okLib_of_within : _root_.Run.PQ.ok (OnBytes.Tie.xdOf S0 stm).base = true := by
  have h := OnBytes.Slice.within_ok S0 stm hw
  unfold _root_.Run.PQ.XD.ok at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- So it passes the sibling's. -/
theorem okT_of_within : TypedOracleCompiler.Run.PQ.ok (PQ.xdOf S0 stm).base = true :=
  ok_of_lib _ (okLib_of_within S0 stm hw)

/-- No round of the sibling's rounds' data asks more than 64 bits of work. -/
theorem workT_of_within : ∀ d ∈ (PQ.xdOf S0 stm).ds, d.entry.work ≤ 64 :=
  work_of_lib _ (okLib_of_within S0 stm hw) (OnBytes.Slice.within_work S0 stm hw)

/-- The sibling's limits on the stored tables' openings hold. -/
theorem okxT_of_within :
    okX (PQ.xdOf S0 stm).ds (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).xs = true := by
  have h := ok_asTypedCompilerDescription (OnBytes.Tie.xdOf S0 stm) (OnBytes.Slice.within_ok S0 stm hw)
  unfold TypedOracleCompiler.Run.PQ.XD.ok at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

end

/-- The sibling's and the line's "string of a call with the number 169" are one notion. -/
theorem isCall169_iff (s : List Bool) : IsCall169 s ↔ OnBytes.Slice.IsCall169 s := Iff.rfl

/-- The string at which the checker asks for the digest of the parameter bytes is the string of a
call with the number 169: the line's `isCall169_digestStr`. -/
theorem isCall169_s0Of (p : ByteArray) : IsCall169 (s0Of p) :=
  (isCall169_iff _).2 (OnBytes.Slice.isCall169_digestStr p)

end TypedOracleCompiler.Slice
