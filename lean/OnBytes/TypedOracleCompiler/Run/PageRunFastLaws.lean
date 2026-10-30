-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageRunFastLaws.lean: the form for a run (OnBytes/TypedOracleCompiler/Run/PageRunFast.lean) is the
program of OnBytes/TypedOracleCompiler/Run/PageRun.lean at the hash function that O makes.

Statements with their proofs, at every O, every `put` and `bk`, every oracle. At the spare oracle
too the two programs agree, but there both hash the query itself, which is not the encoding's string
in general: `famRunFast_eq` is an equation with `famRun`, not with the encoding.
  `gOf_oracle`            `gOf Fmt.oracle = Run.oBits`.
  `getT_thunksOf`, `getT_one`   the bytes behind a delayed value.
  `one_eq`, `fb_eq`       an answer of one block, and of K + 1 blocks, decoded from its data.
  `famRunFast_eq`         `famRunFast Lf put bk O = famRun Lf put bk (gOf O)`.
The proof's arm under the form for a run: Johnson/TypedOracleCompiler/RecCompile/ProofAnsRun.lean
[not in this library; so here read: not proved in this library].

WHICH HASH FUNCTION IS MEANT. At O := `Fmt.oracle` the hash function is `Run.oBits`. At the bits of
a byte string whose first byte is not 4 that is `Fmt.oracle` at the string, read as 256 bits
(`Run.oBits_bytes`, Run/OracleBits.lean). A program that runs an algorithm under this form beside
hand-written checks on bytes must run both at that one function; nothing here says that any program
does.

Not claimed. All that the head of OnBytes/TypedOracleCompiler/Run/PageRunLaws.lean does not claim. Nothing on time.
Nothing on soundness.

-/
import OnBytes.TypedOracleCompiler.Run.PageRunFast

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageRun
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- At the format's oracle it is the library's one oracle on bits. -/
theorem gOf_oracle : gOf _root_.Fmt.oracle = oBits := rfl

/-- The bytes behind the j-th of n delayed values. -/
theorem getT_thunksOf (n : ℕ) (f : Fin n → ByteArray) (j : Fin n) :
    getT (thunksOf n f) j.val = f j := by
  unfold getT thunksOf
  rw [Array.getElem?_ofFn, dif_pos j.isLt]
  rfl

/-- The bytes behind the one value of an answer of one block. -/
theorem getT_one (b : ByteArray) : getT #[Thunk.pure b] 0 = b := rfl

variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) {K : ℕ}
  (put : RealPts 256 K (Lf ()) → Option (List Bool)) (bk : AllPts 256 K (Lf ()) → List Bool)
  (O : ByteArray → ByteArray)

/-- an answer of one block -/
theorem one_eq (b : ByteArray) : digS (getT #[Thunk.pure b] 0) = bytesToDig b := digS_eq b

/-- an answer of K + 1 blocks -/
theorem fb_eq (f : Fin (K + 1) → ByteArray) :
    ((fun k : Fin K => digS (getT (thunksOf (K + 1) f) k.val),
        digS (getT (thunksOf (K + 1) f) K)) : (Fin K → Dig 256) × Dig 256) =
      (fun k : Fin K => bytesToDig (f k.castSucc), bytesToDig (f (Fin.last K))) :=
  Prod.ext
    (funext fun k => (congrArg digS (getT_thunksOf (K + 1) f k.castSucc)).trans (digS_eq _))
    ((congrArg digS (getT_thunksOf (K + 1) f (Fin.last K))).trans (digS_eq _))

/-- **The form for a run is the program at the hash function that O makes.** -/
theorem famRunFast_eq : famRunFast Lf put bk O = famRun Lf put bk (gOf O) := by
  funext o q
  cases o with
  | leaf => exact one_eq _
  | node => exact one_eq _
  | rleaf => exact one_eq _
  | rnode => exact one_eq _
  | fb t => exact fb_eq fun j => O (toBytes (codeRun Lf put bk (.fb t) q j))
  | g t => exact one_eq _
  | ann => rfl
  | other => exact one_eq _
  | fbw t k => exact fb_eq fun j => O (toBytes (codeRun Lf put bk (.fbw t k) q j))

end TypedOracleCompiler.Run.PageRun

#print axioms TypedOracleCompiler.Run.PageRun.gOf_oracle
#print axioms TypedOracleCompiler.Run.PageRun.getT_thunksOf
#print axioms TypedOracleCompiler.Run.PageRun.getT_one
#print axioms TypedOracleCompiler.Run.PageRun.famRunFast_eq
