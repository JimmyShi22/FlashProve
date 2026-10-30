-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxExt.lean: the field `listed` of what is owed so that the lax verifier says yes on
an entry's typed string, from one yes of the strict reader.



OnBytes/K/Left/Lax.lean's record `LaxDebts` asks, in its field `listed`: a position that is read in
a stored table is listed in a stored opening of that table (`ListedX`,
OnBytes/TypedOracleCompiler/Slice/EntryOpened.lean), where "read" is: a member of the written link's external reads
at the verifier messages ρ that the typed chain draws. OnBytes/K/OpenedListed.lean shows `ListedX`
for every test that holds only of such members. Here it is said in that field's own letters. For
proofs only; the program does not import this file.

Main theorem.
 `listed_read` the field's statement, with `(opsOf 1 o).filter fun op => op.sh.stored` written out
    (Lax.lean's `stoOps o`, by unfolding). Asked: the strict reader, at the hash over any function
    O, has read o under a description S that lists D's stored tables and has D's rounds' data; S's
    own part is within the limits of OnBytes/TypedOracleCompiler; the chain has random bytes; all tables have the
    depth `D.a`; what ρ draws is what the reader drew.

At the use. With D := `entryXD G c` and S := the program's description with the statement at two
tables put in, "S lists D's stored tables" holds by unfolding, and "S has D's rounds' data" by
`TypedOracleCompiler.Run.PQ.rds_congr` (OnBytes/TypedOracleCompiler/Run/AllRoots.lean): neither is shown here.

What is not claimed. The hypotheses at any description or file. That what ρ draws is what the reader
drew: that stands beside the record's field `chain`. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.OpenedListed

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf)
open _root_.Run.PQ (View)

/-- The field `listed`, from one yes of the strict reader. -/
theorem listed_read {X : Type} (D : XD) (dec : X → View → Bool) (S : _root_.Fmt.SpecX)
    (O : ByteArray → ByteArray) (hsto : S.stored = D.stored)
    (hds : PQ.rds (PQ.inFile S.base) = D.ds) (hokb : PQ.ok (PQ.inFile S.base) = true)
    (hn : S.base.rand.isNone = false) (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j)) (x : X)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds)))
    (hd : PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn)) :
    ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
      (haveI := (wqXE D dec).ext.dec
       decide (p ∈ (PSXE D dec).up.loc.extReads x ρ)) :=
  listedX_read D dec S O hsto hds hokb hn hD seen b i o j e x ρ hd _ fun _ hp =>
    of_decide_eq_true hp

end OnBytes.K.Left
