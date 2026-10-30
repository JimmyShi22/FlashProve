-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ParseBS.lean.
Run/ParseBS.lean: from what a reader of a proof file holds to the argument string of the compiled
verifier: the tools.

The compiled verifier (Compile/Batch/Verifier.lean: verifyOneProtocol, the function that the compiler's
verifier runs on each proof string) takes a typed argument string (OneProtocolProof): a salt, the roots, the
plain parts of all rounds, and for each position that is read an opening (symbol, salt, whole path).
A proof file by the format page (FORMAT.md, which comes with the programs) holds bytes without
lengths: the random bytes, messages, nonces, and for each tree one pruned opening: columns with
their salts at the listed positions, then the digests that the walk asks for. Here are the map on
openings and the assembly. Everything is generic in the protocol.

1. What the file contains.  Definitions that can be evaluated.
    OpenB                 What a reader holds of one opening: the depth a, the list of positions,
                          the columns (words), the file's salts, the given digests in the walk's
                          order.
    incr l                Strictly increasing.
    O.ok saltBytes W      The parser's own duties at an opening (the typed verifier does not see
                          them): the list increases strictly and lies below 2^a; one column of W
                          words and one salt of saltBytes bytes for each position; exactly as many
                          given digests as the walk takes (Hash/Octopus.lean: need), 32 bytes each.
    O.paths               Whole paths from the pruned set (Octopus.fill): a place that the walk does
                          not read holds the default digest: no byte of the file lands there.
    leafSalt run s        The typed salt of a leaf: the run's value, then the file's salt, as bits;
                          so the start of a leaf's hash rides in the typed salt.
    O.atP sym run paths x The opening at the position x, with paths that the caller gives
    (Run/ParseFull.lean).
    O.at sym run x        The same with O.paths: the opening at the position x; none if x is not
                          listed or the column is no symbol (sym refuses).
    mkBPrf Q run roots plains opens
                          The argument string: salt := the run's value; no external oracle, no
                          request tree (slot 0, empty path, empty rsalt).

2. What is checked when the file compiles.  No test stands in this file. The library's
Run/ParseBS.lean has eleven tests (#guard), of the library's own functions.

3. Theorems. None. That the pruned set read off O.paths is O.given again is tested at an example
only.

4. To be declared with every use. The typed verifier tests the length of a leaf's salt alone: it
would accept any first 256 bits there; that they are the run's value is this parser's doing. A SALT
WITH A FIXED FIRST PART IS NOT UNIFORM: the library's privacy clause does not apply as it stands.

Terms: lean/GLOSSARY.md.

-/
import Run.ParseBS
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Hash.Octopus
import Run.CodingBits

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
export _root_.Run (OpenB incr leafSalt exO)

/-- The argument string. -/
def mkBPrf {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (run : ByteArray) (roots : List ByteArray)
    (plains : Plains Q.loc.shape)
    (opens : (p : OPos Q.loc.shape) → Option (Opening 256 (OSym Q.loc.shape p))) : OneProtocolProof 256 Q :=
  ⟨bytesToBits run, roots.map bytesToDig, plains, opens, fun _ => none, fun _ => false, 0, [], []⟩

/-! ## Guards: none here. (In the library's Run/ParseBS.lean: depth 4, the list 2, 9, 14: seven
given digests, level by level from the leaves.) -/

end TypedOracleCompiler.Run
