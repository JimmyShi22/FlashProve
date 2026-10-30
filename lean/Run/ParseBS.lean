-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseBS.lean: tools for the step from what a reader of a proof file holds to the argument string
of the compiled verifier.

The compiled verifier (Compile/Batch/Verifier.lean: `verifyOneProtocol`, the function that the compiler's
verifier runs on each proof string) takes a typed argument string (`OneProtocolProof`): a salt, the roots, the
plain parts of all rounds, and for each position that is read an opening (symbol, salt, whole path).
This head also calls the compiled verifier the typed verifier. A proof file by the format page
(docs/format/FORMAT.md, which comes with the programs; here in an edition that is not the one that
ships) holds bytes without lengths: the random bytes,
messages, nonces, and, each time a tree is opened, one pruned opening: columns with their salts at
the listed positions, then the digests that the walk asks for. A pruned opening opens several leaves
of one Merkle tree with only those sibling digests that the walk cannot compute itself; the walk
recomputes the root from it (Hash/Octopus.lean).

1. What the file contains.  Definitions that can be evaluated.
    `OpenB`: the depth a, the list of positions, the columns (words), the file's salts, the given
      digests in the walk's order.
    `O.ok saltBytes W`: the parser's own duties at an opening (but for a salt's length the typed
      verifier does not see them): the list increases strictly and lies below 2^a; one column of W
      words and one salt of saltBytes bytes for each position; exactly as many given digests as the
      walk takes (Hash/Octopus.lean: `need`), 32 bytes each.
    `O.paths`: whole paths from the pruned set (`Octopus.fill`): a place that the walk does not read
      holds the default digest: no byte of the file lands there.
    `leafSalt run s`: the typed salt of a leaf: the run's value, then the file's salt, as bits; so
      the start of a leaf's hash is carried in the typed salt.
    `O.atP sym run paths x`: the opening at the position x, with paths that the caller gives
      (Run/ParseFull.lean).
    `O.at sym run x`: the same with `O.paths`; none if x is not listed or the column is no symbol
      (sym refuses).
    `mkBPrf Q run roots plains opens`: the argument string: salt := the run's value; no external
      oracle, no request tree (slot 0, empty path).

2. What is checked when the file compiles.  Eleven tests (#guard).

3. Theorems. None. That the pruned set read off `O.paths` is `O.given` again is tested at an example
   only. On digests the general fact is `Octopus.reads_fill` (Hash/OctopusFacts.lean), which under
   its hypothesis on the length gives back the first `need` digests (all of them where `O.ok`
   holds).

4. To be declared with every use. The typed verifier tests the length of a leaf's salt alone: it
   would accept any first 256 bits there; that they are the run's value is this parser's doing. A
   salt with a fixed first part is not uniform: the library's privacy clause does not apply as it
   stands.

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.Verifier
import Hash.Octopus
import Run.CodingBits

namespace Run
open Iop Rom Compile Compile.Batch

/-- What a reader holds of one opening. What each field is: the head, 1. -/
structure OpenB where
  a     : Nat
  idx   : List Nat
  cols  : List (List UInt64)
  salts : List ByteArray
  given : List ByteArray

/-- strictly increasing -/
def incr : List Nat → Bool
  | [] => true
  | [_] => true
  | i :: j :: l => decide (i < j) && incr (j :: l)

/-- The parser's own duties at an opening. The head, 1, lists them. -/
def OpenB.ok (O : OpenB) (saltBytes W : Nat) : Bool :=
  incr O.idx && O.idx.all (fun x => decide (x < 2 ^ O.a)) &&
    O.cols.length == O.idx.length && O.salts.length == O.idx.length &&
  O.cols.all (fun c => c.length == W) && O.salts.all (fun s => s.size == saltBytes) &&
    O.given.length == Octopus.need O.a O.idx && O.given.all (fun d => d.size == 32)

/-- Whole paths from the pruned set. -/
def OpenB.paths (O : OpenB) : List (List (Dig 256)) :=
  Octopus.fill O.a O.idx (O.given.map bytesToDig)

/-- the typed salt of a leaf: the run's value, then the file's salt -/
def leafSalt (run s : ByteArray) : Bits := bytesToBits run ++ bytesToBits s

/-- The opening at a position, with the paths given, one for each listed position. -/
def OpenB.atP {σ : Type} (sym : List UInt64 → Option σ) (run : ByteArray) (O : OpenB)
    (paths : List (List (Dig 256))) (x : Nat) : Option (Opening 256 σ) :=
  match (O.idx.zip (O.cols.zip (O.salts.zip paths))).lookup x with
  | none => none
  | some (c, s, p) => (sym c).map fun y => ⟨y, leafSalt run s, p⟩

/-- The opening at a position, with the paths made from the pruned set. -/
def OpenB.at {σ : Type} (sym : List UInt64 → Option σ) (run : ByteArray) (O : OpenB) (x : Nat) :
    Option (Opening 256 σ) :=
  O.atP sym run O.paths x

/-- The argument string. -/
def mkBPrf {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (run : ByteArray) (roots : List ByteArray)
    (plains : Plains Q.loc.shape)
    (opens : (p : OPos Q.loc.shape) → Option (Opening 256 (OSym Q.loc.shape p))) : OneProtocolProof 256 Q :=
  ⟨bytesToBits run, roots.map bytesToDig, plains, opens, fun _ => none, fun _ => false, 0, []⟩

/-! ## Guards: seven given digests, level by level from the leaves -/

/-- an example: the given digests are told apart by their first byte -/
def exO : OpenB :=
  ⟨4, [2, 9, 14],
    [[3, 4, 7], [10, 18, 7], [15, 28, 7]],
    [_root_.Fmt.pattern 40, _root_.Fmt.pattern 40 5 1, _root_.Fmt.pattern 40 3 2],
    (List.range 7).map fun k => _root_.Fmt.pattern 32 1 k⟩

#guard Octopus.need 4 [2, 9, 14] = 7
#guard exO.ok 40 3
#guard ({ exO with idx := [2, 2, 14] } : OpenB).ok 40 3 = false
#guard ({ exO with idx := [2, 9, 16] } : OpenB).ok 40 3 = false
#guard ({ exO with given := exO.given.take 6 } : OpenB).ok 40 3 = false
#guard ({ exO with given := exO.given ++ [_root_.Fmt.zero32] } : OpenB).ok 40 3 = false
#guard exO.paths.map List.length = [4, 4, 4]
#guard (Octopus.reads 4 (exO.idx.zip exO.paths)).map digToBytes = exO.given
#guard ((exO.at some (_root_.Fmt.pattern 32) 9).map fun o => (o.sym, o.salt.length, o.path.length)) = some ([10, 18, 7], 256 + 320, 4)
#guard (exO.at some (_root_.Fmt.pattern 32) 3).isNone
#guard (exO.at (fun _ => (none : Option Unit)) (_root_.Fmt.pattern 32) 9).isNone

end Run
