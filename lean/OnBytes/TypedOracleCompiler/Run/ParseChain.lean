-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ParseChain.lean.
TWO: CUT BY PROGRAM out of the library's Run/ParseChain.lean (only what the entry's clause holds and
stands on a declaration that the sibling says again), then turned by hand where it had to be. THE
HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS NOT HERE,
and what it says of "one root | one tree a round" is not true of this file. HERE STAND ONLY: toBPrf.

Run/ParseChain.lean: the parser: from the bytes of a proof file to the inputs of the compiled
verifier.

The compiled verifier is Compile.Batch.verifyOneProtocol, the function that the compiler's verifier runs on
each proof string. Fmt/Rules8.lean reads a proof file (a chain of rounds) by one fold over the plan,
asking the hash as it goes (a file holds no lengths: how many columns and digests an opening has
follows from the positions that the chain draws), and hands out what it has read (ChainOut).
Run/ParseBS.lean has the tools for openings. Here the two are joined. Everything is generic in the
protocol, in a monad and in the hash.

1. What the file contains.  Definitions that can be evaluated.
    o.rootsB              The roots of all rounds, in the order sent.
    o.opensB              All openings of all rounds, each under its tree's number.
    Typing Q              What a protocol supplies, all of it data that can be evaluated: saltBytes;
                          plains: the typed plain parts of all rounds from what was read (the nonce
                          last in a round with work); place: for each position of the protocol's
                          oracles its tree's number and its column's number; sym: a column of words
                          as the symbol at that position, or a refusal.
    toBPrf T o            (The list with the parameters' digest; the argument string), or a refusal.
    parseW h S T file     The parser: the fold, then toBPrf.
    ParseEx               A small example protocol and file of our own, not the programs' (the
                          programs: the C++ implementation that comes with this Lean code). Other
                          files use it for tests.
   The parser's own duties, which the typed verifier does not do. In the fold (Fmt/Rules4.lean,
   Rules8.lean): the parameters' digest and the run's value are computed, by two calls of the hash;
   a run's value of 32 zero bytes is refused; words that spell no element; the file's end (too
   short; a byte behind the last item). Here: at each opening O.ok (exactly the digests that the
   walk takes; one column, one salt a listed position).
   The fold tests more than a parser must: the tests of work, the walks against their roots, listed
   positions. The typed verifier tests work and walks again, on its own queries; so a file that the
   fold refuses never reaches it. For "the typed verifier refuses an altered copy" a run has to say
   which stage refused: the parser or the verifier.
   A CHAIN WITHOUT RANDOM BYTES IS REFUSED HERE: the typed first query has a salt of fixed length,
   and such a chain sends no root; how its queries would be encoded is not settled (toBPrf and
   toBPrfFull give a typed string only where there is a run's value: Run/ParseLaws.lean:
   parseLaws_some, parseLaws_someF).

2. What is checked when the file compiles.  No test stands in this file. The library's
Run/ParseChain.lean has eleven tests (#guard), of the library's own functions.

3. Theorems.  None.

4. What is not claimed. The typed statement x is the caller's: the bytes S.statement must be its
spelling.

Terms: lean/GLOSSARY.md.

-/
import Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS
import Fmt.Rules8

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
export _root_.Run (rootsB opensB Typing)

/-- From what was read to the verifier's inputs. -/
def toBPrf {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (T : Typing Q) (o : _root_.Fmt.ChainOut) :
    Option (List (Dig 256) × OneProtocolProof 256 Q) :=
  match o.run, T.plains o.rounds with
  | some run, some pl =>
      if (opensB o).all (fun x => x.2.2.ok T.saltBytes x.2.1) then
        some ([bytesToDig o.pd], mkBPrf Q run (rootsB o) pl fun p =>
          match (opensB o).lookup (T.place p).1 with
          | none => none
          | some x => x.2.at (T.sym p) run (T.place p).2)
      else none
  | _, _ => none

/-! ## Guards, on the untyped side: none here. (In the library's Run/ParseChain.lean: an example
file of this library's own, by an edition not in this repository: one tree of 16 columns, work 8,
three positions; then one element; the configuration: one public file, as the page's own toys.) -/

namespace ParseEx
open _root_.Fmt

end ParseEx

end TypedOracleCompiler.Run
