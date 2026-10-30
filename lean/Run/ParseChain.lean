-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseChain.lean: the parser, from the bytes of a proof file to the inputs of the compiled
verifier.

The compiled verifier is `Compile.Batch.verifyOneProtocol`, the function that the compiler's verifier runs on
each proof string. It takes typed data, not bytes, so this head also calls it the typed verifier.
The parser makes two of its inputs: the list with the parameters' digest, and the argument string
(`OneProtocolProof`, Compile/Batch/Verifier.lean), which has among its fields a salt, the Merkle roots, the
plain parts of the prover's messages and the openings. Fmt/Rules8.lean (`Fmt.wholeChain`) reads a
proof file, which holds a chain of rounds, by one fold over the rounds, and queries the hash as it
goes. A file holds no lengths: how many columns and digests an opening has follows from the
positions that the chain draws. That reader returns what it has read (`Fmt.ChainOut`).
Run/ParseBS.lean has the tools for openings. Here the two are joined. The parser is generic in the
protocol, in a monad and in the hash.

1. What the file contains.  Definitions that can be evaluated.
    `Typing Q`: what a protocol supplies: saltBytes; plains: the typed plain parts of all rounds
      from what was read (the nonce last in a round with proof of work); place: for each position of
      the protocol's oracles its tree's number and its column's number; sym: a column of words as
      the symbol at that position, or a refusal.
    `parseW h S T file`: the parser.
    `ParseEx`: A small example protocol and file of this library's own, not the programs' (the
      programs: the C++ implementation that comes with this Lean code). Other files use it for
      tests.
   The parser's own duties, which the typed verifier does not do. In the fold (Fmt/Rules4.lean,
   Fmt/Rules8.lean): the parameters' digest and the run's value are computed, by two calls of the
   hash; a run's value of 32 zero bytes is refused; so are words that spell no element, a file that
   is too short, and a file with a byte after the last item. Here: at each opening `OpenB.ok`
   (Run/ParseBS.lean) tests, among other things, that there are exactly as many digests as the walk
   takes, and one column and one salt for each listed position. The run's value is a hash, under the
   chain's label, of the parameters' digest and the chain's 32 random bytes (`Fmt.runValueW`,
   Fmt/Rules4.lean). The walk recomputes a Merkle root from the opened leaves and the given digests
   (Hash/Octopus.lean).
   The fold tests more than a parser must: the proofs of work, the walks against their roots, the
   listed positions. The typed verifier walks again, on its own queries (proof of work is tested
   where the protocol's `accept` tests it: `Q.loc.accept`); so a file that the fold refuses never
   reaches the typed verifier. For "the typed verifier refuses an altered copy" a run has to say
   which stage refused: the parser or the verifier.
   A chain without random bytes is refused here: the typed first query has a salt of fixed length,
   and such a chain sends no root; how its queries would be encoded is not settled
   (Run/CodingFn.lean and Run/CodingPage160.lean spell its first query). `toBPrf` and `toBPrfFull`
   (Run/ParseFull.lean) give a typed string only where there is a run's value (Run/ParseLaws.lean:
   `parseLaws_some`, `parseLaws_someF`).

2. What is checked when the file compiles.  Eleven tests (#guard).

3. Theorems.  None.

4. What is not claimed. The typed statement x is the caller's: the bytes `S.statement` must be its
   spelling.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ParseBS
import Fmt.Rules8

namespace Run
open Iop Rom Compile Compile.Batch

/-- the roots of all rounds, in the order sent -/
def rootsB (o : _root_.Fmt.ChainOut) : List ByteArray :=
  o.rounds.toList.flatMap fun r => _root_.Fmt.rootsOf r.vals

/-- all openings of all rounds, each under its tree's number -/
def opensB (o : _root_.Fmt.ChainOut) : List (Nat × Nat × OpenB) :=
  o.rounds.toList.flatMap fun r =>
    r.opens.map fun x => (x.1.tree, x.1.W, ⟨x.1.a, x.2.1, x.2.2.cols, x.2.2.salts, x.2.2.given⟩)

/-- What a protocol supplies to the parser. What each field is: the head, 1. -/
structure Typing {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) where
  saltBytes : Nat
  plains    : Array _root_.Fmt.RoundOut → Option (Plains Q.loc.shape)
  place     : OPos Q.loc.shape → Nat × Nat
  sym       : (p : OPos Q.loc.shape) → List UInt64 → Option (OSym Q.loc.shape p)

/-- From what was read to two of the verifier's inputs, or a refusal (`none`). -/
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

/-- The parser: the reader `Fmt.wholeChain`, then `toBPrf`. -/
def parseW {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} (S : _root_.Fmt.Spec) (T : Typing Q) (file : ByteArray) :
    m (Option (List (Dig 256) × OneProtocolProof 256 Q)) := do
  let o ← _root_.Fmt.wholeChain h S file
  pure (o.bind (toBPrf T))

/-! ## Guards, on the untyped side

An example file of this library's own, by an edition of the page that is not
the one that ships. The configuration: one public file, as the page's own toys.
-/

namespace ParseEx
open _root_.Fmt

def plan : Plan where
  field := .two
  salt := 40
  nonce := 8
  posB := 0
  samples := 0
  saved := 1
  entries := [{ name := "toy: positions", work := 8, msg := 32, roots := 1, poss := 3, logN := 4 },
    { name := "toy: nothing", msg := 24 }]

def spec (c : UInt64 × UInt64 × UInt64) : Spec where
  label := 7
  plan := plan
  params := paramsBytes plan Toy4.cfg []
  statement := items [("toy: claim", ext c)]
  rand := .inFile
  cfg := Toy4.cfg
  rounds := [
    { entry := { name := "toy: positions", work := 8, msg := 32, roots := 1, poss := 3, logN := 4 },
      kind := .positions, items := [.root], opens := [({ a := 4, W := 3, tree := 0 }, .own 0)] },
    { entry := { name := "toy: nothing", msg := 24 }, kind := .nothing, items := [.e] } ]

def file : ByteArray := unhex "01060b10151a1f24292e33383d42474c51565b60656a6f74797e83888d92979c4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8390000000000000004000000000000000600000000000000070000000000000001060b10151a1f24292e33383d42474c51565b60656a6f74797e83888d92979ca1a6abb0b5babfc4090000000000000010000000000000000700000000000000010b151f29333d47515b656f79838d97a1abb5bfc9d3dde7f1000a141e28323c46505a646e78828c10000000000000001e0000000000000007000000000000000112233445566778899aabbccddeef05162738495a6b7c8d9eafc0d1e2f3091a2b3c4d5e6f8091a2f7d44dd626eb0c145d13e843a55d9516e1214f62273b77e95b747a4bbb76049d6d3ed99a9bd4557d71d23ebc9bc1a604d744fe1f83fcecf04f04ffafe32dcc32f73e5ce4584f1a73b6d37e4587e580372886cf35ad4f0fe6b6565e9c998939e1fd31e1a6d8ea52829253cc678ccb74072a14cc98ed24441817e052467eb52119db718904075b6e164aa87dd3d19aa9879442de5abc70e1b32b638a170f09f9cf36aa5c581e551d9a4048ca1bc03b8f0fe746e72a1e2838435751b76a64224696e0163aeb56fc5004a33f745487d1aefe9b8214c64e3293130050a9fd268475de1e0000000000000036000000000000001800000000000000"

def out : Option ChainOut := wholeChain (m := Id) formatHash (spec (1, 2, 3)) file

end ParseEx

#guard (ParseEx.spec (1, 2, 3)).ok
#guard ParseEx.file.size = 512
#guard ParseEx.out.isSome
#guard (ParseEx.out.map fun o => _root_.Fmt.hex o.pd) = some "ea7dd651ee7905f1a6a0ba17ec9e384f651766d33c0cedaa082d6019a60af476"
#guard (ParseEx.out.map fun o => o.run.map _root_.Fmt.hex) = some (some "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f")
#guard (ParseEx.out.map fun o => (rootsB o).map _root_.Fmt.hex) = some ["4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8"]
#guard (ParseEx.out.map fun o => (opensB o).map fun x => (x.1, x.2.1, x.2.2.a, x.2.2.idx, x.2.2.cols, x.2.2.given.length, x.2.2.ok 40 3)) == some [(0, 3, 4, [3, 8, 15], [[4, 6, 7], [9, 16, 7], [16, 30, 7]], 7, true)]
#guard (ParseEx.out.map fun o => o.rounds.toList.map fun r => r.nonce) = some [57, 0]
#guard (_root_.Fmt.wholeChain (m := Id) _root_.Fmt.formatHash (ParseEx.spec (1, 2, 4)) ParseEx.file).isNone
#guard (_root_.Fmt.wholeChain (m := Id) _root_.Fmt.formatHash (ParseEx.spec (1, 2, 3)) (ParseEx.file.extract 0 511)).isNone
#guard (_root_.Fmt.wholeChain (m := Id) _root_.Fmt.formatHash (ParseEx.spec (1, 2, 3)) (ParseEx.file ++ _root_.Fmt.zeroBytes 1)).isNone

end Run
