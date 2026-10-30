-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OraclesH.lean: the typed oracle functions of the compiled verifier, assembled from the files
that state the format's rules: a second way to define them, and a cross-check of the first.

The compiled verifier (`verifyOneProtocol`, Compile/Batch/Verifier.lean) asks typed oracles
(Compile/Batch/Oracles.lean). To run it one needs a family of functions, one for each oracle name.
Run/CodingFn.lean has one way: each typed query, and each block of its answer, is sent to a string
of the format's single oracle, spelled there, and that oracle (Fmt/Rules23.lean) is asked at that
string (`famOf`). This file has another way, over the same data (`PageD`). `famH D K` calls the
functions in which the format's sections are stated, and never spells a string of the single
oracle.

Sources. The format page (docs/format/FORMAT.md, which comes with the programs, the C++
implementation that comes with this Lean code), rules R2.1, R3.1, R4.6, R5.2, R5.4, R7.3 and R7.7;
this file has not been held against the page as it ships, and may differ from it,
for instance at R3.1, R4.6 and R7.3.




1. What the file contains. Definitions that compute.
   Round 0: the chain's first value (R4.6; `firstValue`, Fmt/Rules4.lean). The parameters' digest
      is the one digest of the query's list; the statement is D.stm; no record; the run's value is
      the query's salt (none if it is empty). The other blocks are zeros.
   Round i > 0: block b of the row of round i (R5.2, R5.4; `block`, Fmt/Rules5.lean), at the
      chain's label, the chain value before, the message, kind, work and nonce. Which b: `blockNo`
      of Run/CodingFn.lean.
   A leaf: the hash (R2.1, R3.1, R7.3; `formatHash`, Fmt/Rules23.lean) under the number of a leaf of a run's
      tree. Its start is the first 256 bits of the typed salt. Its bytes are D.leaf's bytes, then
      the rest of the typed salt (the file's salt).
   A node: the vertex of two digests (`vertex`, Fmt/Rules7.lean), with the data's cfg as its start
      (R7.7: the digest of the public files; in the tests, that of the format page's toys, with one
      public file).
   All else: zeros (at `.ann` the one value of its type).
   How far the two ways are apart. For the chain and for a node: wholly (other files state the
   bytes). For a leaf only in part: D.leaf already holds the column's bytes with their fill, and
   both ways put the file's salt behind them. What is independent there is the test against the
   leaf of Fmt/Rules7.lean, which makes column, fill and salt itself. `blockNo` is shared.

2. What is checked when the file compiles (#guard). All tests, but for two on the data (`D1.cfg`,
`D1.stm`), are at typed queries over a small interface of three rounds (a trivial one; an oracle of
16 columns with a nonce; a list of words, three in the tests).
   (1) The format page's toy chain of six rounds, in both fields: the chain values of rounds 0 to 6
   (round 0 also without random bytes) and the test block of round 3 are the format page's known
   answers.
   (2) This library's own small test protocol (a trace of the reference program: one tree of 16
   columns, work of 8 bits, three positions): the first value, the test block, the chain values,
   the first block of the verifier's message, all 16 leaves and all 15 vertices up to the root.
   (3) The two ways agree at all these chain queries and leaves, block by block, at one of the
   vertices, and at queries that have no call. Each leaf is also the leaf of Fmt/Rules7.lean.

3. Theorems. None.

Notation:
  `K`: the number of blocks from which a verifier message is made;
  `164`: the number under which the leaves of a run's tree are hashed (`Fmt.leafNo`,
    Fmt/Rules7.lean);
  `.fb t`: the chain oracle of the protocol under the tag t (`OracleName`, Compile/Batch/Oracles.lean);
  `.fbw t k`: a ghost name, for the later tries of a proof of work (`OracleName`);
  `.rleaf`, `.rnode`: the Merkle oracles for request trees (`OracleName`);
  `.g t`: the oracle g of the joining round (`OracleName`);
  `.ann`: the oracle to which a query announces a digest (`OracleName`);
  `.other`: a spare oracle on strings (`OracleName`).

4. What is not claimed. It is not claimed that the two ways agree at every query: that is tested at
examples only. It is not claimed that a verifier's run asks these queries (the protocol and the run
are in other files). Also not claimed: anything on soundness or privacy.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingFn
import Fmt.Rules4
import Fmt.Rules5
import Fmt.Rules7

namespace Run
open Compile Compile.Batch Iop Rom

variable {I X : Type} {L : BatchProtocol I X}

/-- No answer: all bits 0. -/
def zDig : Dig 256 := fun _ => false

/-- A chain query: the K blocks of the verifier's message, and the chain value. -/
def fbH (D : PageD L) (K : Nat) (q : FbIn 256 L .test) : (Fin K → Dig 256) × Dig 256 :=
  match q.round, q.head with
  | 0, .f1 [pd] x salt =>
      (fun _ => zDig,
        bytesToDig
          (_root_.Fmt.firstValue D.label (digToBytes pd) (D.stm x) ByteArray.empty
            (if salt.isEmpty then none else some (bitsToBytes salt))))
  | i + 1, .f2 none ρ =>
      let blk := fun b : Nat =>
        bytesToDig
          (_root_.Fmt.block D.label (bitsToBytes ρ) (i + 1)
            (D.msg (i + 1) (q.rt.map digToBytes) q.plain)
            ((_root_.Fmt.Kind.ofNat? (D.kind (i + 1))).getD .nothing) (D.work (i + 1))
            (D.nonce (i + 1) q.plain) b)
      (fun k => blk (blockNo (D.work (i + 1)) K k.castSucc),
        blk (blockNo (D.work (i + 1)) K (Fin.last K)))
  | _, _ => (fun _ => zDig, zDig)

/-- A leaf query. -/
def leafH (D : PageD L) (q : LeafIn L) : Dig 256 :=
  match q.body with
  | some (.inr ⟨.test, s⟩) =>
    bytesToDig
      (_root_.Fmt.formatHash 164 (D.leaf s).1 (D.leaf s).2.1 (bitsToBytes (q.salt.take 256))
        ((D.leaf s).2.2 ++ bitsToBytes (q.salt.drop 256)))
  | _ => zDig

/-- A node query. -/
def nodeH (D : PageD L) (q : Bits × Bits) : Dig 256 :=
  bytesToDig (_root_.Fmt.vertex D.cfg (bitsToBytes q.1) (bitsToBytes q.2))

/-- The family: leaves, nodes and the chain queries of the Test by the three functions above; zeros
at every other oracle (at `.ann` the one value of its type). (`.test`, `.link`, `.onl`: `Tag`,
Compile/Oracles.lean.) -/
def famH (D : PageD L) (K : Nat) : Fam (spec 256 K L)
  | .leaf, q => leafH D q
  | .node, q => nodeH D q
  | .fb .test, q => fbH D K q
  | .fb .link, _ => (fun _ => zDig, zDig)
  | .fb .onl, _ => (fun _ => zDig, zDig)
  | .fbw _ _, _ => (fun _ => zDig, zDig)
  | .rleaf, _ => zDig
  | .rnode, _ => zDig
  | .g _, _ => zDig
  | .ann, _ => ()
  | .other, _ => zDig

/-! ## The guards' interface -/

namespace OHToy

/-- A trivial round; an oracle of 16 columns with a nonce; a list of words (three in the tests). -/
@[reducible] def r0 : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim, Plain := Unit,
    Chal := Unit, dOrc := (), dPlain := () }
@[reducible] def r1 : Round :=
  { Orc := Fin 16 → List UInt64, Pos := Fin 16, Sym := fun _ => List UInt64, rd := fun o p => o p,
    Plain := Nat, Chal := Unit, dOrc := fun _ => [], dPlain := 0 }
@[reducible] def r2 : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim, Plain := List Nat,
    Chal := Unit, dOrc := (), dPlain := [] }
abbrev shT : Shape := [r0, r1, r2]

@[reducible] def pT : InteractiveOracleProof Unit (oneExternalString 0 Unit) :=
  { shape := shT, blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
@[reducible] def pL : InteractiveOracleProof Unit (twoExternalStrings 0 Unit) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }
@[reducible] def pB : InteractiveOracleProof Unit (oneExternalString 0 Unit) :=
  { shape := [], blinded := fun _ => false, extReads := fun _ _ => ∅,
    reads := fun _ _ _ => ∅, accept := fun _ _ _ => true }

/-- The smallest ambient interface (`BatchProtocol`) whose Test has that shape. -/
@[reducible] def Lt : BatchProtocol Unit Unit where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := pT
  link := pL
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto pB
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (),
                           strat := fun _ _ _ =>
                               (((), ()), fun _ => ((fun _ => [], 0), fun _ => (((), []), fun _ => ()))),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()), strat := fun _ _ _ => (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (), strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

abbrev PBt : Type := PlainPart (shapeOf Lt .test) (annOf Lt .test)

/-- Plain parts: of the trivial round; a nonce; words. -/
def pl0 : PBt := .inl (.inr ())
def plN (n : Nat) : PBt := .inr (.inl (.inr n))
def plW (l : List Nat) : PBt := .inr (.inr (.inl (.inr l)))

def nonceOf : PBt → Nat
  | .inr (.inl (.inr n)) => n
  | _ => 0
def wordsOf : PBt → List Nat
  | .inr (.inr (.inl (.inr l))) => l
  | _ => []

def ws (l : List Nat) : ByteArray := _root_.Fmt.cat (l.map _root_.Fmt.u64n)

/-- Of a symbol with its position: the tree's place in the label (tree 0, a column of three words,
a salt of five words); 2^4 + position; the column's bytes with their fill at a salt of 40 bytes. -/
def leafT : SymAny (shapeOf Lt .test) → Nat × Nat × ByteArray
  | ⟨.inr (.inl x), (col : List UInt64)⟩ =>
    (_root_.Fmt.leafPlace 0 3 5,
      2 ^ 4 + x.val,
      _root_.Fmt.colBytes col ++ _root_.Fmt.zeroBytes (_root_.Fmt.fillLen col.length 40))
  | _ => (0, 0, ByteArray.empty)

/-- The data of the small test protocol of the head's point 2 (2). -/
def D1 : PageD Lt where
  label := 7
  kind := fun i => [0, 4, 7].getD i 0
  work := fun i => if i = 1 then 8 else 0
  stm := fun _ => _root_.Fmt.items [("toy: claim", _root_.Fmt.ext (1, 2, 3))]
  msg := fun _ rt p => rt.getD ByteArray.empty ++ ws (wordsOf p)
  nonce := fun _ p => nonceOf p
  leaf := leafT
  cfg := _root_.Fmt.Toy4.cfg

/-- The messages of the page's toy chain, but for the root of round 3. -/
def msg6 : Nat → List Nat
  | 1 => [4, 5, 6, 7, 8, 9]
  | 2 => [1, 1, 1]
  | 5 => [9, 9, 9]
  | 6 => [77]
  | _ => []

/-- The data of the page's toy chain of six rounds. -/
def D6 : PageD Lt where
  label := 7
  kind := fun i => [0, 1, 7, 4, 3, 5, 6].getD i 0
  work := fun i => if i = 3 then 8 else 0
  stm := fun _ => _root_.Fmt.Toy4.statement
  msg := fun i rt _ => rt.getD ByteArray.empty ++ ws (msg6 i)
  nonce := fun _ p => nonceOf p
  leaf := leafT
  cfg := _root_.Fmt.Toy4.cfg

def bits (s : String) : Bits := bytesToBits (_root_.Fmt.unhex s)
def hx (d : Dig 256) : String := _root_.Fmt.hex (digToBytes d)

/-- Typed queries: round 0; a later round; a leaf. -/
def qFirst (pd run : String) : FbIn 256 Lt .test :=
  ⟨0, .f1 [bytesToDig (_root_.Fmt.unhex pd)] (some ()) (bits run), none, pl0⟩
def qRound (i : Nat) (rho : String) (rt : Option ByteArray) (p : PBt) : FbIn 256 Lt .test :=
  ⟨i, .f2 none (bits rho), rt.map bytesToDig, p⟩
def qLeaf (x : Fin 16) (col : List UInt64) (run salt : String) : LeafIn Lt :=
  ⟨some (.inr ⟨.test, ⟨.inr (.inl x), col⟩⟩), bits run ++ bits salt⟩

/-- The two ways (`famH`, `famOf`) agree at a chain query, block by block. -/
def agree (D : PageD Lt) (K : Nat) (q : FbIn 256 Lt .test) : Bool :=
  hx (famH D K (.fb .test) q).2 == hx (famOf _root_.Fmt.oracle D K (.fb .test) q).2 &&
    (List.finRange K).all fun k =>
      hx ((famH D K (.fb .test) q).1 k) == hx ((famOf _root_.Fmt.oracle D K (.fb .test) q).1 k)

/-! the page's chain of six rounds, field 2 -/
#guard hx (famH D6 1 (.fb .test) (qFirst "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1" "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986")).2 == "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72"
#guard hx (famH D6 1 (.fb .test) (qFirst "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1" "")).2 == "8f1d3a0a2a3f69ec890ce893d576a15eb38d2f9f11f497eee333c9eb23247f33"
#guard hx (famH D6 2 (.fb .test) (qRound 1 "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72" none (plN 0))).2 == "3c98919bc70e2dca17b612fdf29be0f6b6f26efcdc04e845a11038260a5861fd"
#guard agree D6 3 (qRound 1 "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72" none (plN 0))
#guard hx (famH D6 2 (.fb .test) (qRound 2 "3c98919bc70e2dca17b612fdf29be0f6b6f26efcdc04e845a11038260a5861fd" none (plN 0))).2 == "ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f"
#guard agree D6 3 (qRound 2 "3c98919bc70e2dca17b612fdf29be0f6b6f26efcdc04e845a11038260a5861fd" none (plN 0))
#guard hx (famH D6 2 (.fb .test) (qRound 3 "ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f" (some (_root_.Fmt.pattern 32 11 2)) (plN 116))).2 == "28d010de3f0b0b8da2ccdd36f9c476eb062e1e416389eb81f6a4eb0c60268495"
#guard agree D6 3 (qRound 3 "ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f" (some (_root_.Fmt.pattern 32 11 2)) (plN 116))
#guard hx (famH D6 2 (.fb .test) (qRound 4 "28d010de3f0b0b8da2ccdd36f9c476eb062e1e416389eb81f6a4eb0c60268495" none (plN 0))).2 == "ad311297fb7c851c0561be363deb88aede14295352d4fcf8f478ed607c8ca10a"
#guard agree D6 3 (qRound 4 "28d010de3f0b0b8da2ccdd36f9c476eb062e1e416389eb81f6a4eb0c60268495" none (plN 0))
#guard hx (famH D6 2 (.fb .test) (qRound 5 "ad311297fb7c851c0561be363deb88aede14295352d4fcf8f478ed607c8ca10a" none (plN 0))).2 == "1377c2217a2329b555a3bc638f2d842dfd01f57cf089aca2cea169d21e70fead"
#guard agree D6 3 (qRound 5 "ad311297fb7c851c0561be363deb88aede14295352d4fcf8f478ed607c8ca10a" none (plN 0))
#guard hx (famH D6 2 (.fb .test) (qRound 6 "1377c2217a2329b555a3bc638f2d842dfd01f57cf089aca2cea169d21e70fead" none (plN 0))).2 == "70b365d8f0bda8f239fa4a9417b2ddddf69a25197785dd096c937c5d05064dad"
#guard agree D6 3 (qRound 6 "1377c2217a2329b555a3bc638f2d842dfd01f57cf089aca2cea169d21e70fead" none (plN 0))
#guard hx ((famH D6 2 (.fb .test) (qRound 3 "ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f" (some (_root_.Fmt.pattern 32 11 2)) (plN 116))).1 0) == "00a1907a594383d79b2b3036935cae89d269e199b114d175318be3d68e81c567"
#guard agree D6 1 (qFirst "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1" "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986") && agree D6 1 (qFirst "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1" "")

/-! the page's chain of six rounds, field 1 -/
#guard hx (famH D6 1 (.fb .test) (qFirst "7de82393ca9b1c414194f8ba35e40fd5b2aa2a9ad637d741cea7e93a9c257f82" "fd50818f742a65f3a1585c667ae07d35b3759f5e922910132b6d953d9feee385")).2 == "8ab45624b5f889e335e84864762f4b3d7e51eb87d278e34722ed12b0e114d90c"
#guard hx (famH D6 1 (.fb .test) (qFirst "7de82393ca9b1c414194f8ba35e40fd5b2aa2a9ad637d741cea7e93a9c257f82" "")).2 == "3d779f4e33228af38fe59cf4b550a6d778a1bcbe51b9fb5e9d3ad2800fb427cd"
#guard hx (famH D6 2 (.fb .test) (qRound 1 "8ab45624b5f889e335e84864762f4b3d7e51eb87d278e34722ed12b0e114d90c" none (plN 0))).2 == "3ac6909ee4a779664bb338ddaa16e08a478ac005417dd95b79cb513918e16e8a"
#guard agree D6 3 (qRound 1 "8ab45624b5f889e335e84864762f4b3d7e51eb87d278e34722ed12b0e114d90c" none (plN 0))
#guard hx (famH D6 2 (.fb .test) (qRound 2 "3ac6909ee4a779664bb338ddaa16e08a478ac005417dd95b79cb513918e16e8a" none (plN 0))).2 == "d8ac18d0b18175bd94b96430ff4625456ad209bf4734b94dfccc445c74c72ad2"
#guard agree D6 3 (qRound 2 "3ac6909ee4a779664bb338ddaa16e08a478ac005417dd95b79cb513918e16e8a" none (plN 0))
#guard hx (famH D6 2 (.fb .test) (qRound 3 "d8ac18d0b18175bd94b96430ff4625456ad209bf4734b94dfccc445c74c72ad2" (some (_root_.Fmt.pattern 32 11 2)) (plN 1058))).2 == "b6a4b579d528fefdef7e64a696ade4089f0fec77d43b72600198d6833228958b"
#guard agree D6 3 (qRound 3 "d8ac18d0b18175bd94b96430ff4625456ad209bf4734b94dfccc445c74c72ad2" (some (_root_.Fmt.pattern 32 11 2)) (plN 1058))
#guard hx (famH D6 2 (.fb .test) (qRound 4 "b6a4b579d528fefdef7e64a696ade4089f0fec77d43b72600198d6833228958b" none (plN 0))).2 == "586489761ec821687c8a7f60e2cb9a1fe8e3635cc6ca872fcb4375b6855e38c1"
#guard agree D6 3 (qRound 4 "b6a4b579d528fefdef7e64a696ade4089f0fec77d43b72600198d6833228958b" none (plN 0))
#guard hx (famH D6 2 (.fb .test) (qRound 5 "586489761ec821687c8a7f60e2cb9a1fe8e3635cc6ca872fcb4375b6855e38c1" none (plN 0))).2 == "6cfcaeee76d66e94659d96d96c9178dd7cb20ffaef41469d79921e37dbf1ff2c"
#guard agree D6 3 (qRound 5 "586489761ec821687c8a7f60e2cb9a1fe8e3635cc6ca872fcb4375b6855e38c1" none (plN 0))
#guard hx (famH D6 2 (.fb .test) (qRound 6 "6cfcaeee76d66e94659d96d96c9178dd7cb20ffaef41469d79921e37dbf1ff2c" none (plN 0))).2 == "1ded778ef215493b19c0050a0a9b93411930b82a5c1399b324c806fe0d901fb9"
#guard agree D6 3 (qRound 6 "6cfcaeee76d66e94659d96d96c9178dd7cb20ffaef41469d79921e37dbf1ff2c" none (plN 0))
#guard hx ((famH D6 2 (.fb .test) (qRound 3 "d8ac18d0b18175bd94b96430ff4625456ad209bf4734b94dfccc445c74c72ad2" (some (_root_.Fmt.pattern 32 11 2)) (plN 1058))).1 0) == "008d9a15b554b94ba50e4af56fc1dbe523966c7265355eb6834158d3269f2b45"
#guard agree D6 1 (qFirst "7de82393ca9b1c414194f8ba35e40fd5b2aa2a9ad637d741cea7e93a9c257f82" "fd50818f742a65f3a1585c667ae07d35b3759f5e922910132b6d953d9feee385") && agree D6 1 (qFirst "7de82393ca9b1c414194f8ba35e40fd5b2aa2a9ad637d741cea7e93a9c257f82" "")

/-! the small test protocol (the head, 2 (2)): the chain -/
#guard _root_.Fmt.hex D1.cfg == "e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f"
#guard _root_.Fmt.hex (D1.stm none) == "0a00000000000000746f793a20636c61696d1800000000000000010000000000000002000000000000000300000000000000"
#guard hx (famH D1 2 (.fb .test) (qFirst "ea7dd651ee7905f1a6a0ba17ec9e384f651766d33c0cedaa082d6019a60af476" "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f")).2 == "859319d1a3c364e3bd1ee29afbe8d1b2e704b8136655150c579449cb3fb776d3"
#guard hx ((famH D1 2 (.fb .test) (qRound 1 "859319d1a3c364e3bd1ee29afbe8d1b2e704b8136655150c579449cb3fb776d3" (some (_root_.Fmt.unhex "4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8")) (plN 57))).1 0) == "00b6174e93316772a49de96a983e4869d056e7335a5f379aef67ab67f260d953"
#guard hx (famH D1 2 (.fb .test) (qRound 1 "859319d1a3c364e3bd1ee29afbe8d1b2e704b8136655150c579449cb3fb776d3" (some (_root_.Fmt.unhex "4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8")) (plN 57))).2 == "14d4912ffda078d3c9fb4456ad62d072069a32df98740b14d03d89b521afa2df"
#guard hx ((famH D1 2 (.fb .test) (qRound 1 "859319d1a3c364e3bd1ee29afbe8d1b2e704b8136655150c579449cb3fb776d3" (some (_root_.Fmt.unhex "4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8")) (plN 57))).1 1) == "332a3ef7310dfba5ff95ec90b8a0a05588d9730aa2dc53dae1e2348ab7f93b22"
#guard hx ((famH D1 3 (.fb .test) (qRound 1 "859319d1a3c364e3bd1ee29afbe8d1b2e704b8136655150c579449cb3fb776d3" (some (_root_.Fmt.unhex "4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8")) (plN 57))).1 2) == "59de2768b2485713e5a53771cc5216d0ec6b71ad403e7337d3438cb48e3a0d48"
#guard hx (famH D1 2 (.fb .test) (qRound 2 "14d4912ffda078d3c9fb4456ad62d072069a32df98740b14d03d89b521afa2df" none (plW [30, 54, 24]))).2 == "58f979c24596f408217cea4c8b5674849bb7cf2a3c724d300cd1db95d6fac945"
#guard agree D1 2 (qFirst "ea7dd651ee7905f1a6a0ba17ec9e384f651766d33c0cedaa082d6019a60af476" "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f") && agree D1 3 (qRound 1 "859319d1a3c364e3bd1ee29afbe8d1b2e704b8136655150c579449cb3fb776d3" (some (_root_.Fmt.unhex "4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8")) (plN 57)) && agree D1 2 (qRound 2 "14d4912ffda078d3c9fb4456ad62d072069a32df98740b14d03d89b521afa2df" none (plW [30, 54, 24]))

/-! the small test protocol: all 16 leaves -/
#guard hx (famH D1 1 .leaf (qLeaf 0 [1, 0, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "01030507090b0d0f11131517191b1d1f21232527292b2d2f31333537393b3d3f41434547494b4d4f")) == "b30d3c87841192205a053419c707c8e9956ff11fa7b90758da5418aa7a64573e"
#guard hx (famH D1 1 .leaf (qLeaf 1 [2, 2, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "0104070a0d101316191c1f2225282b2e3134373a3d404346494c4f5255585b5e6164676a6d707376")) == "6691c2934e75151a1591d8c289527f2fe3ddbc6b397dfd36fcf2a26360a606d2"
#guard hx (famH D1 1 .leaf (qLeaf 2 [3, 4, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "0105090d1115191d2125292d3135393d4145494d5155595d6165696d7175797d8185898d9195999d")) == "f7d44dd626eb0c145d13e843a55d9516e1214f62273b77e95b747a4bbb76049d"
#guard hx (famH D1 1 .leaf (qLeaf 3 [4, 6, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "01060b10151a1f24292e33383d42474c51565b60656a6f74797e83888d92979ca1a6abb0b5babfc4")) == "77221b9d6c1ff9ff33c2b01d008d191ed515ae9a633f4b55c67d18414c6a5f89"
#guard hx (famH D1 1 .leaf (qLeaf 4 [5, 8, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "01070d13191f252b31373d43494f555b61676d73797f858b91979da3a9afb5bbc1c7cdd3d9dfe5eb")) == "9559f7d89e62b91a5089ebce0627df00d179381a22647103fd08312b6a05ad2e"
#guard hx (famH D1 1 .leaf (qLeaf 5 [6, 10, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff602091017")) == "7c59d4f12fc75e934471f05293b8ebf2dfd476fa9b735f48216a4d784660c2c2"
#guard hx (famH D1 1 .leaf (qLeaf 6 [7, 12, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "0109111921293139414951596169717981899199a1a9b1b9c1c9d1d9e1e9f1f9060e161e262e363e")) == "5d01635b7395190c03ba970cc724f862e8a5b627bfed90284b0cfa85b8b3c9ce"
#guard hx (famH D1 1 .leaf (qLeaf 7 [8, 14, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "010a131c252e374049525b646d767f88919aa3acb5bec7d0d9e2ebf4020b141d262f38414a535c65")) == "4cca68e9db46a70a76274d2a9bf7d86053d44c28069cec6d0d8c6a1a2eb75c50"
#guard hx (famH D1 1 .leaf (qLeaf 8 [9, 16, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "010b151f29333d47515b656f79838d97a1abb5bfc9d3dde7f1000a141e28323c46505a646e78828c")) == "de9e85d7157d7b3d360b24bf1abf1b19b495caea0024bebb994f0d5e824958b0"
#guard hx (famH D1 1 .leaf (qLeaf 9 [10, 18, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "010c17222d38434e59646f7a85909ba6b1bcc7d2dde8f3030e19242f3a45505b66717c87929da8b3")) == "6d3ed99a9bd4557d71d23ebc9bc1a604d744fe1f83fcecf04f04ffafe32dcc32"
#guard hx (famH D1 1 .leaf (qLeaf 10 [11, 20, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "010d1925313d4955616d7985919da9b5c1cdd9e5f1020e1a26323e4a56626e7a86929eaab6c2ceda")) == "2bf2474fa5e9cabd427d61cb1a24d81b9ef5602544e707b8bee73047bd6d56f9"
#guard hx (famH D1 1 .leaf (qLeaf 11 [12, 22, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "010e1b2835424f5c697683909daab7c4d1deebf80a1724313e4b5865727f8c99a6b3c0cddae7f406")) == "61275cfed3868ecd868b0bb15be3a5bbed1a1461c239764d22aaba01785188f0"
#guard hx (famH D1 1 .leaf (qLeaf 12 [13, 24, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "010f1d2b39475563717f8d9ba9b7c5d3e1ef02101e2c3a48566472808e9caab8c6d4e2f003111f2d")) == "2e276884985478a186c82ffa6b5723b061deaca35d90ad120808d55ece889e46"
#guard hx (famH D1 1 .leaf (qLeaf 13 [14, 26, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "01101f2e3d4c5b6a798897a6b5c4d3e2f10514233241505f6e7d8c9baab9c8d7e6f5091827364554")) == "992c24be7538c67cfc8f2cf909e55511e5f42d57b5da843f515615a6f40f6825"
#guard hx (famH D1 1 .leaf (qLeaf 14 [15, 28, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "01112131415161718191a1b1c1d1e1f106162636465666768696a6b6c6d6e6f60b1b2b3b4b5b6b7b")) == "f73e5ce4584f1a73b6d37e4587e580372886cf35ad4f0fe6b6565e9c998939e1"
#guard hx (famH D1 1 .leaf (qLeaf 15 [16, 30, 7] "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" "0112233445566778899aabbccddeef05162738495a6b7c8d9eafc0d1e2f3091a2b3c4d5e6f8091a2")) == "d0bcfeb5fc6842b5bbae1a59eefa9f554f8e5459ae3f8fb4910fb3924d6833d1"

/-! the small test protocol: all 15 vertices, up to the root -/
#guard hx (famH D1 1 .node (bits "b30d3c87841192205a053419c707c8e9956ff11fa7b90758da5418aa7a64573e", bits "6691c2934e75151a1591d8c289527f2fe3ddbc6b397dfd36fcf2a26360a606d2")) == "fd31e1a6d8ea52829253cc678ccb74072a14cc98ed24441817e052467eb52119"
#guard hx (famH D1 1 .node (bits "f7d44dd626eb0c145d13e843a55d9516e1214f62273b77e95b747a4bbb76049d", bits "77221b9d6c1ff9ff33c2b01d008d191ed515ae9a633f4b55c67d18414c6a5f89")) == "1f5bd93e8f2dd72c2f577b8b10f7543c27771c9c55bf42836af9fa34a27a820d"
#guard hx (famH D1 1 .node (bits "9559f7d89e62b91a5089ebce0627df00d179381a22647103fd08312b6a05ad2e", bits "7c59d4f12fc75e934471f05293b8ebf2dfd476fa9b735f48216a4d784660c2c2")) == "6ffb809bd5a2159996f4ae62d8c1af7455b59d12c3e426fc43076a11eeb3f79a"
#guard hx (famH D1 1 .node (bits "5d01635b7395190c03ba970cc724f862e8a5b627bfed90284b0cfa85b8b3c9ce", bits "4cca68e9db46a70a76274d2a9bf7d86053d44c28069cec6d0d8c6a1a2eb75c50")) == "cbf44d214c5db152061fc0dc1892d8f71dc2e8802c3d96cd8f7caa7121552ca1"
#guard hx (famH D1 1 .node (bits "de9e85d7157d7b3d360b24bf1abf1b19b495caea0024bebb994f0d5e824958b0", bits "6d3ed99a9bd4557d71d23ebc9bc1a604d744fe1f83fcecf04f04ffafe32dcc32")) == "72aaca51a0b2368af0a3357b543343ff0b28a4f83eb5fbb7b97f15e2035846de"
#guard hx (famH D1 1 .node (bits "2bf2474fa5e9cabd427d61cb1a24d81b9ef5602544e707b8bee73047bd6d56f9", bits "61275cfed3868ecd868b0bb15be3a5bbed1a1461c239764d22aaba01785188f0")) == "db718904075b6e164aa87dd3d19aa9879442de5abc70e1b32b638a170f09f9cf"
#guard hx (famH D1 1 .node (bits "2e276884985478a186c82ffa6b5723b061deaca35d90ad120808d55ece889e46", bits "992c24be7538c67cfc8f2cf909e55511e5f42d57b5da843f515615a6f40f6825")) == "36aa5c581e551d9a4048ca1bc03b8f0fe746e72a1e2838435751b76a64224696"
#guard hx (famH D1 1 .node (bits "f73e5ce4584f1a73b6d37e4587e580372886cf35ad4f0fe6b6565e9c998939e1", bits "d0bcfeb5fc6842b5bbae1a59eefa9f554f8e5459ae3f8fb4910fb3924d6833d1")) == "f8e47aa0ee09e70eb1e645778c47dc980fb658487d84b2918e575621f9fb7a65"
#guard hx (famH D1 1 .node (bits "fd31e1a6d8ea52829253cc678ccb74072a14cc98ed24441817e052467eb52119", bits "1f5bd93e8f2dd72c2f577b8b10f7543c27771c9c55bf42836af9fa34a27a820d")) == "718aabdf879449d8031242ad80ff281c5aed12c5d97e40c1cef3bb9fa5c84084"
#guard hx (famH D1 1 .node (bits "6ffb809bd5a2159996f4ae62d8c1af7455b59d12c3e426fc43076a11eeb3f79a", bits "cbf44d214c5db152061fc0dc1892d8f71dc2e8802c3d96cd8f7caa7121552ca1")) == "e0163aeb56fc5004a33f745487d1aefe9b8214c64e3293130050a9fd268475de"
#guard hx (famH D1 1 .node (bits "72aaca51a0b2368af0a3357b543343ff0b28a4f83eb5fbb7b97f15e2035846de", bits "db718904075b6e164aa87dd3d19aa9879442de5abc70e1b32b638a170f09f9cf")) == "33cf8f304cb1ebee86dae3f861ac4b36555dbc9ef30ac4939a20ade64436e894"
#guard hx (famH D1 1 .node (bits "36aa5c581e551d9a4048ca1bc03b8f0fe746e72a1e2838435751b76a64224696", bits "f8e47aa0ee09e70eb1e645778c47dc980fb658487d84b2918e575621f9fb7a65")) == "694c4895f51ead81872c87dd274c8af7453dabdd73b340707e71ce07a0ab9a75"
#guard hx (famH D1 1 .node (bits "718aabdf879449d8031242ad80ff281c5aed12c5d97e40c1cef3bb9fa5c84084", bits "e0163aeb56fc5004a33f745487d1aefe9b8214c64e3293130050a9fd268475de")) == "d464ec38a9ec1e26b2d2cce40077700c245086305feab7f58d113636266a9d4b"
#guard hx (famH D1 1 .node (bits "33cf8f304cb1ebee86dae3f861ac4b36555dbc9ef30ac4939a20ade64436e894", bits "694c4895f51ead81872c87dd274c8af7453dabdd73b340707e71ce07a0ab9a75")) == "6808d01fffb623955760d1c1808105e5b41c55038af33fd6060ddb91cc390c7c"
#guard hx (famH D1 1 .node (bits "d464ec38a9ec1e26b2d2cce40077700c245086305feab7f58d113636266a9d4b", bits "6808d01fffb623955760d1c1808105e5b41c55038af33fd6060ddb91cc390c7c")) == "4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8"

/-! the two ways agree at the 16 leaves and at one node; a leaf is the leaf of the rule file on
trees, which makes column, fill and salt itself -/
#guard [(0, [1, 0, 7], "01030507090b0d0f11131517191b1d1f21232527292b2d2f31333537393b3d3f41434547494b4d4f"), (1, [2, 2, 7], "0104070a0d101316191c1f2225282b2e3134373a3d404346494c4f5255585b5e6164676a6d707376"), (2, [3, 4, 7], "0105090d1115191d2125292d3135393d4145494d5155595d6165696d7175797d8185898d9195999d"), (3, [4, 6, 7], "01060b10151a1f24292e33383d42474c51565b60656a6f74797e83888d92979ca1a6abb0b5babfc4"), (4, [5, 8, 7], "01070d13191f252b31373d43494f555b61676d73797f858b91979da3a9afb5bbc1c7cdd3d9dfe5eb"), (5, [6, 10, 7], "01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff602091017"), (6, [7, 12, 7], "0109111921293139414951596169717981899199a1a9b1b9c1c9d1d9e1e9f1f9060e161e262e363e"), (7, [8, 14, 7], "010a131c252e374049525b646d767f88919aa3acb5bec7d0d9e2ebf4020b141d262f38414a535c65"), (8, [9, 16, 7], "010b151f29333d47515b656f79838d97a1abb5bfc9d3dde7f1000a141e28323c46505a646e78828c"), (9, [10, 18, 7], "010c17222d38434e59646f7a85909ba6b1bcc7d2dde8f3030e19242f3a45505b66717c87929da8b3"), (10, [11, 20, 7], "010d1925313d4955616d7985919da9b5c1cdd9e5f1020e1a26323e4a56626e7a86929eaab6c2ceda"), (11, [12, 22, 7], "010e1b2835424f5c697683909daab7c4d1deebf80a1724313e4b5865727f8c99a6b3c0cddae7f406"), (12, [13, 24, 7], "010f1d2b39475563717f8d9ba9b7c5d3e1ef02101e2c3a48566472808e9caab8c6d4e2f003111f2d"), (13, [14, 26, 7], "01101f2e3d4c5b6a798897a6b5c4d3e2f10514233241505f6e7d8c9baab9c8d7e6f5091827364554"), (14, [15, 28, 7], "01112131415161718191a1b1c1d1e1f106162636465666768696a6b6c6d6e6f60b1b2b3b4b5b6b7b"), (15, [16, 30, 7], "0112233445566778899aabbccddeef05162738495a6b7c8d9eafc0d1e2f3091a2b3c4d5e6f8091a2")].all fun (z : Fin 16 × List UInt64 × String) =>
  hx (famH D1 1 .leaf (qLeaf z.1 z.2.1 "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" z.2.2)) == hx (famOf _root_.Fmt.oracle D1 1 .leaf (qLeaf z.1 z.2.1 "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" z.2.2)) &&
    hx (famH D1 1 .leaf (qLeaf z.1 z.2.1 "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f" z.2.2)) == _root_.Fmt.hex (_root_.Fmt.leaf 164 0 4 z.1.val (_root_.Fmt.unhex "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f") z.2.1 (_root_.Fmt.unhex z.2.2))
#guard hx (famH D1 1 .node (bits "b30d3c87841192205a053419c707c8e9956ff11fa7b90758da5418aa7a64573e", bits "6691c2934e75151a1591d8c289527f2fe3ddbc6b397dfd36fcf2a26360a606d2")) == hx (famOf _root_.Fmt.oracle D1 1 .node (bits "b30d3c87841192205a053419c707c8e9956ff11fa7b90758da5418aa7a64573e", bits "6691c2934e75151a1591d8c289527f2fe3ddbc6b397dfd36fcf2a26360a606d2"))

/-! queries that have no call: zeros by both ways -/
#guard agree D1 2 ⟨0, .f2 none [], none, pl0⟩ && agree D1 2 ⟨1, .f1 [] none [], none, pl0⟩ && agree D1 2 ⟨0, .f1 [] none [], none, pl0⟩
#guard hx (famH D1 1 .leaf ⟨none, []⟩) == hx (famOf _root_.Fmt.oracle D1 1 .leaf ⟨none, []⟩) && hx (famH D1 1 .leaf ⟨none, []⟩) == hx zDig

end OHToy
end Run
