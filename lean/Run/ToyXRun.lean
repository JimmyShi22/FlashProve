-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyXRun.lean: the toy with an external tree, run: a file ↦ the format's reader ↦ a typed Test
string ↦ `vTS`, with BLAKE2b behind its oracles: the verifier opens a stored tree under the root cm.

Definitions that compute, with tests (#guard: evaluations made while the file compiles; they leave
no theorem). Nothing is proved. (The format page, docs/format/FORMAT.md, R7.4: a stored table's tree
has the number 0; this file has not been held against the page as it ships,
and may differ from it.)

The toy is that of Run/ToyX.lean: its protocol reads an external string (the honest side's is the
encoding of an index) at the positions of two draws.

The toy is this library's own. The three files (`honestP`, `oneP`, `tab8P`) were made outside Lean,
by a Python program on the format page's own reference program (at the edition that this file
follows), written from the data
below (plan, shape, tables, the table's item, label, random bytes), not from Fmt's functions; their
bytes were copied in by a program. They are also made in Lean (`fileOf`, by the format's functions
for the prover's side: Fmt/Rules4, 5, 6, 7): byte for byte the same (tests). Not by the programs
(the C++ implementation that comes with this Lean code).

Main names:
  `tab`: a stored table: four columns (x + 1, 2 x, 7), salts of 40 bytes; its leaves under the
    stored leaves' number, the tree's number 0, start := the configuration's digest.
  `stmX root`: the statement: one item, a stored table's (R4.6): its root as a string of bytes, then
    the list of its record's answers: none. (The name of R4.10 stands in no item.)
  `specX root`: the chain as the format's reader needs it.
  `toX o`: from what the reader holds to the typed string: salt := the run's value; no root, empty
    plain parts; π.ext p := the opening at p: symbol (p, column); salt := the configuration's
    digest, then the file's salt; a whole path from the pruned set.
  `runX root file`: the outcome (`Toy1.Who`): the reader; the verifier `VX` (`vTS` at the toy's
    interface); accepted.

The tests (#guard). Accepted on both readers (the list of the drawn positions is 0, 1: two siblings,
one given digest); and, on the lenient reader, at random bytes at which both draws meet (one
opening). Refused by the verifier behind the lenient reader: a byte of a column, of a salt, of a
given digest. The honest typed string under another root: refused by `VX`; the honest file under
another root: the draws move (the list 2, 3 for 0, 1), the cut still fits, the walk does not end in
that root: refused by `VX` behind the lenient reader, by the reader where the strict reader reads.
Symbols that carry another position (typed string altered): refused. Another start in the leaves'
typed salts: refused, and `VX`'s leaf queries then have no call. Another table, honestly committed
and opened, whose columns end in 8: every hash is right and the decision alone refuses. On the
honest typed string every query that `VX` asks has a call of the format behind every block but the
one message block of round 0. At the wiring with whole paths (no pruned openings): the string with
two siblings is refused, the string with one opening accepted.

Limits: the parser's doing, not the verifier's. The position inside a symbol is put there by `toX`
(a file holds columns alone); V (`VX`) hashes it (2^a + position under the stored leaves' number)
and its decision compares it with the position read. So are the first 256 bits of a leaf's typed
salt (the configuration's digest): V (`VX`) tests the salt's length alone; the encoding of the
queries gives a call only to that start. The run's value is computed by the reader. The root cm is
the caller's (in a scheme: the key's).
What it is not. Typed oracle functions, not a single oracle through an encoding of the queries. No
theorem. No work, no tree of the prover's own, no request tree.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ToyX
import Run.ParseToy1
import Run.DetAlong

set_option autoImplicit false

namespace Run.ToyX
open Iop Rom Compile Compile.Batch
open Run.Toy1 (Who)

def cfgX : ByteArray := _root_.Fmt.configDigest [_root_.Fmt.ascii "toy\n"]
def entX : _root_.Fmt.Entry := { name := "toyx: positions", poss := 2, logN := 2 }
def planX : _root_.Fmt.Plan :=
  { field := .two, salt := 40, nonce := 8, posB := 0, samples := 0, saved := 1, entries := [entX] }
def shX : _root_.Fmt.Shape := { a := 2, W := 3, stored := true, tree := 0 }
def paramsX : ByteArray := _root_.Fmt.paramsBytes planX cfgX []
def pdX : ByteArray := _root_.Fmt.paramsDigest paramsX

/-- A stored table: its columns and salts. -/
structure Tab where
  col  : Nat → List UInt64
  salt : Nat → ByteArray

def tab : Tab :=
  ⟨fun x => [UInt64.ofNat (x + 1), UInt64.ofNat (2 * x), 7],
    fun x => _root_.Fmt.pattern 40 (x + 2) 1⟩
/-- Another table: its columns end in 8. -/
def tab8 : Tab :=
  ⟨fun x => [UInt64.ofNat (x + 1), UInt64.ofNat (2 * x), 8],
    fun x => _root_.Fmt.pattern 40 (x + 2) 1⟩

def Tab.values (T : Tab) : List (List ByteArray) :=
  _root_.Fmt.build cfgX 2
    ((List.range 4).map fun x => _root_.Fmt.leaf 174 0 2 x cfgX (T.col x) (T.salt x))
def Tab.root (T : Tab) : ByteArray := _root_.Fmt.rootOf T.values

def stmX (root : ByteArray) : ByteArray := _root_.Fmt.tableItem "toyx: a stored table" root []

def specX (root : ByteArray) : _root_.Fmt.Spec where
  label := 9
  plan := planX
  params := paramsX
  statement := stmX root
  rand := .inFile
  cfg := cfgX
  rounds := [{ entry := entX, kind := .positions, items := [], opens := [(shX, .given root cfgX)] }]

def xd : XD := ⟨9, pdX, cfgX, 0, stmX⟩

/-- Random bytes at which the two draws are 1, 0: the list is 0, 1: two leaves that are siblings. -/
def rndX : ByteArray := _root_.Fmt.pattern 32 5 0
/-- Random bytes at which both draws are 0: one opening. -/
def rndR : ByteArray := _root_.Fmt.pattern 32 5 4

/-- The list at which the honest prover opens. -/
def listOfT (T : Tab) (rnd : ByteArray := rndX) : Option (List Nat) :=
  match _root_.Fmt.startChain 9 pdX (stmX T.root) (some rnd) with
  | none => none
  | some hd =>
    match _root_.Fmt.Chain.query ⟨9, hd.rho0, 0⟩ ByteArray.empty .positions 0 0 1 with
    | none => none
    | some (_, vb) =>
      some (_root_.Fmt.listOf
          (((_root_.Fmt.drawRound .two entX .positions (_root_.Fmt.rowOf vb)).poss).map (· % 4)))

/-- The file, made in Lean: the random bytes, then the opening at the drawn list. -/
def fileOf (T : Tab) (rnd : ByteArray := rndX) : ByteArray :=
  rnd ++ _root_.Fmt.openingBytes 2 T.col T.salt T.values ((listOfT T rnd).getD [])

/-- The files that were made outside Lean: the honest one; the one at random bytes where both draws
meet; the other table's. -/
def honestP : ByteArray := _root_.Fmt.unhex "00050a0f14191e23282d32373c41464b50555a5f64696e73787d82878c91969b01000000000000000000000000000000070000000000000001030507090b0d0f11131517191b1d1f21232527292b2d2f31333537393b3d3f41434547494b4d4f0200000000000000020000000000000007000000000000000104070a0d101316191c1f2225282b2e3134373a3d404346494c4f5255585b5e6164676a6d707376d5e893d72d5cbbfe67ecd61cc214af6bb16ce04f217132b7e5a1b59b7d836020"
def oneP : ByteArray := _root_.Fmt.unhex "04090e13181d22272c31363b40454a4f54595e63686d72777c81868b90959a9f01000000000000000000000000000000070000000000000001030507090b0d0f11131517191b1d1f21232527292b2d2f31333537393b3d3f41434547494b4d4f912c8b4b4a9e7e1214ffdef489ab719ba399555159e7f094f4e6cfc9bd147636d5e893d72d5cbbfe67ecd61cc214af6bb16ce04f217132b7e5a1b59b7d836020"
def tab8P : ByteArray := _root_.Fmt.unhex "00050a0f14191e23282d32373c41464b50555a5f64696e73787d82878c91969b0300000000000000040000000000000008000000000000000105090d1115191d2125292d3135393d4145494d5155595d6165696d7175797d8185898d9195999d04000000000000000600000000000000080000000000000001060b10151a1f24292e33383d42474c51565b60656a6f74797e83888d92979ca1a6abb0b5babfc41d11f15ca0a8944a76adcfebe914295f36bd45b212ad18ef792480ccc6a77ce0"

/-- The opening at a position of the external string. -/
def atX (O : OpenB) (p : Fin 4) : Option (Opening 256 Sg) :=
  match (O.idx.zip (O.cols.zip (O.salts.zip O.paths))).lookup p.val with
  | some ([a, b, c], s, path) => some ⟨(p, (a, b, c)), leafSalt cfgX s, path⟩
  | _ => none

/-- From what the reader holds to the typed Test string. -/
def toX (o : _root_.Fmt.ChainOut) : Option (OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto Lx.offline)) :=
  match o.run with
  | none => none
  | some run =>
    if (opensB o).all (fun x => x.2.2.ok 40 x.2.1) then
      some ⟨bytesToBits run, [], ((), (), ()), fun _ => none,
        fun p => ((opensB o).lookup 0).bind fun x => atX x.2 p, fun _ => false, 0, []⟩
    else none

def runOnX (root : ByteArray) (o : Option _root_.Fmt.ChainOut) : Who :=
  match o.bind toX with
  | none => .reader
  | some π =>
    if (VX (bytesToDig root) π).det (famX _root_.Fmt.oracle xd) then .accepted else .verifier

/-- The run, through the lenient reader (`runX`); through the format's own (`runXS`). -/
def runX (root file : ByteArray) : Who :=
  runOnX root (laxWhole (m := Id) _root_.Fmt.formatHash (specX root) file)
def runXS (root file : ByteArray) : Who :=
  runOnX root (_root_.Fmt.wholeChain (m := Id) _root_.Fmt.formatHash (specX root) file)

/-- The honest typed string. -/
def piX : Option (OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto Lx.offline)) :=
  (laxWhole (m := Id) _root_.Fmt.formatHash (specX tab.root) (fileOf tab)).bind toX

/-- Every block of a typed answer has a call, but for the message block of round 0; no other oracle.
-/
def hasCallX : (o : Compile.Batch.OracleName) → domOf 256 Lx o → Bool
  | .leaf, q => (leafX xd q).isSome
  | .node, q => (nodeCallC xd.cfg q).isSome
  | .fb .test, q => (firstX xd q 1).isSome && (q.round == 0 || (firstX xd q 0).isSome)
  | _, _ => false

/-- The symbols of all openings moved to the next position. -/
def movePos (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto Lx.offline)) : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto Lx.offline) :=
  { π with ext := fun p => (π.ext p).map fun op => ⟨(op.sym.1 + 1, op.sym.2), op.salt, op.path⟩ }

/-- The first bit of every opening's typed salt flipped: another start. -/
def moveStart (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto Lx.offline)) : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto Lx.offline) :=
  { π with
    ext := fun p =>
        (π.ext p).map fun op => ⟨op.sym, (!op.salt.headD false) :: op.salt.drop 1, op.path⟩ }

end Run.ToyX

open Run Run.ToyX Run.Toy1 in
#guard (specX tab.root).ok
-- the lists: two siblings (the walk takes one digest where two whole paths have four); at other
-- random bytes both draws meet: one opening
open Run Run.ToyX in
#guard listOfT tab == some [0, 1] && Octopus.need 2 [0, 1] = 1 && (fileOf tab).size = 32 + 2 * 64 + 32
open Run Run.ToyX in
#guard listOfT tab rndR == some [0] && (fileOf tab rndR).size = 32 + 64 + 2 * 32
-- the files made outside Lean are the files made in Lean
open Run Run.ToyX in
#guard fileOf tab == honestP && fileOf tab rndR == oneP && fileOf tab8 == tab8P
-- accepted, on both readers: the file made outside Lean
open Run Run.ToyX Run.Toy1 in
#guard runX tab.root honestP == .accepted && runXS tab.root honestP == .accepted
-- a byte of the first column, of its salt, of the last given digest: the verifier refuses behind
-- the lenient reader; the format's own reader refuses itself
open Run Run.ToyX Run.Toy1 in
#guard runX tab.root (ParseEx.flip (fileOf tab) 32) == .verifier && runXS tab.root (ParseEx.flip (fileOf tab) 32) == .reader
open Run Run.ToyX Run.Toy1 in
#guard runX tab.root (ParseEx.flip (fileOf tab) 56) == .verifier && runXS tab.root (ParseEx.flip (fileOf tab) 56) == .reader
open Run Run.ToyX Run.Toy1 in
#guard runX tab.root (ParseEx.flip (fileOf tab) ((fileOf tab).size - 1)) == .verifier && runXS tab.root (ParseEx.flip (fileOf tab) ((fileOf tab).size - 1)) == .reader
-- the honest typed string under another root
open Run Run.ToyX in
#guard (piX.map fun π => (VX (bytesToDig tab8.root) π).det (famX _root_.Fmt.oracle xd)) == some false
-- the file under another root: the draws move (the list 2, 3), the cut still fits: the lenient
-- reader reads, the verifier refuses (the walk does not end in that root); the format's own reader
-- refuses
open Run Run.ToyX Run.Toy1 in
#guard listOfT tab8 == some [2, 3] && runX tab8.root honestP == .verifier && runXS tab8.root honestP == .reader
-- symbols that carry another position
open Run Run.ToyX in
#guard (piX.map fun π => (VX (bytesToDig tab.root) (movePos π)).det (famX _root_.Fmt.oracle xd)) == some false
-- another start in the leaves' typed salts: refused; the leaf queries have no call
open Run Run.ToyX in
#guard (piX.map fun π => ((VX (bytesToDig tab.root) (moveStart π)).det (famX _root_.Fmt.oracle xd), (VX (bytesToDig tab.root) (moveStart π)).askedOK (famX _root_.Fmt.oracle xd) hasCallX)) == some (false, false)
-- another table, honestly committed and opened, whose columns end in 8: the format's own reader
-- reads it (every hash is right); the decision refuses
open Run Run.ToyX Run.Toy1 in
#guard (_root_.Fmt.wholeChain (m := Id) _root_.Fmt.formatHash (specX tab8.root) tab8P).isSome && runXS tab8.root tab8P == .verifier
-- the file's end
open Run Run.ToyX Run.Toy1 in
#guard runX tab.root ((fileOf tab).extract 0 ((fileOf tab).size - 1)) == .reader && runX tab.root (fileOf tab ++ _root_.Fmt.zeroBytes 1) == .reader
-- on the honest typed string: every query that VX asks has a call behind every block that is read
open Run Run.ToyX in
#guard (piX.map fun π => (VX (bytesToDig tab.root) π).askedOK (famX _root_.Fmt.oracle xd) hasCallX) == some true
-- a draw that comes twice: one opening: accepted
open Run Run.ToyX Run.Toy1 in
#guard runX tab.root oneP == .accepted
-- at the wire without the flag for pruned sets: the string with two siblings is refused (the parser
-- left defaults where the walk does not read); the string with one opening, whose whole path the
-- walk reads, is accepted
open Run Run.ToyX in
#guard (piX.map fun π => (VXF (bytesToDig tab.root) π).det (famX _root_.Fmt.oracle xd)) == some false
open Run Run.ToyX in
#guard (((laxWhole (m := Id) _root_.Fmt.formatHash (specX tab.root) (fileOf tab rndR)).bind toX).map fun π => (VXF (bytesToDig tab.root) π).det (famX _root_.Fmt.oracle xd)) == some true
