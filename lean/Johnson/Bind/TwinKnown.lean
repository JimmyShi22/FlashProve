-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinKnown.lean: tests of the committer that runs
(Johnson/Bind/Twin.lean) at small shapes. Tests alone: each is a #guard, which Lean's
evaluator runs when the file is compiled; a #guard leaves no theorem.

1. The format's known answers (docs/format/format-vectors.txt, which comes with the programs, the
   C++ implementation that comes with this Lean code), each taken through this committer's own
   definitions where one covers it: point and symbol at all sixteen positions of the code (4, 8, 3);
   three points; a leaf of a stored tree; a vertex; the digest of one public file; a table's name;
   an OOD seed's point and factor; three commitment IDs. That file has no known answer for a leaf of
   a stored tree with zero bytes before the salt, for a whole tree's root, or for an OOD answer.
2. Whole commitments at five small shapes of this library's own making, and at the first of them with
   salts that are too short. The expected values are the answers of a short Python program, written
   from the same description of the programs as the Lean text, by other formulas where there is a
   choice (the point as a power of one root at the reversed bits; the symbol as the plain sum of
   powers; eq by the bits of the place; the tree by recursion from the root), with Python's own
   BLAKE2b. The second shape has zero bytes before the salt and two seeds. The fourth has one row
   (v = 0), the fifth no plain entry (3 s = l). These values are not the programs'. All tables, salts and public files here are synthetic: given by formulas
   written in this file. No model's weights enter, neither real ones nor weights from a generator,
   and no run of the programs. The Python program is not in the repository.
3. Negative tests, each of which must part from the honest value: one entry, one tail entry, one
   pad, one byte of one salt changed; two rows swapped; each of the six words of the shape changed;
   one public file changed. The first shape's expected values, taken together, are also rejected at
   each of the five changed tables; no other expected value has such a test.
4. Agreements inside the library: the tree's root is that of `Fmt.build`; over the one oracle
   `Fmt.oracle` the committer gives what it gives at `Fmt.formatHash`; a word that is not below p counts
   modulo p; a salt that is too long is cut.

Limits.
(1) Here the OOD answers are held against the Python program alone, which has the same source as the
    Lean text: a misreading of that source would show in neither. Johnson/Bind/TwinPort.lean holds
    them against the text of this library's verifier on bytes.
(2) No value here was computed by the programs. The known answers under 1 are what the format's
    Python script (docs/format/format_rules.py) prints; by the format page two tests of the programs
    form a part of these lines with the programs' own routines.

-/
import Johnson.Bind.Twin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin
namespace Known

open Fmt (Ext hex unhex)

/-- The prime of the field. -/
def p : Nat := Fmt.Fld.two.p

/-- A list of elements of the extension field as hexadecimal digits: 24 bytes each. -/
def spell (l : List Ext) : String := hex (Fmt.cat (l.map Fmt.ext))

/-- The small shapes' table. The salts have 64 bytes here: a shape with a shorter salt cuts them. -/
def toy : Table where
  entry b q := UInt64.ofNat ((1000003 * (64 * b + q) + 17) % p)
  tail b j := UInt64.ofNat (p - 1 - 5 * (64 * b + j))
  pad b j := UInt64.ofNat ((7777777 * (64 * b + j) + 3) % p)
  salt x := ⟨(Array.range 64).map fun k => UInt8.ofNat ((31 * x + 7 * k + 9) % 256)⟩

/-- Three short public files. -/
def files : List ByteArray := [Fmt.ascii "toy\n", Fmt.ascii "lay\n", ⟨#[0, 1, 2, 3, 4, 5, 6, 7]⟩]

def shapeA : Shape := ⟨4, 8, 3, 1, 1, 40⟩
def shapeB : Shape := ⟨5, 16, 5, 3, 2, 64⟩
def shapeC : Shape := ⟨6, 32, 7, 2, 1, 48⟩

/-- The commitment at S, `files` and T has these five values. -/
def meets (S : Shape) (T : Table) (root name seeds answers id : String) : Bool :=
  let o := commit S files T
  hex o.root == root && hex o.name == name && spell (Fmt.flatSeeds o.seeds) == seeds &&
    spell o.answers == answers && hex o.id == id

/-! ### 1. The format's known answers -/

/-- The code (4, 8, 3) as a table of one row without pads. -/
def shape483 : Shape := ⟨4, 8, 3, 0, 0, 40⟩
def table483 : Table where
  entry _ j := UInt64.ofNat (1000003 * j + 17)
  tail _ j := UInt64.ofNat (p - 1 - 5 * j)
  pad _ _ := 0
  salt _ := ByteArray.empty

#guard (List.range 16).map (fun x => Fmt.M1.point 4 x) ==
  [7,
    18446744069414584314,
    1970324836974592,
    18444773744577609729,
    117440512,
    18446744069297143809,
    7696581392640,
    18446736372833191681,
    28672,
    18446744069414555649,
    8070450532247928832,
    10376293537166655489,
    481036337152,
    18446743588378247169,
    31525197384253440,
    18415218872030330881]
#guard (List.range 16).map (columnOf shape483 (laid shape483 table483)) ==
  [[2251967882290790],
    [1761066152988106],
    [7062088817545533301],
    [11380757524195858728],
    [2725397505791400752],
    [9956560198768277230],
    [13552087439267912244],
    [10659558282155280860],
    [6537321372891063553],
    [18188557764674685878],
    [2233206876800962260],
    [16226444926008292991],
    [17139878364151154727],
    [12909924323945411286],
    [15510620354141475440],
    [3487535770944086406]]
#guard Fmt.M1.w32 == 16334397945464290598
#guard [Fmt.M1.point 15 12345, Fmt.M1.point 15 2, Fmt.M1.point 14 9999] ==
  [4649013750641269600, 1970324836974592, 9335015899764920215]

-- a leaf of a stored tree: a = 3, position 6, the column 1, 2, 3
#guard hex (leafAtW (m := Id) Fmt.formatHash ⟨3, 0, 0, 0, 0, 40⟩
    (unhex "01060b10151a1f24292e33383d42474c51565b60656a6f74797e83888d92979c") [1, 2, 3]
    (unhex "090c0f1215181b1e2124272a2d303336393c3f4245484b4e5154575a5d606366696c6f7275787b7e") 6) ==
  "32e9d1c553ae00721507db816c3885fda15a00ab4b538a8fd70185bbcde6ada1"
-- a vertex: the climb from two values of depth 1
#guard hex (climbW (m := Id) Fmt.formatHash
    (unhex "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc") 1
    #[unhex "030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc",
      unhex "e3eaf1f8040b121920272e353c434a51585f666d747b828990979ea5acb3bac1"]) ==
  "af2a19aa20cc89e1e740e2ec4d34a275eae7bff385fcfc64e3064ccd7cc1b3f8"

/-- The known answers' digest of one public file, "toy" and a line feed. -/
def cfgK : ByteArray := unhex "e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f"
def rootK : ByteArray := unhex "04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9c"
def shapeK : Shape := ⟨10, 512, 40, 9, 1, 40⟩

-- the digest of the public files, read off the name that the committer makes
#guard hex ((commit shape483 [Fmt.ascii "toy\n"] table483).name.extract 32 64) == hex cfgK
#guard hex (nameOf shapeK rootK cfgK) == String.join [
  "04111e2b3845525f6c798693a0adbac7d4e1ee000d1a2734414e5b6875828f9c",
  "e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f",
  "0a00000000000000000200000000000028000000000000000900000000000000",
  "01000000000000002800000000000000"]
-- an OOD seed: l = 3, so the point has two coordinates
#guard Id.run (seedsW (m := Id) Fmt.formatHash { shapeK with l := 3 }
    (nameOf { shapeK with l := 3 } rootK cfgK)) ==
  [([(9697749137137958355, 613613959841214928, 8403959380172774020),
     (15526148976690303146, 2032215208828410348, 4053187377642565227)],
    (14917727018641805655, 3966560771581124203, 17230899846445233913))]
-- three IDs: no seed and no answer; a given seed; the name's own seed, sampled
#guard hex (Fmt.publishedID cfgK (nameOf shapeK rootK cfgK) [] [] []) ==
  "80d59c8b07aaa71829c9765057082a108618402daf661caf2c390c09dfafddd3"
#guard hex (Fmt.publishedID cfgK (nameOf shapeK rootK cfgK) [(7, 8, 9), (10, 11, 12), (13, 14, 15)]
    [(1, 2, 3), (4, 5, 6)] []) ==
  "4fb918a30faa7643cf8e6bc431c6643d7b5b4cc298dd0531cc0206bb4f756a0b"
#guard hex (close shapeK cfgK rootK fun _ => [(1, 2, 3), (4, 5, 6)]).id ==
  "e18438e0725ec651fc8bffa3b3f860ddeca70e6cb1991dd43620b98ef6f05bd2"
-- the shape's numbers
#guard shapeK.cube == 9 && ({ shapeK with l := 3 } : Shape).cube == 2 && shapeA.cube == 3 &&
  ({ shapeK with l := 1 } : Shape).cube == 0 && ({ shapeK with l := 524288 } : Shape).cube == 19 &&
  ({ shapeK with l := 524289 } : Shape).cube == 20 && shapeB.plain == 10 && shapeB.rows == 8

/-! ### 2. Whole commitments at small shapes: three here, three under "Shapes at the edge" -/

#guard meets shapeA toy
  "1676a4fe09084b68784e62894dfe79edc6270b9569a0898cb6c48e09340dce60"
  (String.join [
    "1676a4fe09084b68784e62894dfe79edc6270b9569a0898cb6c48e09340dce60a1192c22ed2f44a87c2b3966",
    "c52f8c7984f11017965a951e85df3cf60cf6b864040000000000000008000000000000000300000000000000",
    "010000000000000001000000000000002800000000000000"])
  (String.join [
    "ed9cd53a35d66a55292c99c333f656e310fd08453b616e39f2412c07057e892016332b3f0e7a13b03f7d28f2",
    "1d21abdd5757006e7eb4f6f874b395b9bc3903da201711604d857318c1a2eea0589e34d180d8edde99e1bdd2",
    "7a57b1a71e4e99bc"])
  (String.join [
    "fed9314907f6689a246e3ee5ee455ef6b667c6f17772f054eea7ee924e247964192b05fdddb07260bac123d3",
    "5c70b688"])
  "b8d7312c1b374bcc0e6dfdda3391a8e998b63da37555f7da57975f452642fc59"
#guard meets shapeB toy
  "f4baaca13d6352cbe908db1c06d09f031d61c2f5254a1823d3d76d426ce6214f"
  (String.join [
    "f4baaca13d6352cbe908db1c06d09f031d61c2f5254a1823d3d76d426ce6214fa1192c22ed2f44a87c2b3966",
    "c52f8c7984f11017965a951e85df3cf60cf6b864050000000000000010000000000000000500000000000000",
    "030000000000000002000000000000004000000000000000"])
  (String.join [
    "64ecdd88c447d85b99f0bcab58c9c8a4f17461325e69d0c0686f903e9a2328f614dcd5a60ec0f7783873ed9a",
    "d883627160ed1a179c32e5450ceff18c5dd657fba162c281629cfff5de105eab56b3212d095728a3a4c52706",
    "ed69143231b2bb5c6d81ae54b3fe1274c61389e2ab559bd05c441817f06699e175d611ea3ade1d0f257cccfc",
    "b7eda2f39612b0bf38bc23cb07aa669c8418086692f2ca6284e9d9b620c20815e83acca6da93563525ccad1f",
    "6ff59fe812a7b2d103c3345ae414bdea4774bcc4340ffa1c9393f6cd8f85bdea26779bfc57890ad3d37115e1",
    "1624af8374badac10d2a5aabc436ae6e89b3103e"])
  (String.join [
    "57208900c1c6cd45f2ff066c30ec960320a6ce33782c7660f5ab9bd60e434eaea537c3e74885acc8d0d39ef9",
    "012ed0e7bd59e88809452d478d3f0481c3d04281769ad7cdfa7fca78af8fca50f0cf01c3b37cb645fa36b95e",
    "d5cc33b75f17f2592393471152c38c48287f019656b5eefecc8ee0677dd31e916973f9cad15cb5d7c2c1a9a3",
    "aae8c5f4dbc5c874bc0014cc89cca6999a41ec49c2befeaaea999a7c2283e901002773a923572845b3e968ec",
    "d0069d015c9ad28ae0be5d321aea353eef050622e3bf4b4b5dfefbbf7d7e46fa7877f29b827ac7c1dc3a57bf",
    "95761c01de4b905f0d4cdf20e6b7f2ef76d357b0553f65aa2b3eab4cf73df9d41163f277ce6bfb3505ce1bda",
    "961e86397703d015ed9083bdbdfdebb6ebb087add4bc7922bb78c43274bc0a4e927df6e9a4479ef5246004d0",
    "872170f25002b5b35890832afbd5761b6faff84cf1a91c6b31a69b9421b223bbbc3a6a4f2cbdf3fe382c4a73",
    "79540d6a0b75c40a0ae6e32d3a1d373f0a1b6a791f6105e3f6a2b1288f8fbd06"])
  "9430d67015a91736ac901bb2f7e7309355bdd415592ef88224861bc9027b2db7"
#guard meets shapeC toy
  "0727bcfe0125f95102274f52690d9899818a4040b12499677b77fb38b44f2d91"
  (String.join [
    "0727bcfe0125f95102274f52690d9899818a4040b12499677b77fb38b44f2d91a1192c22ed2f44a87c2b3966",
    "c52f8c7984f11017965a951e85df3cf60cf6b864060000000000000020000000000000000700000000000000",
    "020000000000000001000000000000003000000000000000"])
  (String.join [
    "4d35cf751326422c60d44c6d8f7177199ae914b7a94503d65799e073e8503a0b880c5cd1e9905733eaafc7cd",
    "3fb7d612272ccafe515e45f43a6567fa7bf21ef6138dfd7b20d36dcedf2d2778ed915b7d58f07eae5b9a6b56",
    "0afd79c5664fce394e802a64fc3777618930233cf535253506acbaf82577f71c0832c72e884a2b7d4132e114",
    "8cf936fa0db3920fc0bab1e4"])
  (String.join [
    "1282a290490f3f9db4507ae9a602db732238cea5e972c006210e66b9bc745943f54d4231398f6bb629587c07",
    "630df022319a29e22eda73e9364b0a79cb1bfcf830782a69dca71f3f4026ed0aa23f8e8f7648d2c05ea88c3b",
    "3798d8ca55424f5b"])
  "dad45cfab3cf29f2c1942a661efb6d4237e0eafae6f40e79564b096611583268"
-- the second shape's leaves have zero bytes before the salt; the others' have none
#guard Fmt.fillLen shapeB.rows shapeB.sigma == 48 && Fmt.fillLen shapeA.rows shapeA.sigma == 0 &&
  Fmt.fillLen shapeC.rows shapeC.sigma == 0

/-! ### 3. Negative tests -/

/-- f with its value at (b, q) raised by 1. -/
def bent (f : Nat → Nat → UInt64) (b q : Nat) : Nat → Nat → UInt64 :=
  fun b' q' => if b' == b && q' == q then f b' q' + 1 else f b' q'

/-- The rows 0 and 1 swapped. -/
def swap (f : Nat → Nat → UInt64) : Nat → Nat → UInt64 :=
  fun b q => f (if b == 0 then 1 else if b == 1 then 0 else b) q

def bentEntry : Table := { toy with entry := bent toy.entry 1 2 }
def bentTail : Table := { toy with tail := bent toy.tail 0 1 }
def bentPad : Table := { toy with pad := bent toy.pad 1 2 }
def bentSalt : Table :=
  { toy with salt := fun x => if x == 5 then (toy.salt x).set! 39 0 else toy.salt x }
def swapped : Table :=
  { toy with entry := swap toy.entry, tail := swap toy.tail, pad := swap toy.pad }

/-- Which of root, answers and ID part between two commitments. -/
def parts (o o' : Out) : Bool × Bool × Bool :=
  (hex o.root != hex o'.root, spell o.answers != spell o'.answers, hex o.id != hex o'.id)

def honestA : Out := commit shapeA files toy

/-! ### Shapes at the edge -/

/-- One row: v = 0. -/
def shapeE : Shape := ⟨4, 8, 3, 0, 1, 40⟩
/-- No plain entry: 3 s = l. The format's verifiers reject such a shape; the functions are total. -/
def shapeF : Shape := ⟨4, 3, 2, 1, 1, 40⟩

#guard meets shapeE toy
  "68fa802d149230bf96e72e14632482645f77e4a7910ae57f5a0346e6566d3ab1"
  (String.join [
    "68fa802d149230bf96e72e14632482645f77e4a7910ae57f5a0346e6566d3ab1a1192c22ed2f44a87c2b3966",
    "c52f8c7984f11017965a951e85df3cf60cf6b864040000000000000008000000000000000300000000000000",
    "000000000000000001000000000000002800000000000000"])
  (String.join [
    "ea1015025974c6d127a76308fd6423bdcb5a363848d2aeca1bd90a7c6164cc753f3a48096febe1fd284cb564",
    "b9bcb6876bc50b7e7e401c7b8a3653aeb8c9c5f9ca27ca3ef8743112858cca98e58cb207f281479c94a2604a",
    "c5b848018e220a03"])
  "3b8a0aebfdf15e1df66c0028fd9d099c3536692a3bc8c205"
  "371cf593c35dbd847ab03acd1e600ea7f55f4d5ba11251485897f519371add3b"
#guard meets shapeF toy
  "c3b4b7300a8d75a06a0074769f71e44e5113c7513db2da7a94e8cf744520f506"
  (String.join [
    "c3b4b7300a8d75a06a0074769f71e44e5113c7513db2da7a94e8cf744520f506a1192c22ed2f44a87c2b3966",
    "c52f8c7984f11017965a951e85df3cf60cf6b864040000000000000003000000000000000200000000000000",
    "010000000000000001000000000000002800000000000000"])
  (String.join [
    "8cf821265e2ca710fdbb6f0567d86c02c68618f7aa04134335c8ca84737009e9fe33f99b4530b9a88a3b2c53",
    "cd2f18a5c5a9633bbee6d26029ed7590e71dc69fe9af82f207dc7ecc"])
  (String.join [
    "6cca702d5aef5d5363fc87616aa0b67d22dc55423a02b28c4b3a09e3356a92db47bee6dd802458d6b022e402",
    "ba848d5b"])
  "be93514a563f9a0ceac9cd2d8caef37b0f97d2b363fa748fc17f13ba3cd24b68"
#guard shapeF.plain == 0 && shapeE.rows == 1

/-- Salts of 30 bytes: shorter than the shape's 40. -/
def shortSalts : Table := { toy with salt := fun x => (toy.salt x).extract 0 30 }

-- a salt that is too short is filled up with zero bytes
#guard meets shapeA shortSalts
  "dccf66dfdf2b6fe191a9ae7fbb7e59a80c80782d451369a3c20da74b0c547c46"
  (String.join [
    "dccf66dfdf2b6fe191a9ae7fbb7e59a80c80782d451369a3c20da74b0c547c46a1192c22ed2f44a87c2b3966",
    "c52f8c7984f11017965a951e85df3cf60cf6b864040000000000000008000000000000000300000000000000",
    "010000000000000001000000000000002800000000000000"])
  (String.join [
    "ed67b9ada457052bc397b92f2de3d73233a32ba1db9927b17461416fe286ebb0442d124cb28d8b14f2525446",
    "0b12c5c5a13fcced64d6850145c094036e8b8b513c167ee1d02925aab4d7dd1e60a2e3a6ceee3a5ed96536b5",
    "8bbbf00422692c5f"])
  (String.join [
    "a48b832890aa732f8c6a54d48cc5d6f8299806959e5fa3774cfd01c077e92b4597b9e0dfe8a39142c4552baa",
    "0181240e"])
  "0ba94ab3f7a4af56459fb007e69416fa7edd7ad574af5442f410e6e82e728f6d"
#guard parts honestA (commit shapeA files shortSalts) == (true, true, true)

-- an entry: root, answers and ID part. A tail entry or a salt's byte: the root parts, so the seeds
-- and with them the answers. A pad likewise. Two rows swapped likewise.
#guard [bentEntry, bentTail, bentPad, bentSalt, swapped].all fun T =>
  parts honestA (commit shapeA files T) == (true, true, true)
-- at the honest seeds the answers do not read tails or salts, and do read entries, pads and rows
#guard [bentTail, bentSalt].all fun T =>
  spell (answers shapeA T honestA.seeds) == spell honestA.answers
#guard [bentEntry, bentPad, swapped].all fun T =>
  spell (answers shapeA T honestA.seeds) != spell honestA.answers
-- byte 40 of a salt is beyond this shape's 40 bytes: it is cut and changes nothing
#guard parts honestA (commit shapeA files
    { toy with salt := fun x => if x == 5 then (toy.salt x).set! 40 0 else toy.salt x }) ==
  (false, false, false)
#guard (toy.salt 5).get! 39 != 0 && (toy.salt 5).get! 40 != 0
-- each word of the shape
#guard [{ shapeA with a := 5 }, { shapeA with l := 9 }, { shapeA with r := 4 },
    { shapeA with v := 2 }, { shapeA with s := 2 }, { shapeA with sigma := 48 }].all
  fun (S : Shape) =>
  (parts honestA (commit S files toy)).2.2
-- a public file
#guard parts honestA
    (commit shapeA [Fmt.ascii "toy\n", Fmt.ascii "laz\n", files.getD 2 default] toy) ==
  (true, true, true)
-- the expected values of the first shape are rejected at each changed table
#guard [bentEntry, bentTail, bentPad, bentSalt, swapped].all fun T => !meets shapeA T
  "1676a4fe09084b68784e62894dfe79edc6270b9569a0898cb6c48e09340dce60"
  (String.join [
    "1676a4fe09084b68784e62894dfe79edc6270b9569a0898cb6c48e09340dce60a1192c22ed2f44a87c2b3966",
    "c52f8c7984f11017965a951e85df3cf60cf6b864040000000000000008000000000000000300000000000000",
    "010000000000000001000000000000002800000000000000"])
  (String.join [
    "ed9cd53a35d66a55292c99c333f656e310fd08453b616e39f2412c07057e892016332b3f0e7a13b03f7d28f2",
    "1d21abdd5757006e7eb4f6f874b395b9bc3903da201711604d857318c1a2eea0589e34d180d8edde99e1bdd2",
    "7a57b1a71e4e99bc"])
  (String.join [
    "fed9314907f6689a246e3ee5ee455ef6b667c6f17772f054eea7ee924e247964192b05fdddb07260bac123d3",
    "5c70b688"])
  "b8d7312c1b374bcc0e6dfdda3391a8e998b63da37555f7da57975f452642fc59"

/-! ### 4. Agreements inside the library -/

/-- The digest of `files`. -/
def cfgT : ByteArray := Fmt.configDigest files

-- the root is that of the library's own builder of trees over the library's own leaves
#guard [shapeA, shapeB, shapeC].all fun S =>
  hex (commit S files toy).root ==
    hex (Fmt.rootOf (Fmt.build cfgT S.a ((List.range (2 ^ S.a)).map fun x =>
      Fmt.leaf 174 0 S.a x cfgT (columnOf S (laid S toy) x) (Fmt.fit S.sigma (toy.salt x)))))
-- over the one oracle
#guard parts honestA (commitO Fmt.oracle shapeA files toy) == (false, false, false)
-- over another oracle all parts
#guard parts honestA (commitO (fun s => Fmt.oracle (s ++ ⟨#[0]⟩)) shapeA files toy) ==
  (true, true, true)
-- a word that is not below p counts modulo p
#guard toy.entry 0 0 == 17 && parts honestA (commit shapeA files
    { toy with
      entry := fun b q => if b == 0 && q == 0 then UInt64.ofNat (p + 17) else toy.entry b q })
  == (false, false, false)

end Known
end Bind.Twin
