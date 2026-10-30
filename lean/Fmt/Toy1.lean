-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Toy1.lean: a test of the byte format's rules on a small protocol of this library's own: in
tests, its verifier on bytes accepts the two honest files and refuses all 19 altered ones.

The verifier is this library's rendering of the page's verifier of the rehearsal's toy, on bytes:
the reader of a chain in a file at the toy's plan, then the toy's decision. (The toy was made to
rehearse a run: Fmt/Toy1Files.lean.)
Definitions and guards (#guard). The literals of the guards are put in by a program from the text
that came with the files. No Mathlib.
(In this head "the programs" are the C++ implementation that comes with this Lean code, and "the
format page" is docs/format/FORMAT.md, which comes with the programs.)
This library's own toy, not the programs' (Fmt/Toy1Files.lean says what it is and where its files
come from). The rules are the format page's, as Fmt/Rules1.lean .. Fmt/Rules8.lean state them, each
head telling its edition; the files: another edition than the one that ships (Fmt/Toy1Files.lean).

Main names:
  `plan`, `cfg`, `params`, `spec c`: the toy's plan (R4.3); its configuration's digest (R4.9: one
    public file); the parameters' bytes; what the reader of Fmt/Rules8.lean needs of the chain, at
    the claim c: label 7; random bytes in the file; round 1: one root, 8 bits of work, 3 positions
    below 16, the tree's opening behind the nonce; round 2: one element of the extension field, an
    empty verifier's message.
  `decision c o`: the toy's decision on a chain that was read: the element s of round 2 is c + the
    sum of the symbols at the listed positions.
  `verifyW h c file : m Bool`: the verifier, over any monad, the hash first: read the whole file
    (`wholeChain`), refuse if that refuses, else decide. `verify`: the same at the identity monad
    and `Fmt.formatHash`.
  `why c b`: a second verifier, written out step by step for this toy from the sections' functions,
    without the fold: it says which check refuses, in the order: the work test; the spelling of a
    symbol; the walk and the root; the spelling of s; the file's end; the decision. A file that ends
    too early is refused as too short at the step that lacks the bytes. `why` also answers with the
    work test if the chain cannot be started, and if round 2's query refuses.

What the guards test: `verify` accepts the two honest files and refuses the 19 altered ones; `why`
gives for each of the 21 files what the table of Fmt/Toy1Files.lean says (the table comes from the
reference program's own verifier); the honest file under another claim is refused, at the work test;
over the one oracle the verifier says the same; every intermediate value that the reference program
printed for the first honest file is computed and compared with it: the configuration's digest, the
parameters' bytes and digest, the statement's bytes, the run's value, the chain's three values, the
least nonce, both calls of round 1, the test block, the positions and their list, all 16 leaves, all
15 vertices, the root, the given digests with their places, s; the file itself, put together
from the honest prover's data, is compared with the first honest file.

Limits: no theorem; guards are tests by evaluation. Nothing ties this verifier to the verifier of a
theorem: that is the matter of the folder Run. This file says nothing on the programs' own files:
its sources include none. The programs' own files of the first toy (a product test; not this file's
toy) are held as bytes in Fmt/M1ProgPTFiles.lean, Fmt/M1ProgPRFiles.lean and Fmt/M1ProgPFFiles.lean;
the honest proof of each set is read by the strict reader, with every printed value recomputed, in
Fmt/M1EnginePT.lean, Fmt/M1EnginePR.lean and Fmt/M1EnginePF.lean; and all are judged in
Fmt/M1FullProg.lean, Run/PlanQSFProg.lean and files Run/M1Engine*.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules8
import Fmt.Toy1Files

namespace Fmt
namespace Toy1

/-- The toy's plan. -/
def plan : Plan where
  field := .two
  salt := 40
  nonce := 8
  posB := 0
  samples := 0
  saved := 1
  entries := [
    { name := "toy: positions", work := 8, msg := 32, roots := 1, poss := 3, logN := 4 },
    { name := "toy: nothing", msg := 24 } ]

def entry1 : Entry := plan.entries.getD 0 default
def entry2 : Entry := plan.entries.getD 1 default

/-- The one tree: depth 4, three base-field elements a column, made in the run, number 0. -/
def shape : Shape := { a := 4, W := 3, tree := 0 }

/-- The configuration's digest: one public file, the three letters of "toy" and a line feed. -/
def cfg : ByteArray := configDigest [ascii "toy\n"]

def params : ByteArray := paramsBytes plan cfg []
def statement (c : Ext) : ByteArray := items [("toy: claim", ext c)]

/-- The claim of the rehearsal. -/
def claim : Ext := (1, 2, 3)

/-- The chain, as the reader needs it. -/
def spec (c : Ext) : Spec where
  label := 7
  plan := plan
  params := params
  statement := statement c
  rand := .inFile
  cfg := cfg
  rounds := [
    { entry := entry1, kind := .positions, items := [.root], opens := [(shape, .own 0)] },
    { entry := entry2, kind := .nothing, items := [.e] } ]

/-- Addition in the base field. -/
def addF (f : Fld) (x y : UInt64) : UInt64 := UInt64.ofNat ((x.toNat + y.toNat) % f.p)

/-- Addition in the extension field, coordinate by coordinate. -/
def addE (f : Fld) (x y : Ext) : Ext := (addF f x.1 y.1, addF f x.2.1 y.2.1, addF f x.2.2 y.2.2)

/-- A column of three words as a symbol. -/
def symOf : List UInt64 → Option Ext
  | [a, b, c] => some (a, b, c)
  | _ => none

/-- c + the sum of the symbols; nothing if a column is no symbol. -/
def sumE (f : Fld) (c : Ext) : List (List UInt64) → Option Ext
  | [] => some c
  | col :: r => (symOf col).bind fun x => sumE f (addE f c x) r

/-- The toy's decision. -/
def decision (c : Ext) (o : ChainOut) : Bool :=
  match o.rounds[0]?, o.rounds[1]? with
  | some r1, some r2 =>
    match r1.opens, r2.vals with
    | [(_, _, op)], [.e s] => sumE .two c op.cols == some s
    | _, _ => false
  | _, _ => false

/-- The verifier, over any monad. -/
def verifyW {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)
    (c : Ext) (file : ByteArray) : m Bool := do
  match ← wholeChain h (spec c) file with
  | none => pure false
  | some o => pure (decision c o)

/-- The verifier at the hash formatHash. -/
def verify (c : Ext) (file : ByteArray) : Bool := verifyW (m := Id) formatHash c file

/-- The chain as read, at the hash formatHash. -/
def read (c : Ext) (file : ByteArray) : Option ChainOut := wholeChain (m := Id) formatHash (spec c) file

/-! ## The second verifier: step by step, with the check that refuses -/

/-- The length of an opening at a list: a column and a salt for each position, then the given
digests. -/
def openLen (xs : List Nat) : Nat := (24 + 40) * xs.length + 32 * (walkPlaces 4 xs).length

/-- Which check refuses; nothing: accepted. -/
def why (c : Ext) (b : ByteArray) : Option Why :=
  match slice b 0 32, slice b 32 32, rdWord b 64 with
  | some rnd, some root, some (nonce, _) =>
    match startChain 7 (paramsDigest params) (statement c) (some rnd) with
    | some ⟨some run, rho0⟩ =>
      match (⟨7, rho0, 0⟩ : Chain).query
          root .positions 8 nonce.toNat (blocksFor (wordsAtMost entry1 .positions)) with
      | none => some .work
      | some (ch, vb) =>
        let xs := listOf (drawRound .two entry1 .positions (rowOf vb)).poss
        if b.size < 72 + openLen xs then some .short
        else
          match readOpening cfg .two 40 shape run xs b 72 with
          | none => some .spelling
          | some op =>
            if op.root != root then some .walk
            else if b.size < op.next + 24 then some .short
            else
              match readE .two b op.next with
              | none => some .spelling
              | some s =>
                if b.size != op.next + 24 then some .long
                else if (ch.query (ext s) .nothing 0 0 0).isNone then some .work
                else if sumE .two c op.cols == some s then none else some .decision
    | _ => some .work
  | _, _, _ => some .short

/-! ## Guards -/

#guard (spec claim).ok

-- The 21 files: accepted or refused
#guard verify claim honest
#guard verify claim honest2
#guard files.all fun x => verify claim x.2.1 == x.2.2.isNone
#guard (files.filter fun x => verify claim x.2.1).map (·.1) = ["honest", "honest2"]
-- which check refuses: as the table says, file by file
#guard files.all fun x => why claim x.2.1 == x.2.2
-- those that only the decision refuses are read by the reader; the other refused ones are not
#guard (files.filter fun x => (read claim x.2.1).isSome).map (·.1) = ["honest", "honest2", "alt08", "alt16"]
-- the honest file under another claim: refused, at the work test
#guard verify (1, 2, 4) honest == false
#guard why (1, 2, 4) honest == some .work
-- over the one oracle the verifier says the same on all 21
#guard files.all fun x => Id.run (verifyW (m := Id) (HO oracle) claim x.2.1) == x.2.2.isNone

-- The intermediate values, of the first honest file. The configuration's digest; the parameters'
-- bytes; the statement's bytes
#guard hex cfg = "e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f"
#guard hex params = "140000000000000074686520666f726d617427732076657273696f6e08000000000000004838323100000000020000000000000001000000000000002800000000000000080000000000000000000000000000000000000000000000010000000000000002000000000000000e00000000000000746f793a20706f736974696f6e73010000000000000008000000000000002000000000000000010000000000000000000000000000000000000000000000000000000000000003000000000000000400000000000000000000000000000000000000000000000c00000000000000746f793a206e6f7468696e67010000000000000000000000000000001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d00000000000000636f6e66696775726174696f6e2000000000000000e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f"
#guard hex (statement claim) = "0a00000000000000746f793a20636c61696d1800000000000000010000000000000002000000000000000300000000000000"
-- the parameters' digest, the run's value, the chain's first value and its value behind round 2
#guard ((read claim honest).map fun o => (hex o.pd, o.run.map hex, hex o.rho0, hex o.rho)) =
  some ("ea7dd651ee7905f1a6a0ba17ec9e384f651766d33c0cedaa082d6019a60af476", some "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f",
    "859319d1a3c364e3bd1ee29afbe8d1b2e704b8136655150c579449cb3fb776d3", "58f979c24596f408217cea4c8b5674849bb7cf2a3c724d300cd1db95d6fac945")

def rho0 : ByteArray := unhex "859319d1a3c364e3bd1ee29afbe8d1b2e704b8136655150c579449cb3fb776d3"
def run : ByteArray := unhex "f7baeb7d1660e0ad5119c68da6d514a557cd59c60cc151cddcf6028486ff801f"
def root : ByteArray := unhex "4c9ba0664f4d73c58082e23e7445acd360498577414dcc7d4a4c5b5dccc367b8"

-- round 1: the least nonce; its two calls; the test block; the chain's value behind it
#guard leastNonce 7 rho0 1 root .positions 8 4096 = some 57
#guard hex (call 7 rho0 1 root .positions 8 57 0) = "00b6174e93316772a49de96a983e4869d056e7335a5f379aef67ab67f260d95314d4912ffda078d3c9fb4456ad62d072069a32df98740b14d03d89b521afa2df"
#guard hex (call 7 rho0 1 root .positions 8 57 1) = "332a3ef7310dfba5ff95ec90b8a0a05588d9730aa2dc53dae1e2348ab7f93b2259de2768b2485713e5a53771cc5216d0ec6b71ad403e7337d3438cb48e3a0d48"
#guard hex (block 7 rho0 1 root .positions 8 57 0) = "00b6174e93316772a49de96a983e4869d056e7335a5f379aef67ab67f260d953"
#guard hex (nextRho 7 rho0 1 root .positions 8 57) = "14d4912ffda078d3c9fb4456ad62d072069a32df98740b14d03d89b521afa2df"
-- the next nonce that passes (the fourth altered file's)
#guard leastFrom 7 rho0 1 root .positions 8 4096 (57 + 1) = some 310
-- the nonce in the file, the positions as drawn, their list
#guard ((read claim honest).bind fun o => o.rounds[0]?.map fun r => (r.nonce, r.drawn.poss, r.list)) = some (57, [3, 15, 8], [3, 8, 15])

/-- The honest prover's row: column x is (x + 1, 2 x, 7); its salts. -/
def col (x : Nat) : List UInt64 := [UInt64.ofNat (x + 1), UInt64.ofNat (2 * x), 7]
def saltAtX (x : Nat) : ByteArray := pattern 40 (x + 2) 1
def values : List (List ByteArray) :=
  build cfg 4 ((List.range 16).map fun x => leaf 164 0 4 x run (col x) (saltAtX x))

-- the tree: all sixteen leaves; the vertices level by level; the root
#guard (values.getD 4 []).map hex = [
  "b30d3c87841192205a053419c707c8e9956ff11fa7b90758da5418aa7a64573e", "6691c2934e75151a1591d8c289527f2fe3ddbc6b397dfd36fcf2a26360a606d2", "f7d44dd626eb0c145d13e843a55d9516e1214f62273b77e95b747a4bbb76049d", "77221b9d6c1ff9ff33c2b01d008d191ed515ae9a633f4b55c67d18414c6a5f89",
  "9559f7d89e62b91a5089ebce0627df00d179381a22647103fd08312b6a05ad2e", "7c59d4f12fc75e934471f05293b8ebf2dfd476fa9b735f48216a4d784660c2c2", "5d01635b7395190c03ba970cc724f862e8a5b627bfed90284b0cfa85b8b3c9ce", "4cca68e9db46a70a76274d2a9bf7d86053d44c28069cec6d0d8c6a1a2eb75c50",
  "de9e85d7157d7b3d360b24bf1abf1b19b495caea0024bebb994f0d5e824958b0", "6d3ed99a9bd4557d71d23ebc9bc1a604d744fe1f83fcecf04f04ffafe32dcc32", "2bf2474fa5e9cabd427d61cb1a24d81b9ef5602544e707b8bee73047bd6d56f9", "61275cfed3868ecd868b0bb15be3a5bbed1a1461c239764d22aaba01785188f0",
  "2e276884985478a186c82ffa6b5723b061deaca35d90ad120808d55ece889e46", "992c24be7538c67cfc8f2cf909e55511e5f42d57b5da843f515615a6f40f6825", "f73e5ce4584f1a73b6d37e4587e580372886cf35ad4f0fe6b6565e9c998939e1", "d0bcfeb5fc6842b5bbae1a59eefa9f554f8e5459ae3f8fb4910fb3924d6833d1"]
#guard (values.getD 3 []).map hex = [
  "fd31e1a6d8ea52829253cc678ccb74072a14cc98ed24441817e052467eb52119", "1f5bd93e8f2dd72c2f577b8b10f7543c27771c9c55bf42836af9fa34a27a820d", "6ffb809bd5a2159996f4ae62d8c1af7455b59d12c3e426fc43076a11eeb3f79a", "cbf44d214c5db152061fc0dc1892d8f71dc2e8802c3d96cd8f7caa7121552ca1",
  "72aaca51a0b2368af0a3357b543343ff0b28a4f83eb5fbb7b97f15e2035846de", "db718904075b6e164aa87dd3d19aa9879442de5abc70e1b32b638a170f09f9cf", "36aa5c581e551d9a4048ca1bc03b8f0fe746e72a1e2838435751b76a64224696", "f8e47aa0ee09e70eb1e645778c47dc980fb658487d84b2918e575621f9fb7a65"]
#guard (values.getD 2 []).map hex = [
  "718aabdf879449d8031242ad80ff281c5aed12c5d97e40c1cef3bb9fa5c84084", "e0163aeb56fc5004a33f745487d1aefe9b8214c64e3293130050a9fd268475de", "33cf8f304cb1ebee86dae3f861ac4b36555dbc9ef30ac4939a20ade64436e894", "694c4895f51ead81872c87dd274c8af7453dabdd73b340707e71ce07a0ab9a75"]
#guard (values.getD 1 []).map hex = [
  "d464ec38a9ec1e26b2d2cce40077700c245086305feab7f58d113636266a9d4b", "6808d01fffb623955760d1c1808105e5b41c55038af33fd6060ddb91cc390c7c"]
#guard rootOf values = root
-- the given digests: their places, in the walk's order; their values as read from the file
#guard walkPlaces 4 [3, 8, 15] = [(4, 2), (4, 9), (4, 14), (3, 0), (3, 5), (3, 6), (2, 1)]
#guard ((read claim honest).bind fun o => o.rounds[0]?.bind fun r => r.opens.head?.map fun x => x.2.2.given.map hex) = some [
  "f7d44dd626eb0c145d13e843a55d9516e1214f62273b77e95b747a4bbb76049d", "6d3ed99a9bd4557d71d23ebc9bc1a604d744fe1f83fcecf04f04ffafe32dcc32", "f73e5ce4584f1a73b6d37e4587e580372886cf35ad4f0fe6b6565e9c998939e1",
  "fd31e1a6d8ea52829253cc678ccb74072a14cc98ed24441817e052467eb52119", "db718904075b6e164aa87dd3d19aa9879442de5abc70e1b32b638a170f09f9cf", "36aa5c581e551d9a4048ca1bc03b8f0fe746e72a1e2838435751b76a64224696",
  "e0163aeb56fc5004a33f745487d1aefe9b8214c64e3293130050a9fd268475de"]
-- the columns and salts as read are the honest prover's; the root in which the walk ends
#guard ((read claim honest).bind fun o => o.rounds[0]?.bind fun r => r.opens.head?.map fun x => (x.2.2.cols, x.2.2.salts, x.2.2.root)) = some ([3, 8, 15].map col, [3, 8, 15].map saltAtX, root)
-- s
#guard sumE .two claim ([3, 8, 15].map col) = some (30, 54, 24)
#guard ((read claim honest).bind fun o => o.rounds[1]?.map fun r => r.vals) = some [.e (30, 54, 24)]
-- The whole file, put together from the honest prover's data, is the file
#guard pattern 32 5 1 ++ root ++ u64n 57 ++ openingBytes 4 col saltAtX values [3, 8, 15] ++ ext (30, 54, 24) = honest
-- the second honest file: its nonce, its positions, their list, the number of given digests that the walk takes
#guard ((read claim honest2).bind fun o => o.rounds[0]?.map fun r => (r.nonce, r.drawn.poss, r.list, r.opens.map fun x => x.2.2.given.length)) = some (100, [6, 13, 15], [6, 13, 15], [6])
-- a file's length follows from its list: in both honest files
#guard [honest, honest2].all fun b => ((read claim b).bind fun o => o.rounds[0]?.map fun r => 72 + openLen r.list + 24) = some b.size
-- addition is modulo p
#guard addF .two 18446744069414584320 1 = 0
#guard addE .two (18446744069414584320, 5, 0) (2, 18446744069414584320, 7) = (1, 4, 7)

end Toy1
end Fmt
