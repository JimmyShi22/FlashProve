-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules5.lean: a round's query and its answer: the hash calls, the blocks, the test of the proof
of work, the chain's next value, and the row of words of the verifier's message.

A proof file of the programs (the C++ implementation that comes with this Lean code) holds a chain's
bytes (by the page it can hold several chains: Fmt/Rules8.lean); a chain is a row of rounds. In each
round the prover's message is hashed together with the chain's value so far; the answer gives the
chain's next value and the verifier's message (the challenges). This file renders that step as total
functions on bytes and numbers.

Sources. It restates, in our own words, the fifth section of the format page (docs/format/FORMAT.md,
which comes with the programs), rules R5.1 to R5.7; written against an edition that is not the one
that ships. R5.1 to R5.7 are the same in a second edition, also not the one that ships. The page's
known answers in the tests are those of a third edition, also not the one that ships; they are the
same in the two editions named first. The file stands on
Fmt/Rules1.lean
(words, bits, test strings), Fmt/Plan.lean (the seven kinds of a verifier's message) and
Fmt/Rules23.lean (the hash formatHash and its numbers). Fmt/Rules4.lean (the chain's first value) and
Fmt/Rules6.lean (drawing) are imported for two connections: the tests' first values are those of the
fourth section's example chain, and rowOf is the sixth section's row of words of an array of blocks.
No Mathlib.

1. What the file contains.
   The rules.
   Rounds (R5.1). The rounds of a chain are numbered 1, 2, ... A round is a message of the prover
      and a message of the verifier, which may be empty. Every round asks its query. (A chain can
      end with a round of any kind: `Spec.ok` (Fmt/Rules8.lean) has no clause on it.)
   `tail`: What stands after the prover's message in call j: the word kind + 2^8 w + 2^16 j, then
      the word of the nonce (w: the round's proof-of-work bits).
   `call`: (R5.2) Call j of round i: the hash under the number 162, with the chain's label in the
      place of the tree's number, index i, started from the chain's value before the round, of the
      prover's message and that tail. 64 bytes.
   `block`: (R5.4) The answer is a row of blocks of 32 bytes: block 2 j is the first half of call j,
      block 2 j + 1 its second half.
   `firstBlock`: Without work (w = 0), block 0 is the chain's next value and the verifier's message
      begins at block 1. With work, block 0 is the test block, block 1 the chain's next value, and
      the message begins at block 2.
   The test of work (R5.5; `passesA`). The low w bits of the first word of the test block are 0 (at
      w = 64: the whole word). Nothing else of that block is read. Without work there is no test.
      The same in bits for w ≤ 64 (`bitAt`, `passesBits`; one test, at w = 8; no theorem in this
      file: `passes_bits`, Fmt/Rules5Laws.lean): the first w bits of the block are 0.
   `askOK`: (R5.2, R5.3, R2.3) What the page asks of a query's data: the label is below 2^48; the
      chain's value has 32 bytes; the round's number is at least 1; the message's length is a
      multiple of 8; w ≤ 64; the nonce is a word; without work the nonce is 0; a round of the kind
      "nothing" has no work. R5.3's other half (no work before a seal) is a condition on plans and
      stands in `Round.ok` (Fmt/Rules8.lean), not here. By R5.7, outside these bounds a function
      that renders the section answers "refused", and so `Chain.queryW` does. R5.7's "a kind outside
      1 to 7" cannot be written here: a kind is one of the seven of Fmt/Plan.lean. Beyond R5.7, this
      library's own: round 0, and a nonce that is no word, are refused too.
   One text, three readings. Every function that hashes, but for the forms at the identity monad and
   `Fmt.formatHash` below, is written over any monad m, with the hash h number tree index start bytes : m
   ByteArray as its first argument (names that end in W, and `fetchFrom`). At the identity monad and
   h := `Fmt.formatHash` it is the evaluation; all tests run there but the last, which runs at `HO oracle`
   (Fmt/Rules23.lean). At the identity monad and the hash over a variable oracle it is a function of
   that oracle. At a monad of trees of questions it is a tree of questions. At the identity monad
   and the Lean program's hash (`formatHashFastForm`, OnBytes/Hash/H.lean), `askOK`, `callW`, `fetchFrom`,
   `fetchW`, `passesA`, `nextA`, `msgA` and `Chain.queryW` are text that the program's main runs
   (through OnBytes/ChecksWithHashAsArgument/M/Chain/EngineM.lean).
   `callW`, `fetchW h .. n`: Call j. The blocks 0 .. n − 1, fetched in order into an array: calls 0
      .. ceil(n / 2) − 1, each cut in two (if n is odd the last call's second half is asked and
      dropped).
   There is no lazy row of words across the monad: a round first fetches a fixed number of blocks,
   and all that follows is a pure function of that array.
   `passesA w bs`, `nextA w bs`, `msgA w bs`: The test of work; the chain's next value; the blocks
      of the verifier's message.
   `rowOf vb`: Word t of the verifier's message: word t mod 4 of its block t div 4; 0 beyond the
      array. This is the row of words from which drawing reads.
   `Chain`, `Chain.queryW h c msg kind work nonce K`: The step of a chain: it fetches firstBlock
      work + K blocks, then tests. It gives nothing (none: no new chain) if the data are not in
      order (`askOK` is false; then nothing is asked) or the test of work fails; else the chain
      after the round and the K blocks of the verifier's message.
   `call`, `block`, `passes`, `nextRho`, `vblock`, `word`, `leastNonce`, `Chain.query`: The same at
      the identity monad and `Fmt.formatHash`, block by block. `leastNonce`: for tests and an example prover;
      no verifier calls it.
   A departure in the order of asking, not in any value. By the page nothing is drawn from an answer
   that fails the test of work, and a program computes a block only when a draw reaches it. Here all
   blocks of a round are asked before the test is made; what is put out is the same.
   Total where the page is silent. The page has j below 2^48. Here the word with j is spelled modulo
   2^64, as every word: for larger j the function has a value, which is no call of the format. A
   hash that returns fewer than 64 bytes gives shorter blocks, and words are read with 0 beyond the
   end. `askOK` does not ask the hash's other bounds (`hDom`, Fmt/Rules23.lean: on the index and on
   the length of the bytes); `Spec.small` (Fmt/Rules8.lean) asks them of a chain's description.

2. What is checked when the file compiles. 34 tests (#guard). The page's known answers, in both
fields. Tests of this library's own: fetching and the block-by-block form agree; the test of work in
words and in bits agree at all nonces below 100, in the second field (in the first field `passesA`
and `passes` are compared there). (The main groups, not every test.)

3. Theorems. Five small ones, under "Small facts".

4. What is not claimed. What is drawn from the words, and how many blocks K a round needs (the sixth
section). Which bytes of a file are a round's message and nonce (the eighth). The chain's first
value (the fourth): in the tests it is a literal, the page's known answer, and a test compares it
with the fourth section's function. No file holds a chain's value or a block: nothing here reads a
file.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules4
import Fmt.Rules6

namespace Fmt

/-- what stands after the prover's message in call j -/
def tail (kind : Kind) (w nonce j : Nat) : ByteArray :=
  u64n (kind.num + 2 ^ 8 * w + 2 ^ 16 * j) ++ u64n nonce

/-- the first block of the verifier's message -/
def firstBlock (w : Nat) : Nat := if w = 0 then 1 else 2

/-- What the page asks of a query's data (without the hash's other bounds: see the file's top
comment). -/
def askOK (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce : Nat) :
    Bool :=
  decide (lab < 2 ^ 48) && rho.size == 32 && decide (1 ≤ i) &&
    msg.size % 8 == 0 && decide (w ≤ 64) && decide (nonce < 2 ^ 64) &&
    (w != 0 || nonce == 0) && (kind != .nothing || w == 0)

/-! ## Over any monad -/

/-- Call j of round i. -/
def callW {m : Type → Type} (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (lab : Nat)
    (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce j : Nat) : m ByteArray :=
  h 162 lab i rho (msg ++ tail kind w nonce j)

/-- the calls j, j + 1, .., each cut in two, after what is there -/
def fetchFrom {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (lab : Nat) (rho : ByteArray)
    (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce : Nat) :
    Nat → Nat → Array ByteArray → m (Array ByteArray)
  | 0, _, acc => pure acc
  | n + 1, j, acc => do
    let c ← callW h lab rho i msg kind w nonce j
    fetchFrom h lab rho i msg kind w nonce n (j + 1)
      ((acc.push (c.extract 0 32)).push (c.extract 32 64))

/-- The blocks 0 .. n − 1 of the answer of round i. -/
def fetchW {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)
    (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce n : Nat) :
    m (Array ByteArray) := do
  let bs ← fetchFrom h lab rho i msg kind w nonce ((n + 1) / 2) 0 #[]
  pure (bs.extract 0 n)

/-! ## Pure, on the fetched blocks; then the chain and its step -/

/-- The test of work. -/
def passesA (w : Nat) (bs : Array ByteArray) : Bool := w == 0 || (wordAt (bs.getD 0 ByteArray.empty) 0).toNat % 2 ^ w == 0

/-- the test of work in bits: the first w bits of the test block are 0 -/
def passesBits (w : Nat) (bs : Array ByteArray) : Bool :=
  (List.range w).all fun k => bitAt (bs.getD 0 ByteArray.empty) k == false

/-- The chain's next value. -/
def nextA (w : Nat) (bs : Array ByteArray) : ByteArray := bs.getD (firstBlock w - 1) ByteArray.empty

/-- the blocks of the verifier's message -/
def msgA (w : Nat) (bs : Array ByteArray) : Array ByteArray := bs.extract (firstBlock w) bs.size

/-- Word t of the verifier's message. -/
def rowOf (vb : Array ByteArray) (t : Nat) : UInt64 :=
  wordAt (vb.getD (t / 4) ByteArray.empty) (8 * (t % 4))

/-- A chain between two rounds: its label; its value; how many rounds are done. -/
structure Chain where
  label : Nat
  rho   : ByteArray
  round : Nat

/-- The step of a chain. -/
def Chain.queryW {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (c : Chain) (msg : ByteArray)
    (kind : Kind) (work nonce K : Nat) :
    m (Option (Chain × Array ByteArray)) :=
  if askOK c.label c.rho (c.round + 1) msg kind work nonce then do
    let bs ← fetchW h c.label c.rho (c.round + 1) msg kind work nonce (firstBlock work + K)
    pure (if passesA work bs then some (⟨c.label, nextA work bs, c.round + 1⟩, msgA work bs)
      else none)
  else pure none

/-! ## At the identity monad and the hash formatHash -/

/-- call j of round i -/
def call (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce j : Nat) :
    ByteArray :=
  callW (m := Id) formatHash lab rho i msg kind w nonce j

/-- Block b of the answer of round i. -/
def block (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce b : Nat) : ByteArray :=
  (call lab rho i msg kind w nonce (b / 2)).extract (32 * (b % 2)) (32 * (b % 2) + 32)

def passes (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce : Nat) :
    Bool :=
  w == 0 || (wordAt (block lab rho i msg kind w nonce 0) 0).toNat % 2 ^ w == 0

def nextRho (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce : Nat) : ByteArray :=
  block lab rho i msg kind w nonce (firstBlock w - 1)

def vblock (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce n : Nat) : ByteArray :=
  block lab rho i msg kind w nonce (firstBlock w + n)

def word (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w nonce t : Nat) :
    UInt64 :=
  wordAt (vblock lab rho i msg kind w nonce (t / 4)) (8 * (t % 4))

/-- the least nonce that passes among n, n + 1, .., with so many tries -/
def leastFrom (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind) (w : Nat) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, n =>
    if passes lab rho i msg kind w n then some n else leastFrom lab rho i msg kind w fuel (n + 1)

/-- The least nonce below a bound that passes. -/
def leastNonce (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w bound : Nat) : Option Nat :=
  leastFrom lab rho i msg kind w bound 0

def Chain.query (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat) :
    Option (Chain × Array ByteArray) :=
  Chain.queryW (m := Id) formatHash c msg kind work nonce K

/-! ## The known answers -/

namespace Guard5

/-- the sixth kind, by its number -/
def kind6 : Kind := (Kind.ofNat? 6).getD .nothing

/-- words in a row -/
def ws (l : List Nat) : ByteArray := cat (l.map u64n)

/-- the six rounds of the page's toy plan: message, kind, bits of work, nonce -/
def rounds (nonce3 : Nat) : List (ByteArray × Kind × Nat × Nat) :=
  [(ws [4, 5, 6, 7, 8, 9], .elems, 0, 0), (ws [1, 1, 1], .nothing, 0, 0),
    (pattern 32 11 2, .positions, 8, nonce3), (ByteArray.empty, .seeds, 0, 0),
    (ws [9, 9, 9], .entries, 0, 0), (ws [77], kind6, 0, 0)]

/-- one more round after a chain and the values so far -/
def stepRun (st : Option (Chain × List String)) (r : ByteArray × Kind × Nat × Nat) :
    Option (Chain × List String) :=
  st.bind fun x => (x.1.query r.1 r.2.1 r.2.2.1 r.2.2.2 1).map fun y => (y.1, x.2 ++ [hex y.1.rho])

/-- the chain's values after the six rounds, in order; nothing if a step gives nothing. The toy
chain's label is 7 -/
def run (rho0 : ByteArray) (nonce3 : Nat) : Option (List String) :=
  ((rounds nonce3).foldl stepRun (some (⟨7, rho0, 0⟩, []))).map Prod.snd

def rho0F2 : ByteArray := unhex "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72"
def rho0F1 : ByteArray := unhex "8ab45624b5f889e335e84864762f4b3d7e51eb87d278e34722ed12b0e114d90c"
def rho2F2 : ByteArray := unhex "ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f"
def rho2F1 : ByteArray := unhex "d8ac18d0b18175bd94b96430ff4625456ad209bf4734b94dfccc445c74c72ad2"
def rho5F2 : ByteArray := unhex "1377c2217a2329b555a3bc638f2d842dfd01f57cf089aca2cea169d21e70fead"
def rho5F1 : ByteArray := unhex "6cfcaeee76d66e94659d96d96c9178dd7cb20ffaef41469d79921e37dbf1ff2c"
def root3 : ByteArray := pattern 32 11 2

-- the two first values are those of the fourth section's toy chain (label 7, with random bytes)
#guard (startChain 7 (Toy4.pd .two) Toy4.statement (some Toy4.rnd)).any fun c => c.rho0 = rho0F2
#guard (startChain 7 (Toy4.pd .one) Toy4.statement (some Toy4.rnd)).any fun c => c.rho0 = rho0F1

-- The page's known answers (those of another edition than the one that ships).
-- The second field: the chain's values
-- after rounds 1 to 6; round 3, eight bits of work: the least nonce, and block 0, the test block;
-- round 6, of the sixth kind: the sealed value is the first block of the verifier's message
#guard run rho0F2 116 == some [
  "3c98919bc70e2dca17b612fdf29be0f6b6f26efcdc04e845a11038260a5861fd", "ed50d6b77518037aa4dfcfd7bae987e6761391c089e349575d6ccac53aa3556f",
  "28d010de3f0b0b8da2ccdd36f9c476eb062e1e416389eb81f6a4eb0c60268495", "ad311297fb7c851c0561be363deb88aede14295352d4fcf8f478ed607c8ca10a",
  "1377c2217a2329b555a3bc638f2d842dfd01f57cf089aca2cea169d21e70fead", "70b365d8f0bda8f239fa4a9417b2ddddf69a25197785dd096c937c5d05064dad"]
#guard leastNonce 7 rho2F2 3 root3 .positions 8 2048 == some 116
#guard hex (block 7 rho2F2 3 root3 .positions 8 116 0) == "00a1907a594383d79b2b3036935cae89d269e199b114d175318be3d68e81c567"
#guard hex (vblock 7 rho5F2 6 (ws [77]) kind6 0 0 0) == "0b5ec9235d31cb34c68dd2f4f50a59b3b0fd28c246389e8f59cd0350416cfdd6"
-- the first field
#guard run rho0F1 1058 == some [
  "3ac6909ee4a779664bb338ddaa16e08a478ac005417dd95b79cb513918e16e8a", "d8ac18d0b18175bd94b96430ff4625456ad209bf4734b94dfccc445c74c72ad2",
  "b6a4b579d528fefdef7e64a696ade4089f0fec77d43b72600198d6833228958b", "586489761ec821687c8a7f60e2cb9a1fe8e3635cc6ca872fcb4375b6855e38c1",
  "6cfcaeee76d66e94659d96d96c9178dd7cb20ffaef41469d79921e37dbf1ff2c", "1ded778ef215493b19c0050a0a9b93411930b82a5c1399b324c806fe0d901fb9"]
#guard leastNonce 7 rho2F1 3 root3 .positions 8 2048 == some 1058
#guard hex (block 7 rho2F1 3 root3 .positions 8 1058 0) == "008d9a15b554b94ba50e4af56fc1dbe523966c7265355eb6834158d3269f2b45"
#guard hex (vblock 7 rho5F1 6 (ws [77]) kind6 0 0 0) == "dd228c00ad29dc3bb954e861ed335c21e032010f26e9813749b96bb7bad58fe6"

-- Tests of this library's own. A nonce that fails the test: the step gives nothing
#guard (run rho0F2 115).isNone
#guard (run rho0F1 1057).isNone
-- The label enters every call (R5.2): under another label the first round's value is another, and
-- the nonce of round 3 fails
#guard hex (nextRho 8 rho0F2 1 (ws [4, 5, 6, 7, 8, 9]) .elems 0 0) != "3c98919bc70e2dca17b612fdf29be0f6b6f26efcdc04e845a11038260a5861fd"
#guard passes 8 rho2F2 3 root3 .positions 8 116 == false
-- the chain after a round keeps its label
#guard ((⟨7, rho0F2, 0⟩ : Chain).query (ws [4, 5, 6, 7, 8, 9]) .elems 0 0 1).any fun y => y.1.label == 7 && y.1.round == 1
-- data that are not in order: a nonce without work; work in a round of the kind "nothing"; a
-- message whose length is no multiple of 8; more than 64 bits of work; round 0; a chain's value of
-- 31 bytes; a nonce that is no word; a label that is not below 2^48
#guard ((⟨7, rho0F2, 0⟩ : Chain).query (ws [1]) .elems 0 5 1).isNone
#guard ((⟨7, rho0F2, 0⟩ : Chain).query (ws [1]) .nothing 1 0 0).isNone
#guard ((⟨7, rho0F2, 0⟩ : Chain).query (pattern 7) .elems 0 0 1).isNone
#guard askOK 7 rho0F2 1 (ws [1]) .positions 65 0 == false
#guard askOK 7 rho0F2 0 (ws [1]) .elems 0 0 == false
#guard askOK 7 (pattern 31) 1 (ws [1]) .elems 0 0 == false
#guard askOK 7 rho0F2 1 (ws [1]) .positions 8 (2 ^ 64) == false
#guard askOK (2 ^ 48) rho0F2 1 (ws [1]) .elems 0 0 == false
#guard askOK (2 ^ 48 - 1) rho0F2 1 (ws [1]) .elems 0 0
-- 64 bits of work are in order (R5.5: the whole word is 0)
#guard askOK 7 rho0F2 1 (ws [1]) .positions 64 0
#guard passesA 64 #[u64n 0 ++ pattern 24] && passesA 64 #[u64n (2 ^ 63) ++ pattern 24] == false && passesA 63 #[u64n (2 ^ 63) ++ pattern 24]
-- fetching and the block-by-block form agree: five blocks with work, four without; the parts of the
-- array
#guard (fetchW (m := Id) formatHash 7 rho2F2 3 root3 .positions 8 116 5).toList.map hex == (List.range 5).map fun b => hex (block 7 rho2F2 3 root3 .positions 8 116 b)
#guard (fetchW (m := Id) formatHash 7 rho0F1 1 (ws [4, 5, 6, 7, 8, 9]) .elems 0 0 4).toList.map hex == (List.range 4).map fun b => hex (block 7 rho0F1 1 (ws [4, 5, 6, 7, 8, 9]) .elems 0 0 b)
#guard ((⟨7, rho2F2, 2⟩ : Chain).query root3 .positions 8 116 3).any fun y => y.2.toList.map hex == (List.range 3).map fun n => hex (vblock 7 rho2F2 3 root3 .positions 8 116 n)
#guard ((⟨7, rho2F2, 2⟩ : Chain).query root3 .positions 8 116 3).any fun y => (List.range 14).all fun t => rowOf y.2 t == (if t < 12 then word 7 rho2F2 3 root3 .positions 8 116 t else 0)
-- the test of work, nonces below 100: words and bits (second field); passesA, passes (first field)
#guard (List.range 100).all fun n => passesA 8 (fetchW (m := Id) formatHash 7 rho2F2 3 root3 .positions 8 n 1) == passesBits 8 (fetchW (m := Id) formatHash 7 rho2F2 3 root3 .positions 8 n 1)
#guard (List.range 100).all fun n => passesA 8 (fetchW (m := Id) formatHash 7 rho2F1 3 root3 .positions 8 n 1) == passes 7 rho2F1 3 root3 .positions 8 n
-- a block is the one oracle on the string of its half
#guard (List.range 6).all fun b => block 7 rho2F2 3 root3 .positions 8 116 b = oracle (oStr (UInt8.ofNat (b % 2)) 162 7 3 rho2F2 (root3 ++ tail .positions 8 116 (b / 2)))
-- the hash over the one oracle gives the same chain
#guard (Chain.queryW (m := Id) (HO oracle) ⟨7, rho2F2, 2⟩ root3 .positions 8 116 3).any fun y => hex y.1.rho == "28d010de3f0b0b8da2ccdd36f9c476eb062e1e416389eb81f6a4eb0c60268495"

end Guard5

/-! ## Small facts -/

/-- the row of words is the sixth section's -/
theorem rowOf_eq (vb : Array ByteArray) : rowOf vb = rowOfBlocks vb := rfl

theorem firstBlock_zero : firstBlock 0 = 1 := rfl
theorem firstBlock_pos (w : Nat) (hw : w ≠ 0) : firstBlock w = 2 := if_neg hw

/-- data that are not in order: nothing is asked, and nothing comes out -/
theorem Chain.queryW_bad {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (c : Chain) (msg : ByteArray)
    (kind : Kind) (work nonce K : Nat)
    (e : askOK c.label c.rho (c.round + 1) msg kind work nonce = false) :
    c.queryW h msg kind work nonce K = pure none := by
  unfold Chain.queryW
  rw [e]
  rfl

/-- a step at the identity monad and formatHash (`Chain.query`) that gives something: the data are in order,
and the chain after it has one round more and the same label -/
theorem Chain.query_some (c c' : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat)
    (vb : Array ByteArray) (e : c.query msg kind work nonce K = some (c', vb)) :
    askOK c.label c.rho (c.round + 1) msg kind work nonce = true ∧
    c'.round = c.round + 1 ∧
    c'.label = c.label := by
  unfold Chain.query Chain.queryW at e
  by_cases hq : askOK c.label c.rho (c.round + 1) msg kind work nonce = true
  · refine ⟨hq, ?_⟩
    rw [if_pos hq] at e
    have e' : (if passesA work
                (fetchW (m := Id) formatHash c.label c.rho (c.round + 1)
                  msg kind work nonce (firstBlock work + K)) = true then
            some ((⟨c.label,
                  nextA work
                    (fetchW (m := Id) formatHash c.label c.rho (c.round + 1)
                      msg kind work nonce (firstBlock work + K)),
                  c.round + 1⟩ : Chain),
                msgA work (fetchW (m := Id) formatHash c.label c.rho (c.round + 1)
                    msg kind work nonce (firstBlock work + K)))
          else none) = some (c', vb) := e
    split at e'
    · have := (Prod.mk.inj (Option.some.inj e')).1
      rw [← this]
      exact ⟨rfl, rfl⟩
    · cases e'
  · rw [if_neg hq] at e
    cases e

end Fmt
