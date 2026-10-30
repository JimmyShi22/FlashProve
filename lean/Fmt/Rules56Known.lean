-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules56Known.lean: what the six rounds of the format page's example chain draw, and the seed of
a stored table's record, computed from the chain's start by the real hash: the page's known answers,
in both fields (`Fld`, Fmt/Rules1.lean).

Fmt/Rules6Round.lean has the same twelve rounds' draws as tests on rows of words given as numbers,
which the page does not print. Here no row is given. Each round's query is asked of the hash
(Fmt/Rules5.lean: Chain.query, at Fmt.formatHash: BLAKE2b), as many blocks of the verifier's message are
fetched as the plan's entry allows at most (blocksFor (wordsAtMost e k)), and the round's message is
drawn from them (drawRound on rowOf). So these tests run sections 1 to 6 together: spellings, the
hash, the first query, a round's query, the test of work, drawing.

Sources. Sections 5 and 6 of the format page (docs/format/FORMAT.md, which comes with the programs,
the C++
implementation that comes with this Lean code), in an edition that is not the one that ships. The
six rounds' known answers are the same in a second edition, also not the one that ships; not held
against the page that ships. The record's seed is at the name of a table of the edition named first;
it is the same in two other editions, neither of them the one that ships.

1. What the file contains. Definitions that can be evaluated.
   `toyMsgs`, `toyKinds`: The six rounds' prover's messages and kinds, as the page's known answers
      name them. The entries are the example plan's (Fmt/Rules4.lean: `Toy4.plan`).
   `stepDraw`, `toyDraws f n`: The chain from its first value (label 7, with the random bytes)
      through the six rounds; n: the nonce of round 3, which has 8 bits of work.
   `recordSeeds f name v a`: The seeds of a stored table's record: a chain of its own, under the
      label 2^32 (Fmt/Rules4.lean: `recordLabel`, `recordFirst`), one round of the kind "seeds" with
      an empty message, then `a` seeds of `v` coordinates.

2. What is checked when the file compiles. Six tests (#guard), three in each field. What the six
rounds draw. The record's seed. The values are the page's, digit for digit. At a nonce that fails
the test of work `toyDraws` gives nothing.

3. Theorems. None. A test is an evaluation made while the file compiles; it leaves no declaration.

4. What is not claimed. Nothing on files (a chain in a file is another section's matter).

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules5
import Fmt.Rules6Round

namespace Fmt
namespace Known56

/-- words, spelled one after the other -/
def ws (l : List Nat) : ByteArray := cat (l.map u64n)

/-- the six rounds' prover's messages -/
def toyMsgs : List ByteArray :=
  [ws [4, 5, 6, 7, 8, 9], ws [1, 1, 1], pattern 32 11 2, ByteArray.empty, ws [9, 9, 9], ws [77]]

/-- the six rounds' kinds -/
def toyKinds : List Kind := [.elems, .nothing, .positions, .seeds, .entries, .sealed]

/-- one round: ask, fetch the most blocks that the entry allows, draw -/
def stepDraw (f : Fld) (st : Option (Chain × List Drawn)) (r : Entry × Kind × ByteArray × Nat) :
    Option (Chain × List Drawn) :=
  match st with
  | none => none
  | some (c, l) => match c.query r.2.2.1 r.2.1 r.1.work r.2.2.2 (blocksFor (wordsAtMost r.1 r.2.1)) with
    | none => none
    | some (c', vb) => some (c', l ++ [drawRound f r.1 r.2.1 (rowOf vb)])

/-- What the six rounds draw, from the chain's start. -/
def toyDraws (f : Fld) (nonce3 : Nat) : Option (List Drawn) :=
  match startChain 7 (Toy4.pd f) Toy4.statement (some Toy4.rnd) with
  | none => none
  | some hd =>
    (((Toy4.plan f).entries.zip (toyKinds.zip (toyMsgs.zip [0, 0, nonce3, 0, 0, 0]))).foldl
      (stepDraw f) (some (⟨7, hd.rho0, 0⟩, []))).map Prod.snd

/-- The seeds of a stored table's record: `a` seeds, each with a point of `v` coordinates. -/
def recordSeeds (f : Fld) (name : ByteArray) (v a : Nat) : Option (List (List Ext × Ext)) :=
  match (⟨recordLabel, recordFirst name, 0⟩ : Chain).query
      ByteArray.empty .seeds 0 0 (blocksFor (a * (v * 18 + 36))) with
  | none => none
  | some (_, vb) => some (((drawSeed f v).times a (rowOf vb) 0).1)

-- field 2: the six rounds, from the chain's first value on, by the hash
#guard toyDraws .two 116 = some [
    ⟨[(4610700807997304418, 4447928095050642327, 12963931155414147300)], [], [], none⟩,
    ⟨[], [], [], none⟩,
    ⟨[(1566154797897025065, 5902544055155014206, 6066228902280467927)], [69, 895, 454, 526, 842], [], none⟩,
    ⟨[(10242453029133591669, 14074992841984905743, 12408565391145546959), (3606079508961713394, 16625540050041287054, 18228235731105415187), (12223257125875722716, 11485735129323258346, 7129091038179324709)], [], [], none⟩,
    ⟨[], [], [0, 1, 0, 0, -1, -1, 0, 0, -1, 1, -1, 0, 0, 0, 1, 1, 0, 0, -1, 1, 1, 0, 1, -1, -1, -1, 1, 0, 1, -1, -1, 0, 0, 0, 0, 1, 0, -1, 0, 1], none⟩,
    ⟨[], [], [], some (unhex "0b5ec9235d31cb34c68dd2f4f50a59b3b0fd28c246389e8f59cd0350416cfdd6")⟩]
-- field 2: the seed of a stored table's record, at a name by R4.10 (root, the toy's configuration's
-- digest, six words), two coordinates: the point; the factor
#guard recordSeeds .two (tableName (pattern 32 13 4) Toy4.cfg 10 3 40 9 1 40) 2 1 = some [([(9697749137137958355, 613613959841214928, 8403959380172774020), (15526148976690303146, 2032215208828410348, 4053187377642565227)], (14917727018641805655, 3966560771581124203, 17230899846445233913))]

-- field 1: the six rounds, from the chain's first value on, by the hash
#guard toyDraws .one 1058 = some [
    ⟨[(409361236637539239, 40035298637638609, 2235074053556579745)], [], [], none⟩,
    ⟨[], [], [], none⟩,
    ⟨[(2026416711000827630, 1186740266042479584, 703665205314857216)], [948, 30, 628, 774, 1014], [], none⟩,
    ⟨[(215140809556339522, 755276408924441934, 471292596782118740), (230195220646656464, 958046372488734896, 666710011286853005), (208866533461959506, 89463761546949817, 218210764656520523)], [], [], none⟩,
    ⟨[], [], [1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, -1, 1, 0, -1, -1, 1, 0, 0, -1, 0, 0, 1, 0, -1, 0, -1, 0, 0, 1, 0, 0, -1, 1, 1, 1, 1, 1, 0, -1], none⟩,
    ⟨[], [], [], some (unhex "dd228c00ad29dc3bb954e861ed335c21e032010f26e9813749b96bb7bad58fe6")⟩]
-- field 1: the same
#guard recordSeeds .one (tableName (pattern 32 13 4) Toy4.cfg 10 3 40 9 1 40) 2 1 = some [([(474377100283182547, 613613959841214928, 1486430352531692164), (1691090921408139434, 2032215208828410348, 1747344368428871275)], (1082668963359641943, 1660717762367430251, 1089998781949376249))]

-- a nonce that fails the test of work: the chain stops, nothing is drawn
#guard toyDraws .two 115 = none
#guard toyDraws .one 1057 = none

end Known56
end Fmt
