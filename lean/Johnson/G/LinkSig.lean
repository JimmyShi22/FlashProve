-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/LinkSig.lean: the sendings of a proof's first chain in the verifier on bytes, link by
link, as values from the three public files, and each link's signature.

For the callers of the blocks of a written proof file. Definitions, and tests by evaluation.
Main names:
  `SendRow`: one sending: its chain, the number of its entry "SEND seed", its label, the chain's
    codes, its sampled messages' shapes each with a radius (Johnson/G/PackList.lean), and its
    riders: the messages without an answer, which are sent here for a later block.
  `sendRowsOf`: all sendings of the seven chains, in order.
  `linkRows rows l`: the sendings of link number l of the first proof chain, in order of its
    moments. The number after the last link's is the last group's.
  `linkList rows l`: the sampled messages of all these sendings, in order.
  `linkSig cs rows l`: `Johnson.Pack.sigOf` at that list.
  `rowsFull`, `codesFull`: at the full-size example.
Whence the numbers of the test: Lean's evaluator, at the full-size example: the three shipped public
files policy.txt, layout.txt and KL.bin of prover/examples/target_full_f2, as Johnson/G/KitFull.lean
holds them, with their sums. No other file is read.
Limits: those of Johnson/G/Sends.lean and Johnson/G/PackList.lean. No theorem is stated; the tests
are evidence by evaluation at one example. That a link's signature in a description of the protocol
is the list of just these messages, in this order, is a proposal, not a fact of the verifier: a link
also reads messages that earlier links sent and it keeps (they are sent again at its moment 0, as
the verifier's `keptOf` lists them, and so stand in the list). The riders are in no signature here.
A sending belongs to a link by its label.
-/
import Johnson.G.PackFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Params

/-- One sending, with what is sampled and what rides. -/
structure SendRow where
  file : String
  chain : Nat
  entry : Nat
  label : String
  codes : Codes
  sampled : List (OracleShape × Nat)
  riders : List OracleShape

/-- All sendings of the seven chains, in order. -/
def sendRowsOf (pol lay KL : ByteArray) : Except String (List SendRow) := do
  let sends ← sendsOf pol lay KL
  let pack ← packListOf pol lay KL
  let flat := sends.flatMap fun c => c.sends.map fun s => (c, s)
  unless flat.length == pack.length do throw "the two lists have not as many sendings"
  pure ((flat.zip pack).map fun ((c, s), p) =>
    ⟨c.file, c.chain, s.entry, s.label, c.codes, p.2,
      (s.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩)

/-- The sendings of a link of the first proof chain. -/
def linkRows (rows : List SendRow) (l : Nat) : List SendRow :=
  rows.filter fun r => r.file == "proof" && r.chain == 0 && r.label.startsWith s!"link {l},"

/-- The sampled messages of a link, in order. -/
def linkList (rows : List SendRow) (l : Nat) : List (OracleShape × Nat) :=
  (linkRows rows l).flatMap (·.sampled)

/-- A link's signature. -/
noncomputable def linkSig (cs : Codes) (rows : List SendRow) (l : Nat) : Cb.Sig OnBytes.Slice.GE :=
  Johnson.Pack.sigOf cs (linkList rows l)

/-- The sendings at the full-size example; empty if the making refuses. -/
def rowsFull : List SendRow :=
  (sendRowsOf KitFull.policy.toUTF8 KitFull.layout.toUTF8 KitFull.scales).toOption.getD []

/-- The codes of the proof's chains at the full-size example. -/
def codesFull : Codes := ((linkRows rowsFull 0).head?.map (·.codes)).getD {}

-- 119 sendings. The first proof chain has 26 groups: 25 links of three sendings and the last
-- group's one. Link by link: the sampled messages; one rider each. The test of
-- Johnson/Pack/Check.lean holds at each link's whole list.
#guard
  let R := rowsFull
  let cs := ((linkRows R 0).head?.map (·.codes)).getD {}
  R.length == 119 &&
  (List.range 27).map (fun l => (linkRows R l).length) == List.replicate 25 3 ++ [1, 0] &&
  (List.range 26).map (fun l => (linkList R l).length) ==
    [6] ++ (List.replicate 11 [6, 7]).flatten ++ [6, 5, 1] &&
  ((List.range 26).all fun l => ((linkRows R l).flatMap (·.riders)).length == 1) &&
  ((List.range 26).all fun l => Johnson.Pack.allMeet cs (linkList R l))

end Johnson.G
