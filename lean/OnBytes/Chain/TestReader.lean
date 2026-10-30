-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/TestReader.lean: tests of the reader, of the names of its checks and of a session.
No program imports this file.

The first example is the made-up chain of Fmt/Rules8X.lean (`Fmt.ToyX8`). Its file holds 32 random
bytes, a word, a nonce of two bytes, the openings of two stored trees and one element of the field.
The second example is a file of a chain with a tree, one of the format's known answers
(docs/format/format-vectors.txt; here `Fmt.Known8.file2`).
A session carries the record of the tree vertices met from one chain to the next
(OnBytes/Chain/Session.lean). An entry of that record is a root with vertices (depth, place, value).
-/
import OnBytes.Chain.Session
import OnBytes.Chain.Why

namespace OnBytes.TestReader

open Fmt.ToyX8

/-- The name of the check at which a file of the first example is refused, and the number of
rounds read before it. -/
def why (seen : Fmt.Seen) (b : ByteArray) : Option (String × Nat) :=
  (whyRefused spec seen b 0).map fun x => (x.1.name, x.2)

/-- b with the n bytes from place i on set to 255. -/
def allOnes (b : ByteArray) (i n : Nat) : ByteArray :=
  b.extract 0 i ++ ⟨Array.replicate n 255⟩ ++ b.extract (i + n) b.size

-- the honest file: read to its end, to the same last value as by the strict reader of Fmt/
#guard (readChain spec [] honest 0).map (fun x => (x.1.rho, x.2)) ==
  (Fmt.readChainX (m := Id) Fmt.formatHash spec [] honest 0).map fun x => (x.1.rho, x.2)
#guard (readChain spec [] honest 0).map (·.2) == some honest.size
#guard why [] honest == none

-- bytes are missing: at the chain's start; at the last element
#guard (readChain spec [] (honest.extract 0 31) 0).isNone && why [] (honest.extract 0 31) ==
  some ("form", 0)
#guard (readChain spec [] (honest.extract 0 (honest.size - 1)) 0).isNone &&
  why [] (honest.extract 0 (honest.size - 1)) == some ("form", 1)

-- words that are no elements: in an opened column; in the last message
#guard (readChain spec [] (allOnes honest 42 8) 0).isNone &&
  why [] (allOnes honest 42 8) == some ("form", 0)
#guard (readChain spec [] (allOnes honest (honest.size - 8) 8) 0).isNone &&
  why [] (allOnes honest (honest.size - 8) 8) == some ("form", 1)

-- another element in an opened column: the walk does not end in the root
#guard (readChain spec [] (Fmt.flipAt honest 42) 0).isNone &&
  why [] (Fmt.flipAt honest 42) == some ("opening", 0)

-- the leaf at depth 2, place 0, which the file opens, was met before under the same root with
-- another value (32 zero bytes)
#guard (readChain spec [(root0, [(2, 0, Fmt.zero32)])] honest 0).isNone &&
  why [(root0, [(2, 0, Fmt.zero32)])] honest == some ("one-value-at-a-vertex", 0)
-- under another root that is no hindrance
#guard (readChain spec [(Fmt.zero32, [(2, 0, Fmt.zero32)])] honest 0).isSome

-- a description that is not in order: one list of stored trees for two rounds
#guard ((whyRefused ⟨base root0 root1, [[⟨sh, 40, 0, 0, 5⟩]]⟩ [] honest 0).map fun x =>
  x.1.name) == some "description"

-- a session: the same chain read twice; the second reading meets the same values
#guard ((do
  let x ← readIn spec honest 0
  let y ← readIn spec honest 0
  pure (x.next, y.next, x.roots.length, x.seal.isSome) :
    InSession (Nat × Nat × Nat × Bool))).run == some (honest.size, honest.size, 0, false)

-- a session: a decision that says no refuses
#guard ((acceptIn (Y := Unit) ⟨spec, fun _ v => v.opened.length == 4⟩ () honest 0).run).isSome
#guard ((acceptIn (Y := Unit) ⟨spec, fun _ v => v.opened.length == 5⟩ () honest 0).run).isNone

-- the second example: one root is sent; a later chain can name its tree
#guard ((readIn (Fmt.SpecX.plain (Fmt.Known8.spec .two)) Fmt.Known8.file2 0).run.map fun x =>
  (x.next, x.roots.length, (x.tree 0).isSome, (x.tree 1).isSome)) ==
  some (Fmt.Known8.file2.size, 1, true, false)

/-- True if the reader refuses b exactly if `whyRefused` names a check. -/
def agreeOn (S : Fmt.SpecX) (b : ByteArray) : Bool :=
  (readChain S [] b 0).isNone == (whyRefused S [] b 0).isSome

-- No theorem ties the names to the reader. On both examples: with one bit changed in each byte in
-- turn, and cut after each byte in turn, a check is named exactly where the reader refuses.
#guard (List.range honest.size).all fun i => agreeOn spec (Fmt.flipAt honest i)
#guard (List.range (honest.size + 1)).all fun i => agreeOn spec (honest.extract 0 i)
#guard (List.range Fmt.Known8.file2.size).all fun i =>
  agreeOn (Fmt.SpecX.plain (Fmt.Known8.spec .two)) (Fmt.flipAt Fmt.Known8.file2 i)
#guard (List.range (Fmt.Known8.file2.size + 1)).all fun i =>
  agreeOn (Fmt.SpecX.plain (Fmt.Known8.spec .two)) (Fmt.Known8.file2.extract 0 i)

/-- The first example as it was read, cut to its first round, with that round's openings replaced by
one opening of n positions, each with a column of one element. Only the view is made from it: no
hash is right. -/
def wide (n : Nat) : Option Fmt.ChainOut :=
  match readChain spec [] honest 0 with
  | none => none
  | some (o, _) =>
    match o.rounds[0]?, (o.rounds[0]?).bind (·.opens.head?) with
    | some r0, some x =>
      let xs := List.range n
      let big : Fmt.OpenOut := { x.2.2 with cols := xs.map fun i => [i.toUInt64] }
      some { o with rounds := #[{ r0 with opens := [(x.1, xs, big)] }] }
    | _, _ => none

-- Long lists. A public file sets how many positions a round draws. Each guard ends in a stack
-- overflow if what it makes, the list of positions or the view, is made by a recursion as deep as
-- that number. Neither can fail on steps that grow with its square: the run would only be long.
-- The view's guard has no stored tree: of `openedXT` only the other trees' half, `openedOfT`, runs
-- at length.
#guard (listOfT ((List.range 300000).map fun i => (i * 7919) % 65536)).length == 65536
#guard (wide 300000).map (fun o => (viewOf { spec with stored := [[]] } o).opened.length) ==
  some 300000

end OnBytes.TestReader
