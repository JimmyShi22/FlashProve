-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hash/Octopus.lean: pruned Merkle paths ("authentication octopus"): the definitions.

Definitions only; what is proved of them is in Hash/OctopusFacts.lean.

To open several leaves of one binary hash tree one need not send a whole path for each. It is enough
to send, level by level from the leaves up and from left to right within a level, the sibling of
each node that lies on a path unless that sibling lies on a path itself (Aumasson and Endignoux,
"Improving stateless hash-based signatures", ePrint 2017/933, section 3.5). The verifier walks up:
at each level it hashes two neighbours, siblings, both of which it has, and for a node whose sibling
it does not have it takes the next digest of the message.

A level is a list js of node numbers and, beside it, the list of their digests. What is hashed with
what, and how many digests of the message (the list of digests that is sent) are taken, depends on
js only:
  `sib i j`         i is even and j = i + 1.
  `up js`           The numbers of the parents: two neighbours in the list that are siblings have
                    one parent; every other node has its own parent.
  `need1 js`        How many digests of the message this level takes; `need d js`: d levels.
  `stepC`, `octC`   The joint verification, over any monad with a function `hN` that hashes two
                    children: the digests after one level, after d levels. The message is read with
                    `headD default`: a message that is too short is read as if padded; so is the
                    list v of the nodes' digests, whose length `octC` does not compare with that of
                    js (`octSound`, Compile/OctopusRom.lean, has v.length = js.length as a
                    hypothesis). `octC` does not compare the length of the message with need d js:
                    that is its caller's task.
  `reads1`, `reads` Pruning: from whole paths (one for each node of js), the digests that the
                    verification takes, in its order. Of two siblings the path of the left one is
                    followed upwards.
  `fill1`, `fill`   The converse: whole paths that have the digests of a message at the positions
                    that the verification reads, and the fixed digest `default` at all others.
                    (`fill` is used in Compile/Batch/Pruned.lean, among others.)

No order is asked of js. Only neighbours in the list are joined: on a list that is not ascending
fewer nodes may be joined and more digests sent. The count (Hash/OctopusFacts.lean, Part 4) is for
strictly ascending lists.
Several trees of one depth d at once (a forest): leaf j of tree number t gets the number t * 2^d +
j. In the first d levels nodes of different trees are never siblings, and after d levels the node
number is t.
The file imports Mathlib only. There is no oracle and no probability here.

Notation: `D`: a type with a fixed element `default`, the digests; `s : List D`: the message; `upP`:
the parents with their paths (`up` on pairs of a node's number and its path).
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Data.List.Basic

namespace Octopus

/-! ## What depends on the node numbers only -/

/-- the nodes number i and j are the left and the right child of one node -/
abbrev sib (i j : ℕ) : Prop := i % 2 = 0 ∧ j = i + 1

/-- the numbers of the parents -/
def up : List ℕ → List ℕ
  | [] => []
  | [i] => [i / 2]
  | i :: j :: l => if sib i j then i / 2 :: up l else i / 2 :: up (j :: l)

/-- how many digests of the message one level takes -/
def need1 : List ℕ → ℕ
  | [] => 0
  | [_] => 1
  | i :: j :: l => if sib i j then need1 l else 1 + need1 (j :: l)

/-- the numbers after d levels -/
def upN : ℕ → List ℕ → List ℕ
  | 0, js => js
  | d + 1, js => upN d (up js)

/-- how many digests of the message d levels take -/
def need : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | d + 1, js => need1 js + need d (up js)

/-! ## The joint verification -/

section Walk
variable {M : Type → Type} [Monad M] {D : Type} [Inhabited D]

/-- the parent of node number i with the digest a, whose sibling has the digest s -/
def lone (hN : D → D → M D) (i : ℕ) (a s : D) : M D := if i % 2 = 0 then hN a s else hN s a

/-- One level up: js the numbers, v the digests of the nodes, s the message. The result: the digests
of the parents, in the order of up js. -/
def stepC (hN : D → D → M D) : List ℕ → List D → List D → M (List D)
  | [], _, _ => pure []
  | [i], v, s => do
      let u ← lone hN i (v.headD default) (s.headD default)
      pure [u]
  | i :: j :: l, v, s =>
      if sib i j then do
        let u ← hN (v.headD default) (v.tail.headD default)
        let r ← stepC hN l v.tail.tail s
        pure (u :: r)
      else do
        let u ← lone hN i (v.headD default) (s.headD default)
        let r ← stepC hN (j :: l) v.tail s.tail
        pure (u :: r)

/-- d levels up. The result: the digests of the nodes upN d js. -/
def octC (hN : D → D → M D) : ℕ → List ℕ → List D → List D → M (List D)
  | 0, _, v, _ => pure v
  | d + 1, js, v, s => do
      let v' ← stepC hN js v s
      octC hN d (up js) v' (s.drop (need1 js))

end Walk

/-! ## From whole paths to the message, and back -/

section Prune
variable {D : Type} [Inhabited D]

/-- the digests that one level takes, read off the paths: the first entry of the path of every node
that is not joined with a neighbour -/
def reads1 : List (ℕ × List D) → List D
  | [] => []
  | [x] => [x.2.headD default]
  | x :: y :: l => if sib x.1 y.1 then reads1 l else x.2.headD default :: reads1 (y :: l)

/-- the parents with their paths: a parent's path is the rest of its child's path; where two
siblings are joined, of the left child's path -/
def upP : List (ℕ × List D) → List (ℕ × List D)
  | [] => []
  | [x] => [(x.1 / 2, x.2.tail)]
  | x :: y :: l =>
    if sib x.1 y.1 then (x.1 / 2, x.2.tail) :: upP l else (x.1 / 2, x.2.tail) :: upP (y :: l)

/-- The pruned paths: the digests that d levels take, read off whole paths -/
def reads : ℕ → List (ℕ × List D) → List D
  | 0, _ => []
  | d + 1, l => reads1 l ++ reads d (upP l)

/-- paths for the nodes js of a level with d levels above it, from the message s of this level and
the paths r of the parents. A position of this level that the verification does not read holds
`default`. -/
def fill1 (d : ℕ) : List ℕ → List D → List (List D) → List (List D)
  | [], _, _ => []
  | [_], s, r => [s.headD default :: r.headD []]
  | i :: j :: l, s, r =>
      if sib i j then
        (default :: r.headD []) :: List.replicate (d + 1) default :: fill1 d l s r.tail
      else (s.headD default :: r.headD []) :: fill1 d (j :: l) s.tail r.tail

/-- Whole paths from pruned paths: one path of d digests for each node of js -/
def fill : ℕ → List ℕ → List D → List (List D)
  | 0, js, _ => js.map fun _ => []
  | d + 1, js, s => fill1 d js s (fill d (up js) (s.drop (need1 js)))

end Prune

end Octopus
