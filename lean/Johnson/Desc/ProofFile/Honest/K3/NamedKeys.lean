-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/NamedKeys.lean: TEST SCAFFOLDING. Keys and bits of a lookup on
calls, in the numbering of the joint key vector and the joint table, made of two functions that the
caller names: a call's key at a place, as an integer or none at a padding place; and a call's count
at a row of its table. Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: the joint key vector and the joint table are those of
`OnBytes.Ends.jointKey` and `OnBytes.Ends.jointTab` (OnBytes/Tie/Pv/Lookup/Ends/Joint.lean; not
imported): key number x has its tree's number in the low rK bits; row u has its call's number in the
low cK bits.

Why a file of its own. It imports the verifier program's own modules alone, so that its compiled
code can be loaded beside Lean's evaluator: `keyFn` is called once for each of 2 ^ 22 keys and more.

What is defined.
  `ofInt`: an integer as an element of the program's field; a negative one as 0 less its amount.
  `Plan`, `planOf`: what `keyFn` and `bitFn` read of a lookup's shape, made once: the numbers, the
    trees' calls and the calls' first trees, each call's padding key and each call's number as
    elements.
  `keyFn P keyAt theta i x`: key number x. With y the tree and c its call: the call's key at the
    place (y - first c) 2 ^ dT + x / 2 ^ rK, or the call's padding key where `keyAt` gives none;
    plus c times theta. In a tree beyond the calls: call 0's padding key, without theta. It does not
    read i: a proof file's lookup has one part of keys.
  `bitFn P count u j`: with c the call and t the row of its table: bit j of `count c t`, as 0 or 1;
    0 where there is no call c, and 0 at a repeated row (t from 2 ^ k on, k the call's own).

Imported. OnBytes/Tie/Pv/Lookup/Port/FoNums.lean, and through it OnBytes/Model/Look.lean.

Users. Honest/K3/WitNamed.lean; outside this library:
Honest/K3/NamedLaw.lean [not in this library], Honest/K3/WitNamedToy.lean [not in this library].

Limits. THIS FILE IS SCAFFOLDING FOR TESTS: it reads keys and bits with a default at an index that
nothing bounds: it is not for a filling at which anything is counted. In this file no theorem ties
these functions to `jointKey`, to `jointTab` or to the reader that a lot seats.
Honest/K3/NamedLaw.lean [not in this library] has, each under hypotheses on the shape and on a
program's keys and counts: `keyFn_joint`: `keyFn` is the joint key of the integers' casts, laid into
the program's elements; `bitFn_bit`: `bitFn` is the given bit; `named_same_on`: so the named
structure and a `LookIn`'s agree at the keys below 2 ^ h.v, the rows below 2 ^ h.d and the planes
below 32. It shows that the hypotheses on keys and counts are not empty (`keysAre_member`,
`bitsAre_member`) and has a test with code for those on the shape (`shapeFits_holds`); an instance
at a program's own keys and counts it does not exhibit. By its own limits this is no equality of the
two structures. That a row at two readers that so agree says and passes on the same: `site_same`
(Honest/K3/Law/Keep/ReadsNoFurtherNamed.lean [not in this library]).
Honest/K3/WitNamedToy.lean [not in this library] (a test)
tries numbers at one small shape. Nothing asks that the counts fit the keys. Where a
shorter table is repeated in the joint table the whole count is laid at the first copy: that is one
choice of rows, the one that `hitsOf` makes (Johnson/HonestTrace/Counts.lean): a key is counted at
the first row that holds it; `count` there takes any chosen rows. Where `callOf` names a call from
NC on, `padE` and `callE` give 0, while `jointKey` has c times theta there: no shape that passes
`FoNums.ok` has such a tree. Other readings of public numbers by a stand-in, without a word: a
tree's call where `callOf` is shorter than NT, and a call's first tree, count as 0; y less the first
tree is cut at 0; a call's k counts as 0; where there is no call, call 0's padding key is 0.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Tie.Pv.Lookup.Port.FoNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Named
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (ofNat)

/-- An integer as an element of the program's field. -/
def ofInt : Int → E
  | .ofNat n => ofNat n
  | .negSucc n => subE zeroE (ofNat (n + 1))

/-- What the two functions read of a lookup's shape, made once. -/
structure Plan where
  rK : Nat
  dT : Nat
  NT : Nat
  cK : Nat
  NC : Nat
  /-- a tree's call -/
  callOf : Array Nat
  /-- a call's first tree -/
  first : Array Nat
  /-- a call's table has 2 ^ k rows -/
  kN : Array Nat
  /-- a call's padding key, without the shift -/
  padE : Array E
  /-- a call's number, as an element -/
  callE : Array E

/-- The plan of a shape. -/
def planOf (h : OnBytes.Model.Forest.Shape) : Plan :=
  { rK := h.rK, dT := h.dT, NT := h.NT, cK := h.cK, NC := h.NC
    callOf := h.callOf, first := h.first
    kN := (Array.range h.NC).map (FoNums.kOf h)
    padE := (Array.range h.NC).map fun c => ofNat (FoNums.tauN h c (FoNums.t0Of h c))
    callE := (Array.range h.NC).map ofNat }

/-- **Key number x of the joint key vector.** Here keyAt gives a call's key at a place of the call's
own vector, none at a padding place. -/
def keyFn (P : Plan) (keyAt : Nat → Nat → Option Int) (theta : E) (_ : Nat) (x : Nat) : E :=
  let y := x % 2 ^ P.rK
  if y < P.NT then
    let c := P.callOf.getD y 0
    let k :=
      match keyAt c ((y - P.first.getD c 0) * 2 ^ P.dT + x / 2 ^ P.rK) with
      | some k => ofInt k
      | none => P.padE.getD c zeroE
    addE k (mulE (P.callE.getD c zeroE) theta)
  else P.padE.getD 0 zeroE

/-- **Bit j of the count of row u of the joint table.** Here count gives a call's count at a row of
the call's own table. -/
def bitFn (P : Plan) (count : Nat → Nat → Nat) (u j : Nat) : E :=
  let c := u % 2 ^ P.cK
  let t := u / 2 ^ P.cK
  if c < P.NC && t < 2 ^ P.kN.getD c 0 && (count c t).testBit j then oneE else zeroE

end ProofFile.Honest.K3.Named
